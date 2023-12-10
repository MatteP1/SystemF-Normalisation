(** * Normalisation of System F *)

(** In this file we define a logical relations model for Normalisation
	and use it to prove Normalisation. *)

From SFN Require Export SystemF.
From stdpp Require Import gmap.
From Autosubst Require Export Autosubst.
Import SystemF.


(* ################################################################# *)
(** * Normalises *)

Definition normalises (e : tm) := exists v, value v /\ e -->* v.

Example normalise_value : normalises (tm_abs (tm_var 0)).
Proof.
	exists (tm_abs (tm_var 0)). split; auto.
Qed.

Example normalise_fun : normalises (tm_app (tm_abs (tm_var 0)) tm_unit).
Proof.
	exists <{()}>. split; trivial. apply multi_step with tm_unit; trivial.
	apply (Step_nh HoleCtxt). apply Step_app. apply v_unit.
Qed.

Example stuck : ~ normalises (<{fst () }>).
Proof.
	intros H. inversion H as [v [Hv Hstep]].
	inversion Hstep.
	- subst. inversion Hv.
	- subst. inversion H0; subst. destruct K; inversion H3.
		+ cbn in H3; subst. inversion Hred.
		+ destruct K; inversion H4. cbn in H4; subst. inversion Hred.
Qed.


Definition normalises_pred (e : tm) (P : tm -> Prop) :=
	exists v, value v /\ e -->* v /\ P v.

(** normalises_pred lemmas  *)
Lemma norm_mono e P Q:
	(forall v, P v -> Q v) ->
	normalises_pred e P ->
	normalises_pred e Q.
Proof.
	intros HPQ HNeP. unfold normalises_pred in *.
	destruct HNeP as [v' [Hv'val [Hev' HPv']]].
	exists v'. auto.
Qed.

Lemma norm_val v P:
	value v ->
	P v->
	normalises_pred v P.
Proof.
	intros Hvval HPv. unfold normalises_pred in *.
	exists v. auto.
Qed.

Lemma norm_bind e P Q K: 
	normalises_pred e Q /\
	(forall v , value v /\ Q v -> normalises_pred (fill K v) P) ->
	normalises_pred (fill K e) P.
Proof.
	intros [HNeQ HQNP]. unfold normalises_pred in HNeQ.
	destruct HNeQ as (v_e & Hveval & Hev_e & HQv_e).
	specialize HQNP with v_e.
	assert (HNKveP: normalises_pred (fill K v_e) P); auto.
	destruct HNKveP as (v_f & Hvfval & HKvevf & HPvf).
	exists v_f. split. assumption. split; try assumption.
	apply step_trans with (fill K v_e).
	- apply eval_ctxt_steps. assumption.
	- assumption.
Qed.

Lemma norm_step e e' P:
	e --> e' /\ normalises_pred e' P ->
	normalises_pred e P.
Proof.
	intros (Hee' & HNe'P). destruct HNe'P as (v' & Hv'val & He'v' & HPv').
	exists v'. split. assumption. split; try assumption.
	apply step_trans with e'.
	- apply multi_step with e'; done.
	- assumption.
Qed.


(* ################################################################# *)
(** * Logical Relations Model for Normalisation *)

Definition predCtxt := list (tm -> Prop).

Definition over_vals (P : tm -> Prop) : Prop :=
	forall t, P t -> value t.

Fixpoint lr_val (xi : predCtxt) (t : ty) (v : tm) : Prop :=
	match t with
	| Ty_Var a =>
		match xi !! a with
		| Some P => P v
		| None => False
		end
	| Ty_Unit =>
		v = <{()}>
	| Ty_Prod T1 T2 =>
		exists v1 v2,
		v = <{(- v1, v2 -)}> /\
		lr_val xi T1 v1 /\
		lr_val xi T2 v2
	| Ty_Arrow T1 T2 =>
		exists e,
		v = tm_abs e /\
		(forall v', lr_val xi T1 v' -> normalises_pred e.[v'/] (lr_val xi T2))
	| Ty_Abs T =>
		exists e,
		v = tm_tyabs e /\
		(forall P, over_vals P -> normalises_pred e (lr_val (P :: xi) T))
	end.

Lemma lr_val_val (xi : predCtxt) (T : ty) (v : tm) :
	Forall over_vals xi -> lr_val xi T v -> value v.
Proof.
	revert xi v. induction T.
	- intros xi v0 Hxi Hlr. simpl in Hlr.
	  remember (xi !! v) as P.
	  destruct P; try contradiction.
	  symmetry in HeqP.
	  destruct (elem_of_list_split_length xi v P HeqP) as (xi1 & xi2 & ? & ?).
	  subst. clear HeqP.
	  apply Forall_app in Hxi. destruct Hxi as [_ Hxi].
	  inversion Hxi as [|? ? H1 H2]; subst.
	  apply H1. assumption.
	- intros xi v Hxi Hlr. simpl in Hlr. subst. constructor.
	- intros xi v Hxi Hlr. simpl in Hlr.
	  destruct Hlr as [v1 [v2 [H1 [H2 H3]]]].
	  apply IHT1 in H2; auto.
	  apply IHT2 in H3; auto.
	  subst. auto.
	- intros xi v Hxi Hlr. simpl in Hlr.
	  destruct Hlr as [e [H1 H2]].
	  subst. auto.
	- intros xi v Hxi Hlr. simpl in Hlr.
	  destruct Hlr as [e [H1 H2]].
	  subst. auto.
Qed.

Fixpoint log_rel_seq (xi : predCtxt) (Gamma : varContext) (vs : list tm) : Prop :=
	match Gamma with
	| [] => vs = []
	| t :: ts' =>
		exists v vs', vs = v :: vs' /\ lr_val xi t v /\ log_rel_seq xi ts' vs'
	end.

Fixpoint env_subst (vs : list tm) : var → tm :=
	match vs with
	| [] => ids
	| v :: vs' => v .: env_subst vs'
	end.

Definition log_rel Gamma e T :=
	forall xi vs,
	Forall over_vals xi ->
	log_rel_seq xi Gamma vs ->
	normalises_pred e.[env_subst vs] (lr_val xi T).

Notation "Gamma '|=' e ':' T" := (log_rel Gamma e T)
	(at level 101,
		e custom sysf, T custom sysf at level 0).

(* ================================================================= *)
(** ** Helper Lemmas *)

(**	The following Section was taken from:
	https://gitlab.mpi-sws.org/iris/examples/-/blob/master/theories/logrel/F_mu_ref_conc/base.v *)
Section Autosubst_Lemmas.
Context {term : Type} {Ids_term : Ids term}
        {Rename_term : Rename term} {Subst_term : Subst term}
        {SubstLemmas_term : SubstLemmas term}.

Lemma iter_up (m x : nat) (f : var → term) :
	upn m f x = if lt_dec x m then ids x else rename (+m) (f (x - m)).
Proof using Type*.
	revert x; induction m; intros [ | x ]; asimpl; auto;
		repeat (destruct (lt_dec _ _) || asimpl || rewrite IHm); auto with lia.
  Qed.
End Autosubst_Lemmas.

Lemma log_rel_weaken_gen xi xi1 xi2 v T :
	Forall over_vals xi ->
	Forall over_vals xi1 ->
	Forall over_vals xi2 ->
	lr_val (xi1 ++ xi2) T v <->
	lr_val (xi1 ++ xi ++ xi2) T.[upn (length xi1) (ren (+ length xi))] v.
Proof.
	revert xi xi1 xi2 v. induction T; intros xi xi1 xi2; cbn.
	- intros v0 Hxi Hxi1 Hxi2. split.
		+ rewrite iter_up; destruct (lt_dec v (length xi1)); simpl.
			* rewrite (lookup_app_l _ xi2); auto.
			  rewrite (lookup_app_l _ (xi ++ xi2)); auto.
			* rewrite (lookup_app_r xi1); try lia; auto.
			  intro. rewrite app_assoc.
			  rewrite (lookup_app_r (xi1 ++ xi)); try rewrite app_length; try lia; auto.
			  assert (l: length xi1 + (length xi + (v - length xi1)) - (length xi1 + length xi) = v - length xi1) by lia.
			  by rewrite l.
		+ rewrite iter_up; destruct (lt_dec v (length xi1)); simpl.
			* rewrite (lookup_app_l _ (xi ++ xi2)); auto; rewrite (lookup_app_l _ xi2); auto.
			* rewrite app_assoc. rewrite (lookup_app_r (xi1 ++ xi)); try rewrite app_length; try lia; auto.
			  assert (l: length xi1 + (length xi + (v - length xi1)) - (length xi1 + length xi) = v - length xi1) by lia.
			  rewrite l.
			  rewrite (lookup_app_r xi1); try lia; auto.
	- reflexivity.
	- intros v0 Hxi Hxi1 Hxi2. split; intro H.
		+ destruct H as [v1 [v2 [H1 [H2 H3]]]].
			exists v1, v2. 
		 	split; auto.
			split; try apply IHT1; try apply IHT2; assumption.
		+ destruct H as [v1 [v2 [H1 [H2 H3]]]].
			exists v1, v2. split; auto.
			split; try rewrite (IHT1 xi); try rewrite (IHT2 xi); assumption.
	- intros v0 Hxi Hxi1 Hxi2. split; intro H.
		+ destruct H as [e [H1 H2]].
			exists e. split; auto.
			intros v' Hv'.
			apply IHT1 in Hv'; auto.
			apply H2 in Hv'.
			destruct Hv' as [v'' [Hv'' [Hv''' Hv'''']]].
			exists v''.
			split; auto; split; auto.
			apply IHT2; assumption.
		+ destruct H as [e [H1 H2]].
			exists e. split; auto.
			intros v' Hv'.
			assert (Hv'': lr_val (xi1 ++ xi ++ xi2) T1.[upn (length xi1) (ren (+length xi))] v').
			apply IHT1; auto.
			apply H2 in Hv''.
			destruct Hv'' as [v'' [Hv'' [Hv''' Hv'''']]].
			exists v''.
			split; auto; split; auto.
			rewrite (IHT2 xi); assumption.
	- intros v0 Hxi Hxi1 Hxi2. split; intro H.
		+ destruct H as [e [H1 H2]].
			exists e. split; auto.
			intros P HP.
			destruct (H2 P) as (v' & Hv' & Hv'' & Hv'''); auto.
			exists v'.
			split; auto; split; auto.
			apply (IHT xi (P :: xi1)); auto.
		+ destruct H as [e [H1 H2]].
			exists e. split; auto.
		 	intros P HP.
			destruct (H2 P) as (v' & Hv' & Hv'' & Hv'''); auto.
			exists v'.
			split; auto; split; auto.
			apply (IHT xi (P :: xi1)); auto.
Qed.

Lemma log_rel_weaken xi P v T :
	Forall over_vals xi ->
	over_vals P ->
	lr_val xi T v <-> lr_val (P :: xi) T.[ren (+1)] v.
Proof.
	intros Hxi HP.
	apply log_rel_weaken_gen with (xi1 := []) (xi := [P]) (xi2 := xi); auto.
Qed.

Lemma log_rel_seq_weaken xi P Gamma vs :
	Forall over_vals xi ->
	over_vals P ->
	log_rel_seq xi Gamma vs <-> log_rel_seq (P :: xi) (subst (ren (+1)) <$> Gamma) vs.
Proof.
	revert xi vs. induction Gamma; intros xi vs Hxi Hp; cbn.
	- reflexivity.
	- split; intros H.
		+ destruct H as [v [vs' [H1 [H2 H3]]]].
			exists v, vs'. repeat (split; auto).
			eapply log_rel_weaken in H2; eauto.
			by apply IHGamma.
		+ destruct H as [v [vs' [H1 [H2 H3]]]].
			exists v, vs'. repeat (split; auto).
			eapply log_rel_weaken; eauto.
			by apply IHGamma.
Qed.

Lemma log_rel_subst_gen xi' xi T T' v :
	Forall over_vals xi ->
	Forall over_vals xi' ->
	lr_val (xi' ++ xi) T.[upn (length xi') (T' .: ids)] v <-> lr_val (xi' ++ (lr_val xi T') :: xi) T v.
Proof.
	revert xi' xi v. induction T; intros xi' xi v''' Hxi_val Hxi_val'; cbn.
	- rewrite iter_up; destruct lt_dec; simpl.
	    + rewrite (lookup_app_l xi' xi); auto. rewrite (lookup_app_l _ (lr_val xi T' :: xi)); auto.
		+ rewrite (lookup_app_r xi'); try lia.
		  destruct (v - length xi'); subst; simpl.
		  	* rewrite (log_rel_weaken_gen xi' [] xi); asimpl. all: auto.
			* rewrite (lookup_app_r xi' xi); try rewrite app_length; try lia.
			  assert (l: length xi' + n0 - length xi' = n0) by lia.
			  by rewrite l.
	- reflexivity.
	- split; intros H.
		+ destruct H as [v1 [v2 [H1 [H2 H3]]]].
			exists v1, v2. 
		 	split; auto.
			symmetry in IHT1. apply IHT1 in H2.
			symmetry in IHT2. apply IHT2 in H3.
			all: auto.
		+ destruct H as [v1 [v2 [H1 [H2 H3]]]].
			exists v1, v2. split; auto; split.
			* apply IHT1; auto.
			* apply IHT2; auto.
	- split; intros H.
		+ destruct H as [e [H1 H2]].
			exists e. split; auto.
			intros v' Hv'.
			apply IHT1 in Hv'; auto.
			apply H2 in Hv'.
			unfold normalises_pred in Hv'.
			destruct Hv' as [v'' [Hv'' [Hv''' Hv'''']]].
			unfold normalises_pred.
			exists v''.
			split; auto; split; auto.
			apply IHT2; auto.
		+ destruct H as [e [H1 H2]].
			exists e. split; auto.
			intros v' Hv'. rewrite IHT1 in Hv'; auto.
			apply H2 in Hv'.
			unfold normalises_pred in Hv'.
			destruct Hv' as [v'' [Hv'' [Hv''' Hv'''']]].
			unfold normalises_pred.
			exists v''.
			split; auto; split; auto.
			symmetry in IHT2. apply IHT2; assumption.
	- split; intros H.
		+ destruct H as [e [H1 H2]].
			exists e. split; auto.
			intros P.
			specialize (H2 P).
			unfold normalises_pred in H2.
			intros Hp_val.
			destruct H2 as [v' [Hv' [Hv'' Hv''']]]; auto.
			unfold normalises_pred.
			exists v'.
			split; auto; split; auto.
			apply (IHT (P :: xi')). 
			* assumption.
			* apply Forall_cons. auto.
			* auto.
		+ destruct H as [e [H1 H2]].
			exists e. split; auto.
			intros P.
			specialize (H2 P).
			unfold normalises_pred in H2.
			intros Hp_val.
			destruct H2 as [v' [Hv' [Hv'' Hv''']]]; auto.
			unfold normalises_pred.
			exists v'.
			split; auto; split; auto.
			symmetry in IHT. apply (IHT (P :: xi')).
			* assumption.
			* apply Forall_cons. auto.
			* auto.
Qed.

Lemma log_rel_subst xi T T' v :
	Forall over_vals xi ->
	lr_val xi T.[T'/] v <-> lr_val ((lr_val xi T') :: xi) T v.
Proof.
	intro Hxi_val. apply log_rel_subst_gen with (xi' := []) (xi := xi); auto.
Qed.


(* ################################################################# *)
(** * Fundamental Theorem and Soundness *)

Lemma subst_step_var Gamma x T vs xi:
	Forall over_vals xi ->
	Gamma !! x = Some T ->
	log_rel_seq xi Gamma vs ->
	normalises_pred (env_subst vs x) (lr_val xi T).
Proof.
	revert x vs T xi.
	induction Gamma as [ | a Gamma IHG].
	- done.
	- intros x vs T xi Hxi Hx Hlrs.
	  destruct x.
	  * simpl in *. destruct Hlrs as (v & vs' & Hlr & ? & ?).
	  	simplify_eq. simpl. exists v. split; auto.
		eapply lr_val_val; eauto.
	  * simpl in *. destruct Hlrs as (v & vs' & Hlr & ? & ?).
	    simplify_eq. cbn. apply IHG; assumption.
Qed.

Theorem fundamental_theorem : forall Gamma e T,
	Gamma |- e : T ->
	Gamma |= e : T.
Proof with auto.
	unfold log_rel.
	intros Gamma e T HGeT xi vs Hxi_val. revert vs xi Hxi_val.
	induction HGeT as [ Gamma x T HxGamma | Gamma 
					  | Gamma T1 T2 e1 e2 HGe1T1 IH1 HGe2T2 IH2 
					  | Gamma T1 T2 e HGeT1T2 IH 
					  | Gamma T1 T2 e HGeT1T2 IH
					  | Gamma T1 T2 e HGeT2 IH
					  | Gamma T1 T2 e1 e2 HGe1T1T2 IH1 HGe2T2 IH2
					  | Gamma T e HGeT IH
					  | Gamma T T' e HGeAT IH].
	all: intros vs xi Hxi_val Hlrs_xi_G_vs;
	asimpl. (* The asimpl performs the substitution in the goals. *)
	- apply subst_step_var with Gamma; assumption.
	- exists tm_unit; done.
	- rewrite eval_ctxt_pair_left. apply norm_bind with (lr_val xi T1).
		split. apply IH1...
		intros v1 (Hv1val & Hlrv_v1). cbn.
		rewrite eval_ctxt_pair_right with _ _ Hv1val...
		apply norm_bind with (lr_val xi T2).
		split. apply IH2...
		intros v2 (Hv2val & Hlrv_v2).
		apply norm_val; cbn; auto.
		exists v1, v2...
	- rewrite eval_ctxt_fst. apply norm_bind with (lr_val xi (Ty_Prod T1 T2)).
		split. apply IH...
		intros v (Hvval & Hlrv_v).
		destruct Hlrv_v as (v1 & v2 & Heq & Hlrv_v1 & Hlrv_v2).
		subst. inversion Hvval; subst. apply norm_step with v1. split; cbn.
		+ rewrite (eval_ctxt_hole <{fst (- v1, v2 -)}>). 
			rewrite (eval_ctxt_hole v1). auto.
		+ apply norm_val...
	- rewrite eval_ctxt_snd. apply norm_bind with (lr_val xi (Ty_Prod T1 T2)).
		split. apply IH...
		intros v (Hvval & Hlrv_v).
		destruct Hlrv_v as (v1 & v2 & Heq & Hlrv_v1 & Hlrv_v2).
		subst. inversion Hvval; subst. apply norm_step with v2. split; cbn.
		+ rewrite (eval_ctxt_hole <{snd (- v1, v2 -)}>). 
			rewrite (eval_ctxt_hole v2). auto.
		+ apply norm_val...
	- apply norm_val... exists (e.[up (env_subst vs)]); split...
		intros v' Hlrv_v'. asimpl. 
		assert (Hes: v' .: env_subst vs = env_subst (v' :: vs))... 
		rewrite Hes. apply IH... cbn. exists v', vs...
	- rewrite eval_ctxt_app_left. 
		apply norm_bind with (lr_val xi (Ty_Arrow T1 T2)).
		split. apply IH1...
		intros v1 (Hv1val & Hlrv_v1). destruct Hlrv_v1 as (e & Heq & H); subst.
		cbn. rewrite eval_ctxt_app_right with _ _ Hv1val...
		apply norm_bind with (lr_val xi T1). split. apply IH2...
		intros v2 (Hv2val & Hlrv_v2). apply norm_step with e.[v2/]. split.
		+ cbn. rewrite (eval_ctxt_hole (tm_app (tm_abs e) v2)). 
			rewrite eval_ctxt_hole. auto.
		+ apply (H v2 Hlrv_v2).
	- apply norm_val... exists (e.[env_subst vs]). split...
		intros P HovP. apply IH... apply log_rel_seq_weaken...
	- rewrite eval_ctxt_tapp. apply norm_bind with (lr_val xi (Ty_Abs T)).
		split. apply IH...
		intros v (Hvval & Hlrv_v). destruct Hlrv_v as (e' & Heq & H); subst.
		apply norm_step with e'. split.
		+ cbn. rewrite (eval_ctxt_hole <{(/\ e') _}>). 
			rewrite (eval_ctxt_hole e'). auto.
		+ apply norm_mono with (lr_val ( (lr_val xi T' ) :: xi) T).
			* intros v. apply log_rel_subst...
			* apply (H (lr_val xi T')). intros v Hlrv_v. 
				apply (lr_val_val xi T')...
Qed.

Theorem normalisation: forall e T,
	[] |- e : T ->
	normalises e.
Proof.
	intros e T HT.
	apply fundamental_theorem in HT. unfold log_rel in HT.
	specialize HT with [] []. asimpl in HT. destruct HT as (v & Hvval & Hev & Hlrv_v).
	1,2: done. exists v. split; done.
Qed.

Theorem normalisation_alt: forall e T,
	[] |- e : T ->
	exists e', e -->* e' /\ ~(exists e'', e' --> e'').
Proof.
	intros e T HEeT. apply normalisation in HEeT as (v & Hv & Hev).
	exists v. split.
	- assumption.
	- intros [e'' Hcontra]. apply value_not_step with v.
		+ assumption.
		+ exists e''. assumption.
Qed.
