(** * System F *)

(* NOTE: THE FOLLOWING DEVELOPMENT IS AN EXTENSION OF stlc.v FROM PROGRAMMING LANGUAGE FOUNDATIONS. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
Require Import List.
Import ListNotations.
From stdpp Require Import gmap.
From Autosubst Require Export Autosubst.

(* Relation *)
Definition relation (X : Type) := X -> X -> Prop.

(* Multi step Relation *)
Inductive multi {X : Type} (R : relation X) : relation X :=
	| multi_refl : forall (x : X), multi R x x
	| multi_step : forall (x y z : X),
	R x y ->
						multi R y z ->
						multi R x z.

Hint Constructors multi : core.

Module SystemF.

(* ================================================================= *)
(** ** Types *)

Inductive ty : Type :=
	| Ty_Var   : var -> ty
	| Ty_Unit  : ty
	| Ty_Prod  : ty -> ty -> ty
	| Ty_Arrow : ty -> ty -> ty
	| Ty_Abs   : {bind ty} -> ty.

Global Instance Ids_type : Ids ty. derive. Defined.
Global Instance Rename_type : Rename ty. derive. Defined.
Global Instance Subst_type : Subst ty. derive. Defined.
Global Instance SubstLemmas_type : SubstLemmas ty. derive. Qed.


(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
	| tm_var   : var -> tm
	| tm_unit  : tm
	| tm_pair  : tm -> tm -> tm
	| tm_fst   : tm -> tm
	| tm_snd   : tm -> tm
	| tm_abs   : {bind tm} -> tm
	| tm_app   : tm -> tm -> tm
	| tm_tyabs : tm -> tm
	| tm_tyapp : tm -> tm.


Global Instance Ids_expr : Ids tm. derive. Defined.
Global Instance Rename_expr : Rename tm. derive. Defined.
Global Instance Subst_expr : Subst tm. derive. Defined.
Global Instance SubstLemmas_expr : SubstLemmas tm. derive. Qed.

Declare Custom Entry sysf.
Notation "<{ e }>" := e (e custom sysf at level 99).
Notation "( x )" := x (in custom sysf, x at level 99).
Notation "x" := x (in custom sysf at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom sysf at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom sysf at level 1, left associativity).
(* Notation "\ x , y" :=
	(tm_abs x y) (in custom sysf at level 90, x at level 99,
						y custom sysf at level 99,
						left associativity). *)

Coercion tm_var : var >-> tm.

Notation "'\All' a '..' T" := (Ty_Abs a T) (in custom sysf at level 50, right associativity).
Notation "x '_'" := (tm_tyapp x) (in custom sysf at level 1, left associativity).
Notation "'/\' x" :=
	(tm_tyabs x) (in custom sysf at level 90, x at level 99,
						left associativity).

Notation "'Unit'" := Ty_Unit (in custom sysf at level 0).
Notation "'()'" := (tm_unit) (in custom sysf at level 0).

Notation "'(~' S '*' T '~)'" := (Ty_Prod S T) (in custom sysf at level 50, right associativity).
Notation "'(-' x ',' y '-)'" :=
	(tm_pair x y) (in custom sysf at level 89,
					x custom sysf at level 99,
					y custom sysf at level 99,
					left associativity).
Notation "'fst' x" :=
	(tm_fst x) (in custom sysf at level 89,
					x custom sysf at level 99,
					left associativity).
Notation "'snd' x" :=
	(tm_snd x) (in custom sysf at level 89,
					x custom sysf at level 99,
					left associativity).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.


(* ################################################################# *)
(** * Operational Semantics *)

(* ================================================================= *)
(** ** Values *)

Inductive value : tm -> Prop :=
	| v_unit :
		value <{()}>
	| v_pair :
		forall v1 v2,
		value v1 ->
		value v2 ->
		value <{(-v1, v2-)}>
	| v_abs : forall (e : tm),
		value (tm_abs e)
	| v_tyabs : forall e,
		value <{/\ e}>.

Hint Constructors value : core.

(* ================================================================= *)
(** ** Evaluation Contexts *)

Inductive eval_ctxt :=
| HoleCtxt	: eval_ctxt
| FstCtxt (K : eval_ctxt) : eval_ctxt
| SndCtxt (K : eval_ctxt) : eval_ctxt
| PairLCtxt (K : eval_ctxt) (e: tm) : eval_ctxt
| PairRCtxt (K : eval_ctxt) (v: tm) (Hv: value v) : eval_ctxt
| AppLCtxt (K : eval_ctxt) (e: tm) : eval_ctxt
| AppRCtxt (K : eval_ctxt) (v: tm) (Hv: value v) : eval_ctxt
| TAppCtxt (K : eval_ctxt) : eval_ctxt.

Hint Constructors eval_ctxt : core.

Fixpoint fill (K : eval_ctxt) (e : tm) : tm :=
	match K with
	| HoleCtxt => e
	| FstCtxt K' => tm_fst (fill K' e)
	| SndCtxt K' => tm_snd (fill K' e)
	| PairLCtxt K' e2 => tm_pair (fill K' e ) e2
	| PairRCtxt K' v Hv => tm_pair v (fill K' e)
	| AppLCtxt K' e' => tm_app (fill K' e) e'
	| AppRCtxt K' v Hv => tm_app v (fill K' e)
	| TAppCtxt K' => tm_tyapp (fill K' e)
	end.

Fixpoint compose (K K' : eval_ctxt) : eval_ctxt :=
	match K with
	| HoleCtxt => K'
	| FstCtxt K'' => FstCtxt (compose K'' K')
	| SndCtxt K'' => SndCtxt (compose K'' K')
	| PairLCtxt K'' e2 => PairLCtxt (compose K'' K') e2
	| PairRCtxt K'' v Hv => PairRCtxt (compose K'' K') v Hv
	| AppLCtxt K'' e' => AppLCtxt (compose K'' K') e'
	| AppRCtxt K'' v Hv => AppRCtxt (compose K'' K') v Hv
	| TAppCtxt K'' => TAppCtxt (compose K'' K')
	end.

(* ================================================================= *)
(** ** Reduction *)

Inductive head_reduction : tm -> tm -> Prop :=
| Step_fst v1 v2 (Hv1: value v1) (Hv2: value v2) : 
	head_reduction (tm_fst (tm_pair v1 v2)) v1
| Step_snd v1 v2 (Hv1: value v1) (Hv2: value v2) : 
	head_reduction (tm_snd (tm_pair v1 v2)) v2
| Step_app e v (Hv: value v) :
	head_reduction (tm_app (tm_abs e) v) (e.[v/])
| Step_tapp e :
	head_reduction (tm_tyapp (tm_tyabs e)) e.

Reserved Notation "e '-->' e'" (in custom sysf at level 40).

Hint Constructors head_reduction : core.

Inductive step : tm -> tm -> Prop :=
| Step_nh K e1 e2 (Hred: head_reduction e1 e2) :
	(fill K e1) --> (fill K e2)

where "e '-->' e'" := (step e e').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "e1 '-->*' e2" := (multistep e1 e2) (at level 40).

Lemma step_trans : forall e1 e2 e3,
	e1 -->* e2 ->
	e2 -->* e3 ->
	e1 -->* e3.
Proof.
	intros e1 e2 e3 He1e2. 
	induction He1e2 as [e | e e' e'' Hee' He'e'' IH].
	- trivial.
	- intros He''e3. apply IH in He''e3 as He'e3. 
		apply multi_step with e'; assumption.
Qed.

Lemma fill_compose: forall e K K',
	fill K (fill K' e) = fill (compose K K') e.
Proof.
	intros e K. revert e. induction K; intros; cbn; try rewrite IHK; auto.
Qed.

Lemma eval_ctxt_step: forall e e' K,
	e --> e' ->
	fill K e --> fill K e'.
Proof.
	intros e e' K Hee'.
	inversion Hee' as [K' e1 e2 Hred HK'e1 HK'e2].
	do 2 (rewrite fill_compose). apply Step_nh. assumption.
Qed.

Lemma eval_ctxt_steps: forall e e' K,
	e -->* e' ->
	fill K e -->* fill K e'.
Proof.
	intros e e' K Hee'. induction Hee'.
	- apply multi_refl.
	- apply multi_step with (fill K y0).
		+ apply eval_ctxt_step. assumption.
		+ assumption.
Qed.

Lemma eval_ctxt_hole: forall e,
	<{ e }> = fill HoleCtxt <{ e }>.
Proof. auto. Qed.

Lemma eval_ctxt_fst: forall e,
	<{ fst e }> = fill (FstCtxt HoleCtxt) e.
Proof. auto. Qed.

Lemma eval_ctxt_snd: forall e,
	<{ snd e }> = fill (SndCtxt HoleCtxt) e.
Proof. auto. Qed.

Lemma eval_ctxt_pair_left: forall e1 e2, 
	<{ (- e1, e2 -) }> = fill (PairLCtxt HoleCtxt e2) e1.
Proof. auto. Qed.

Lemma eval_ctxt_pair_right: forall v1 e2 H,
	<{(- v1, e2 -)}> = fill (PairRCtxt HoleCtxt v1 H) e2.
Proof. auto. Qed.

Lemma eval_ctxt_app_left: forall e1 e2,
	tm_app e1 e2 = fill (AppLCtxt HoleCtxt e2) e1.
Proof. auto. Qed.
	
Lemma eval_ctxt_app_right: forall v1 e2 H,
	tm_app v1 e2 = fill (AppRCtxt HoleCtxt v1 H) e2.
Proof. auto. Qed.

Lemma eval_ctxt_tapp: forall e,
	tm_tyapp e = fill (TAppCtxt HoleCtxt) e.
Proof. auto. Qed.

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
(** * Typing *)

(* ================================================================= *)
(** ** Contexts *)

Definition varContext := list ty.
(* Definition typeCtxt := list ty. *)

(* Definition free_varctxt (a : string) (Gamma : varContext) : Prop :=
	exists x T,
		Gamma x = Some T /\
		free a T. *)

(* ================================================================= *)

Reserved Notation "Gamma '|-' e ':' T"
			(at level 101,
				e custom sysf, T custom sysf at level 0).

Inductive has_type : varContext -> tm -> ty -> Prop :=
	| T_Var : forall (Gamma: varContext) x T1,
		Gamma !! x = Some T1 ->
		has_type Gamma (tm_var x) T1
	| T_Unit : forall Gamma,
		Gamma |- () : Unit
	| T_Prod : forall Gamma T1 T2 e1 e2,
		Gamma |- e1 : T1 ->
		Gamma |- e2 : T2 ->
		Gamma |- (- e1, e2 -) : (~ T1 * T2 ~)
	| T_Fst : forall Gamma T1 T2 e,
		Gamma |- e : ((~ T1 * T2 ~)) ->
		Gamma |- fst e : T1
	| T_Snd : forall Gamma T1 T2 e,
		Gamma |- e : ((~ T1 * T2 ~)) ->
		Gamma |- snd e : T2
	| T_Abs : forall Gamma T1 T2 e,
		(T1 :: Gamma) |- e : T2 ->
		has_type Gamma (tm_abs e) (Ty_Arrow T1 T2)
	| T_App : forall Gamma T1 T2 e1 e2,
		Gamma |- e1 : (T1 -> T2) ->
		Gamma |- e2 : T1 ->
		Gamma |- e1 e2 : T2
	| T_TLam : forall Gamma T e,
		has_type (subst (ren (+1)) <$> Gamma) e T ->
		has_type Gamma (tm_tyabs e) (Ty_Abs T)
	| T_TApp : forall Gamma T T' e,
		has_type Gamma e (Ty_Abs T) ->
		has_type Gamma (tm_tyapp e) T.[T'/]

where "Gamma '|-' e ':' T" := (has_type Gamma e T).

Hint Constructors has_type : core.

(* ================================================================= *)
(** ** Examples *)

Lemma ty_not_eq : forall T1 T2, ~ Ty_Arrow T2 T1 = T2.
Proof.
	induction T2; intros H.
	- inversion H.
	- inversion H.
	- inversion H.
	- inversion H; subst. apply IHT2_1. assumption.
	- inversion H.
Qed.

Example typing_nonexample_3 :
	~ (exists T,
		has_type [] (tm_abs (tm_app (tm_var 0) (tm_var 0))) T).
Proof.
	intros [T H]. inversion H; subst. inversion H2; subst.
	inversion H4; subst. inversion H3; subst.
	inversion H6; subst. inversion H5. apply (ty_not_eq T2 T0). assumption.
Qed.
(** [] *)


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
	- intros xi v Hxi Hlr. simpl in Hlr. subst. auto.
	- intros xi v Hxi Hlr. simpl in Hlr.
	  destruct Hlr as [v1 [v2 [H1 [H2 H3]]]].
	  apply IHT1 in H2; auto.
	  apply IHT2 in H3; auto.
	  subst; eauto.
	- intros xi v Hxi Hlr. simpl in Hlr.
	  destruct Hlr as [e [H1 H2]].
	  subst. eauto.
	- intros xi v Hxi Hlr. simpl in Hlr.
	  destruct Hlr as [e [H1 H2]].
	  subst. eauto.
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

(* ================================================================= *)
(** ** Helper Lemmas *)

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
	revert xi xi1 xi2 v. induction T; simpl; auto; intros xi xi1 xi2; simpl.
	- intros v0 Hxi Hxi1 Hxi2. split.
		+ rewrite iter_up; destruct (lt_dec v (length xi1)); simpl.
			* rewrite (lookup_app_l _ xi2); auto;
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
	revert xi vs. induction Gamma; simpl; auto; intros xi vs Hxi Hp; simpl.
	split; intros.
	- destruct H as [v [vs' [H1 [H2 H3]]]].
		exists v, vs'. repeat (split; auto).
		eapply log_rel_weaken in H2; eauto.
		by apply IHGamma.
	- destruct H as [v [vs' [H1 [H2 H3]]]].
		exists v, vs'. repeat (split; auto).
		eapply log_rel_weaken; eauto.
		by apply IHGamma.
Qed.

Lemma log_rel_subst_gen xi' xi T T' v :
	Forall over_vals xi ->
	Forall over_vals xi' ->
	lr_val (xi' ++ xi) T.[upn (length xi') (T' .: ids)] v <-> lr_val (xi' ++ (lr_val xi T') :: xi) T v.
Proof.
	revert xi' xi v. induction T; simpl; auto; intros xi' xi v''' Hxi_val Hxi_val'; simpl.
	- rewrite iter_up; destruct lt_dec; simpl.
	    + rewrite (lookup_app_l xi' xi); auto; rewrite (lookup_app_l _ (lr_val xi T' :: xi)); auto.
		+ rewrite (lookup_app_r xi'); try lia; auto.
		  destruct (v - length xi'); subst; simpl.
		  	* rewrite (log_rel_weaken_gen xi' [] xi). simpl. asimpl. reflexivity. assumption. trivial. assumption.
			* rewrite (lookup_app_r xi' xi); try rewrite app_length; try lia.
			  assert (l: length xi' + n0 - length xi' = n0) by lia.
			  by rewrite l.
	- split; intros H.
		+ destruct H as [v1 [v2 [H1 [H2 H3]]]].
			exists v1, v2. 
		 	split; auto.
			symmetry in IHT1. apply IHT1 in H2.
			symmetry in IHT2. apply IHT2 in H3.
			all: auto.
		+ destruct H as [v1 [v2 [H1 [H2 H3]]]].
			exists v1, v2. split; auto; split.
			apply IHT1; auto.
			apply IHT2; auto.
	- split; intros H.
		+ destruct H as [e [H1 H2]].
			exists e. split; auto.
			intros v' Hv'.
			apply IHT1 in Hv'.
			apply H2 in Hv'.
			unfold normalises_pred in Hv'.
			destruct Hv' as [v'' [Hv'' [Hv''' Hv'''']]].
			unfold normalises_pred.
			exists v''.
			split; auto; split; auto.
			apply IHT2; auto. all: auto.
		+ destruct H as [e [H1 H2]].
			exists e. split; auto.
			intros v' Hv'. rewrite IHT1 in Hv'.
			apply H2 in Hv'.
			unfold normalises_pred in Hv'.
			destruct Hv' as [v'' [Hv'' [Hv''' Hv'''']]].
			unfold normalises_pred.
			exists v''.
			split; auto; split; auto.
			symmetry in IHT2. apply IHT2; assumption. all: auto.
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
	log_rel Gamma e T.
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
	asimpl. (* The asimpl performs the substitution in the goals*)
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

End SystemF.
