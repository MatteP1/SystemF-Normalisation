(** * System F *)

(* NOTE: THE FOLLOWING DEVELOPMENT IS AN EXTENSION OF stlc.v FROM PROGRAMMING LANGUAGE FOUNDATIONS. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SFN Require Import Maps.
Require Import List.
Import ListNotations.
From stdpp Require Import gmap.
From Autosubst Require Export Autosubst.

Hint Resolve update_eq : core.

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

Print Subst_expr.

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

Fixpoint fill (K : eval_ctxt) (e : tm) : tm :=
	match K with
	| HoleCtxt => e
	| FstCtxt K' => tm_fst (fill K' e)
	| SndCtxt K' => tm_snd (fill K' e)
	| PairLCtxt K' e2 => tm_pair (fill K' e ) e2
	| PairRCtxt K' v Hv => tm_pair v (fill K' e)
	| AppLCtxt K' e' => tm_app (fill K' e) e'
	| AppRCtxt K' v Hv => tm_app v (fill K' e)
	| TAppCtxt K' => tm_tyabs (fill K' e)
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
Admitted.

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
	| T_Unit : forall Gamma,
		Gamma |- () : Unit
	| T_Var : forall (Gamma: varContext) x T1,
		Gamma !! x = Some T1 ->
		has_type Gamma (tm_var x) T1
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
	| T_App : forall T1 T2 Gamma e1 e2,
		Gamma |- e1 : (T2 -> T1) ->
		Gamma |- e2 : T2 ->
		Gamma |- e1 e2 : T1
	| T_TLam : forall Gamma T e,
		has_type (subst (ren (+1)) <$> Gamma) e T ->
		has_type Gamma (tm_tyabs e) (Ty_Abs T)
	| T_TApp : forall T T' Gamma e,
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
	inversion H6; subst. inversion H5. apply (ty_not_eq T2 T3). assumption.
Qed.
(** [] *)


(* ################################################################# *)
(** * Logical Relations Model for Normalisation *)

Definition predCtxt := list (tm -> Prop).

(* TODO: DEFINE LR *)

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

Lemma norm_mono e P Q:
	(forall v, P v -> Q v) ->
	normalises_pred e P ->
	normalises_pred e Q.
Proof.
	intros H1 H2. unfold normalises_pred in *.
	destruct H2 as [v [? [? ?]]].
	exists v. repeat (split; auto).
Qed.

Lemma norm_val v P:
	value v ->
	P v->
	normalises_pred v P.
Proof.
	intros H1 H2. unfold normalises_pred in *.
	exists v. repeat (split; auto).
Qed.

(* ################################################################# *)
(** * Fundamental Theorem and Soundness *)

Fixpoint env_subst (vs : list tm) : var → tm :=
  match vs with
  | [] => ids
  | v :: vs' => v .: env_subst vs'
  end.

Lemma subst_step_var Gamma x T vs xi:
	Forall over_vals xi ->
	Gamma !! x = Some T ->
	log_rel_seq xi Gamma vs ->
	normalises_pred (env_subst vs x) (lr_val xi T).
Proof.
	revert x vs T xi.
	induction Gamma.
	- done.
	- intros x vs T xi Hxi Hx Hlrs.
	  destruct x.
	  * simpl in *. destruct Hlrs as (v & vs' & Hlr & ? & ?).
	  	simplify_eq. simpl. exists v. split; auto.
		eapply lr_val_val; eauto.
	  * simpl in *. destruct Hlrs as (v & vs' & Hlr & ? & ?).
	    simplify_eq.
Admitted.

Lemma subst_step_pair e1 v1 e2 v2 vs:
	e1.[env_subst vs] -->* v1 ->
	value v1 ->
	e2.[env_subst vs] -->* v2 ->
	value v2 ->
	tm_pair e1.[env_subst vs] e2.[env_subst vs] -->* <{(- v1, v2 -)}>.
Proof.
Admitted.

Lemma subst_step_fst e v1 v2 vs:
	e.[env_subst vs] -->* <{(- v1, v2 -)}> ->
	value v1 ->
	value v2 ->
	tm_fst e.[env_subst vs] -->* v1.
Proof.
Admitted.

Lemma subst_step_snd e v1 v2 vs:
	e.[env_subst vs] -->* <{(- v1, v2 -)}> ->
	value v1 ->
	value v2 ->
	tm_snd e.[env_subst vs] -->* v2.
Proof.
Admitted.

Lemma subst_step_app e1 e e2 v vs v':
	e1.[env_subst vs] -->* tm_abs e ->
	e2.[env_subst vs] -->* v ->
	value v ->
	e.[v/] -->* v' ->
	value v' ->
	tm_app e1.[env_subst vs] e2.[env_subst vs] -->* v'.
Proof.
Admitted.

Lemma subst_step_tapp e b v0 vs:
	e.[env_subst vs] -->* tm_tyabs b ->
	b -->* v0 ->
	value v0 ->
	tm_tyapp e.[env_subst vs] -->* v0.
Proof.
Admitted.

Theorem fundamental_theorem : forall Gamma e vs T xi,
	Forall over_vals xi ->
	Gamma |- e : T ->
	log_rel_seq xi Gamma vs ->
	normalises_pred e.[env_subst vs] (lr_val xi T).
Proof.
	intros Gamma e vs T xi Hxi_val H. revert vs xi Hxi_val.
	induction H; intros vs xi Hlog; simpl.
	- unfold normalises_pred. exists <{()}>. split; auto.
	- eapply subst_step_var; eauto.
	- destruct (IHhas_type1 vs xi Hlog) as [v1 [Hv1 [Hv1' Hv1'']]].
	  destruct (IHhas_type2 vs xi Hlog) as [v2 [Hv2 [Hv2' Hv2'']]].
	  unfold normalises_pred.
	  exists <{(- v1, v2 -)}>; repeat (auto; split).
	  { eapply subst_step_pair; eauto. }
	  exists v1, v2. repeat (split; auto).
	- destruct (IHhas_type vs xi Hlog) as [v [Hv [Hv' Hv'']]].
	  inversion Hv'' as [v1 [v2 [Hv_eq [Hv1 Hv2]]]]; subst.
	  exists v1. inversion Hv; subst. repeat (split; auto).
	  eapply subst_step_fst; eauto.
	- destruct (IHhas_type vs xi Hlog) as [v [Hv [Hv' Hv'']]].
	  inversion Hv'' as [v1 [v2 [Hv_eq [Hv1 Hv2]]]]; subst.
	  exists v2. inversion Hv; subst. repeat (split; auto).
	  eapply subst_step_snd; eauto.
	- apply norm_val; auto.
	  exists e.[up (env_subst vs)]; split; auto.
	  intros v Hv.
	  assert (Hsubst: e.[up (env_subst vs)].[v/] = e.[env_subst (v :: vs)]) by by asimpl.
	  rewrite Hsubst. apply IHhas_type. simpl; eauto.
	- destruct (IHhas_type1 vs xi Hlog) as [v1 [Hv1 [Hv1' Hv1'']]].
	  destruct (IHhas_type2 vs xi Hlog) as [v2 [Hv2 [Hv2' Hv2'']]].
	  inversion Hv1'' as [e [He He']].
	  apply He' in Hv2''.
	  unfold normalises_pred in Hv2''.
	  destruct Hv2'' as [v' [Hv' [Hv'' Hv''']]]; subst.
	  exists v'. repeat (split; auto). subst.
	  eapply subst_step_app; eauto.
	- apply norm_val; auto.
	  exists e.[env_subst vs]. split; auto.
	  intros P.
	  apply IHhas_type. simpl.
	  by apply log_rel_seq_weaken.
	- destruct (IHhas_type vs xi Hlog) as [v [Hv [Hv' Hv'']]].
	  inversion Hv'' as [b [Hb Hb']]; subst.
	  destruct (Hb' (lr_val xi T')) as [v0 [Hv0' [Hv0'' Hv0''']]].
	  apply norm_mono with (P := lr_val (lr_val xi T' :: xi) T).
	  apply log_rel_subst.
	  exists v0. repeat (split; auto).
	  apply subst_step_tapp with (b := b); auto.
Qed.

Theorem normalisation: forall e T,
	[] |- e : T ->
	normalises e.
Proof.
	intros e T HT.
	apply fundamental_theorem with (vs := []) (xi := []) in HT; cbn; auto.
	unfold normalises_pred in HT.
	asimpl in HT. destruct HT as [v [Hv [Hv' Hv'']]].
	unfold normalises. eauto.
Qed.

End SystemF.
