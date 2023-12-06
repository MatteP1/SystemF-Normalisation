(** * System F *)

(** In this file we define the language System F *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From stdpp Require Import gmap.
From Autosubst Require Export Autosubst.

(* NOTE: The following two definition were taken from Smallstep.v 
	from software-foundations. *)

(* Relation *)
Definition relation (X : Type) := X -> X -> Prop.

(* Multi step Relation *)
Inductive multi {X : Type} (R : relation X) : relation X :=
	| multi_refl : forall (x : X), multi R x x
	| multi_step : forall (x y z : X),
	R x y ->
						multi R y z ->
						multi R x z.

Lemma multi_trans : forall (X: Type) (R: relation X) a b c,
	multi R a b ->
	multi R b c ->
	multi R a c.
Proof.
	intros X R a b c Hab. 
	induction Hab as [d | a a' b Haa' Ha'b IH].
	- trivial.
	- intros Hbc. apply IH in Hbc as Ha'c. 
		apply multi_step with a'; assumption.
Qed.

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


(* ================================================================= *)
(** ** Notation *)
Declare Custom Entry sysf.
Notation "<{ e }>" := e (e custom sysf at level 99).
Notation "( x )" := x (in custom sysf, x at level 99).
Notation "x" := x (in custom sysf at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom sysf at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom sysf at level 1, left associativity).

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

(* The following lemmas follow directly from the defintion of fill.
	They are used to rewrite expressions as plugged contexts. *)
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

(* We can compose two contexts K and K' as follows: *)
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

Lemma fill_compose: forall e K K',
	fill K (fill K' e) = fill (compose K K') e.
Proof.
	intros e K. revert e. induction K; intros; cbn; try rewrite IHK; auto.
Qed.

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

Hint Constructors head_reduction : core.

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
Proof. apply multi_trans. Qed.

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

(* ################################################################# *)
(** * Typing *)

(* ================================================================= *)
(** ** The Typing Relation *)

Definition varContext := list ty.

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

End SystemF.
