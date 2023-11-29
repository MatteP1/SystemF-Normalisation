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
(** ** Substitution *)

(* Reserved Notation "'[' x ':=' s ']' e" (in custom sysf at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (e : tm) : tm :=
	match e with
	| <{()}> => <{()}>
	| tm_var y =>
		if String.eqb x y then s else e
	| <{\y, e1}> =>
		if String.eqb x y then e else <{\y, [x:=s] e1}>
	| <{e1 e2}> =>
		<{([x:=s] e1) ([x:=s] e2)}>
	| <{(- e1, e2 -) }> =>
		<{(- [x:=s] e1, [x:=s] e2 -) }>
	| <{fst e1}> =>
		<{fst [x:=s] e1}>
	| <{snd e2}> =>
		<{snd [x:=s] e2}>
	| <{/\ e1}> =>
		<{/\ [x:=s] e1}>
	| <{e1 _}> =>
		<{([x:=s] e1) _}>
	end

where "'[' x ':=' s ']' e" := (subst x s e) (in custom sysf).

(* Example *)
Check <{[x:=()] x}>.


(** **** Exercise: 3 stars, standard (substi_correct)

	The definition that we gave above uses Coq's [Fixpoint] facility
	to define substitution as a _function_.  Suppose, instead, we
	wanted to define substitution as an inductive _relation_ [substi].
	We've begun the definition by providing the [Inductive] header and
	one of the constructors; your job is to fill in the rest of the
	constructors and prove that the relation you've defined coincides
	with the function given above. *)

Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
	| s_var1 :
		substi s x (tm_var x) s
	| s_var2 y :
		x <> y ->
		substi s x y y
	| s_abs1 e :
		substi s x (tm_abs x e) (tm_abs x e)
	| s_abs2 y e k :
		x <> y ->
		substi s x e k ->
		substi s x (tm_abs y e) (tm_abs y k)
	| s_app e1 e2 s1 s2 :
		substi s x e1 s1 ->
		substi s x e2 s2 ->
		substi s x (tm_app e1 e2) (tm_app s1 s2)
	| s_unit :
		substi s x tm_unit tm_unit
	| s_pair e1 e2 s1 s2 :
		substi s x e1 s1 ->
		substi s x e2 s2 ->
		substi s x (tm_pair e1 e2) (tm_pair s1 s2)
	| s_fst e k :
		substi s x e k ->
		substi s x (tm_fst e) (tm_fst k)
	| s_snd e k :
		substi s x e k ->
		substi s x (tm_snd e) (tm_snd k)
	| s_tyabs e k :
		substi s x e k ->
		substi s x (tm_tyabs e) (tm_tyabs k)
	| s_tyapp e k :
		substi s x e k ->
		substi s x (tm_tyapp e) (tm_tyapp k)
.

Hint Constructors substi : core.

Theorem substi_correct : forall s x e e',
	<{ [x:=s]e }> = e' <-> substi s x e e'.
Proof.
	intros s x e e'. split; intros H.
	- generalize dependent e'. induction e as [s'| |s'| | | | | |];
	intros; subst; cbn; auto. destruct (eqb_spec x s'); subst; auto.
	destruct (eqb_spec x s0); subst; auto.
	- induction H; cbn; subst; try rewrite eqb_refl;
	try rewrite (proj2 (eqb_neq _ _)); auto.
Qed.
(** [] *)

Fixpoint ty_subst (T : ty) (S : ty) (a : string): ty :=
	match T with
	| Ty_Var b =>
		if String.eqb a b then S else T
	| Ty_Unit => Ty_Unit
	| Ty_Prod T1 T2 => Ty_Prod (ty_subst T1 S a) (ty_subst T2 S a)
	| Ty_Arrow T1 T2 => Ty_Arrow (ty_subst T1 S a) (ty_subst T2 S a)
	| Ty_Abs b T' =>
		if String.eqb a b then T else (ty_subst T' S a)
	end. *)


(* ================================================================= *)
(** ** Reduction *)

Reserved Notation "e '-->' e'" (in custom sysf at level 40).

Inductive step : tm -> tm -> Prop :=
	| ST_AppAbs : forall e v,
			value v ->
			tm_app (tm_abs e) v --> e.[v/]
	| ST_App1 : forall e1 e1' e2,
			e1 --> e1' ->
			<{e1 e2}> --> <{e1' e2}>
	| ST_App2 : forall v1 e2 e2',
			value v1 ->
			e2 --> e2' ->
			<{v1 e2}> --> <{v1  e2'}>
	| ST_Pair1 : forall e1 e1' e2,
			e1 --> e1' ->
			<{(- e1, e2 -)}> --> <{(- e1', e2 -)}>
	| ST_Pair2 : forall v1 e2 e2',
			value v1 ->
			e2 --> e2' ->
			<{(- v1, e2 -)}> --> <{(- v1, e2' -)}>
	| ST_FstPair : forall v1 v2,
		value v1 ->
		value v2 ->
		<{fst (- v1, v2 -)}> --> <{v1}>
	| ST_SndPair : forall v1 v2,
		value v1 ->
		value v2 ->
		<{snd (- v1, v2 -)}> --> <{v2}>
	| ST_TyApp : forall e e',
		e --> e' ->
		<{e _}> --> <{e' _}>
	| ST_TyAppTyAbs : forall e,
		<{(/\ e) _}> --> <{e}>

where "e '-->' e'" := (step e e').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "e1 '-->*' e2" := (multistep e1 e2) (at level 40).


Definition normalises (e : tm) := exists v, value v /\ e -->* v.

Example normalise_value : normalises (tm_abs (tm_var 0)).
Proof.
	exists (tm_abs (tm_var 0)). split; auto.
	apply multi_refl.
Qed.

Example normalise_fun : normalises (tm_app (tm_abs (tm_var 0)) tm_unit).
Proof.
	exists <{()}>. split; auto.
	eapply multi_step; auto.
	apply multi_refl.
Qed.

Example stuck : ~ normalises (<{fst () }>).
Proof.
	intros H. inversion H as [v [Hv Hstep]].
	inversion Hstep.
	- subst. inversion Hv.
	- inversion H0.
Qed.


Definition normalises_pred (e : tm) (P : tm -> Prop) :=
	exists v, value v /\ e -->* v /\ P v.

(* ################################################################# *)
(** * Typing *)

(* We define a notion of A being free in type T *)
(* Inductive free : var -> ty -> Prop :=
	| Free_Var : forall a, free a (Ty_Var a)
	| Free_Unit : forall a, free a Ty_Unit
	| Free_Prod1 : forall a T1 T2,
		free a T1 ->
		free a (Ty_Prod T1 T2)
	| Free_Prod2 : forall a T1 T2,
		free a T2 ->
		free a (Ty_Prod T1 T2)
	| Free_Arrow1 : forall a T1 T2,
		free a T1 ->
		free a (Ty_Arrow T1 T2)
	| Free_Arrow2 : forall a T1 T2,
		free a T2 ->
		free a (Ty_Arrow T1 T2)
	| Free_Tabs : forall a b T,
		a <> b ->
		free b T ->
		free b (Ty_Abs T). *)

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
		nth_error Gamma x = Some T1 ->
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

Definition predCtxt := partial_map Prop.

(* TODO: DEFINE LR *)

(* Fixpoint lr_val (Delta : typeCtxt) (xi : predCtxt) (t : ty) (v : tm) : Prop :=
	match t with
	| Ty_Var a =>
		xi a
	| Ty_Unit =>
		v = <{()}>
	| Ty_Prod T1 T2 =>
		exists v1 v2,
		v = <{(- v1, v2 -)}> /\
		lr_val Delta xi T1 v1 /\
		lr_val Delta xi T2 v2
	| Ty_Arrow T1 T2 =>
		True
	| Ty_Abs a T =>
		True
	end. *)

(* ================================================================= *)
(** ** Helper Lemmas *)


(* TODO: STATE AND PROVE LogRel-Weaken, LogRel-Subst, AND LogRel-Seq-Weaken *)


(* ################################################################# *)
(** * Fundamental Theorem and Soundness *)


Theorem normalisation: forall e T,
	[] |- e : T ->
	normalises e.
Proof.
	intros e T HT.
	(* Apply fundamental theorem *)
	Admitted.


End SystemF.
