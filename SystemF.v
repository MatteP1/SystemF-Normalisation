(** * System F *)

(* NOTE: THE FOLLOWING DEVELOPMENT IS AN EXTENSION OF stlc.v FROM PROGRAMMING LANGUAGE FOUNDATIONS. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From SFN Require Import Maps.
Require Import List.
Import ListNotations.

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

(* Normalise tactic *)
Tactic Notation "print_goal" :=
	match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
	repeat (print_goal; eapply multi_step ;
				[ (eauto 10; fail) | (instantiate; simpl)]);
	apply multi_refl.
						

Module SystemF.

(* ================================================================= *)
(** ** Types *)

Inductive ty : Type :=
	| Ty_Var   : string -> ty
	| Ty_Unit  : ty
	| Ty_Prod  : ty -> ty -> ty
	| Ty_Arrow : ty -> ty -> ty
	| Ty_Abs   : string -> ty -> ty.

(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
	| tm_var   : string -> tm
	| tm_unit  : tm
	| tm_pair  : tm -> tm -> tm
	| tm_fst   : tm -> tm
	| tm_snd   : tm -> tm
	| tm_abs   : string -> tm -> tm
	| tm_app   : tm -> tm -> tm
	| tm_tyabs : tm -> tm
	| tm_tyapp : tm -> tm.

Declare Custom Entry sysf.
Notation "<{ e }>" := e (e custom sysf at level 99).
Notation "( x )" := x (in custom sysf, x at level 99).
Notation "x" := x (in custom sysf at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom sysf at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom sysf at level 1, left associativity).
Notation "\ x , y" :=
	(tm_abs x y) (in custom sysf at level 90, x at level 99,
						y custom sysf at level 99,
						left associativity).

Coercion tm_var : string >-> tm.

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
	| v_abs : forall x t1,
		value <{\x, t1}>
	| v_tyabs : forall t,
		value <{/\ t}>.

Hint Constructors value : core.

(* ================================================================= *)
(** ** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom sysf at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
	match t with
	| <{()}> => <{()}>
	| tm_var y =>
		if String.eqb x y then s else t
	| <{\y, t1}> =>
		if String.eqb x y then t else <{\y, [x:=s] t1}>
	| <{t1 t2}> =>
		<{([x:=s] t1) ([x:=s] t2)}>
	| <{(- t1, t2 -) }> =>
		<{(- [x:=s] t1, [x:=s] t2 -) }>
	| <{fst t}> =>
		<{fst [x:=s] t}>
	| <{snd t}> =>
		<{snd [x:=s] t}>
	| <{/\ t}> =>
		<{/\ [x:=s] t}>
	| <{t _}> =>
		<{([x:=s] t) _}>
	end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom sysf).

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
	| s_abs1 t :
		substi s x (tm_abs x t) (tm_abs x t)
	| s_abs2 y t k :
		x <> y ->
		substi s x t k ->
		substi s x (tm_abs y t) (tm_abs y k)
	| s_app t1 t2 s1 s2 :
		substi s x t1 s1 ->
		substi s x t2 s2 ->
		substi s x (tm_app t1 t2) (tm_app s1 s2)
	| s_unit :
		substi s x tm_unit tm_unit
	| s_pair t1 t2 s1 s2 :
		substi s x t1 s1 ->
		substi s x t2 s2 ->
		substi s x (tm_pair t1 t2) (tm_pair s1 s2)
	| s_fst t k :
		substi s x t k ->
		substi s x (tm_fst t) (tm_fst k)
	| s_snd t k :
		substi s x t k ->
		substi s x (tm_snd t) (tm_snd k)
	| s_tyabs t k :
		substi s x t k ->
		substi s x (tm_tyabs t) (tm_tyabs k)
	| s_tyapp t k :
		substi s x t k ->
		substi s x (tm_tyapp t) (tm_tyapp k)
.

Hint Constructors substi : core.

Theorem substi_correct : forall s x t t',
	<{ [x:=s]t }> = t' <-> substi s x t t'.
Proof.
	intros s x t t'. split; intros H.
	- generalize dependent t'. induction t as [s'| |s'| | | | | |];
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
	end.


(* ================================================================= *)
(** ** Reduction *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
	| ST_AppAbs : forall x t1 v2,
			value v2 ->
			<{(\x, t1) v2}> --> <{ [x:=v2]t1 }>
	| ST_App1 : forall t1 t1' t2,
			t1 --> t1' ->
			<{t1 t2}> --> <{t1' t2}>
	| ST_App2 : forall v1 t2 t2',
			value v1 ->
			t2 --> t2' ->
			<{v1 t2}> --> <{v1  t2'}>
	| ST_Pair1 : forall t1 t1' t2,
			t1 --> t1' ->
			<{(- t1, t2 -)}> --> <{(- t1', t2 -)}>
	| ST_Pair2 : forall v1 t2 t2',
			value v1 ->
			t2 --> t2' ->
			<{(- v1, t2 -)}> --> <{(- v1, t2' -)}>
	| ST_FstPair : forall v1 v2,
		value v1 ->
		value v2 ->
		<{fst (- v1, v2 -)}> --> <{v1}>
	| ST_SndPair : forall v1 v2,
		value v1 ->
		value v2 ->
		<{snd (- v1, v2 -)}> --> <{v2}>
	| ST_TyApp : forall t t',
		t --> t' ->
		<{t _}> --> <{t' _}>
	| ST_TyAppTyAbs : forall t,
		<{(/\ t) _}> --> <{t}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).


(* ################################################################# *)
(** * Typing *)

(* We define a notion of A being free in type T *)
Inductive free : string -> ty -> Prop :=
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
		free b (Ty_Abs a T).

Inductive not_free : string -> ty -> Prop :=
	| NotFree_Var : forall a b,
		a <> b ->
		not_free b (Ty_Var a)
	| NotFree_Unit : forall a, not_free a Ty_Unit
	| NotFree_Prod : forall a T1 T2, 
		not_free a T1 ->
		not_free a T2 ->
		not_free a (Ty_Prod T1 T2)
	| NotFree_Arrow : forall a T1 T2,
		not_free a T1 ->
		not_free a T2 ->
		not_free a (Ty_Arrow T1 T2)
	| NotFree_Abs : forall a T,
		not_free a (Ty_Abs a T).

(* ================================================================= *)
(** ** Contexts *)

Definition varContext := partial_map ty.
Definition typeCtxt := list string.

Inductive free_varctxt : string -> varContext -> Prop :=
	| FreeCtxt_Gamma : forall a Gamma x T,
		Gamma x = Some T ->
		free a T ->
		free_varctxt a Gamma.

Inductive not_free_varctxt : string -> varContext -> Prop :=
	| NotFreeCtxt_Empty : forall a, not_free_varctxt a empty
	| NotFreeCtxt_Gamma : forall a Gamma Gamma' x T,
		Gamma = update Gamma' x T ->
		not_free_varctxt a Gamma' ->
		not_free a T ->
		not_free_varctxt a Gamma.

(* ================================================================= *)

Reserved Notation "Delta '|;' Gamma '|-' t ':' T"
			(at level 101,
				t custom sysf, T custom sysf at level 0).

Inductive has_type : typeCtxt -> varContext -> tm -> ty -> Prop :=
	| T_Unit : forall Delta Gamma,
		Delta |; Gamma |- () : Unit
	| T_Var : forall Delta Gamma x T1,
		Gamma x = Some T1 ->
		Delta |; Gamma |- x : T1
	| T_Prod : forall Delta Gamma T1 T2 t1 t2,
		Delta |; Gamma |- t1 : T1 ->
		Delta |; Gamma |- t2 : T2 ->
		Delta |; Gamma |- (- t1, t2 -) : (~ T1 * T2 ~)
	| T_Fst : forall Delta Gamma T1 T2 t,
		Delta |; Gamma |- t : ((~ T1 * T2 ~)) ->
		Delta |; Gamma |- fst t : T1
	| T_Snd : forall Delta Gamma T1 T2 t,
		Delta |; Gamma |- t : ((~ T1 * T2 ~)) ->
		Delta |; Gamma |- snd t : T2
	| T_Abs : forall Delta Gamma x T1 T2 t,
		Delta |; (x |-> T1 ; Gamma) |- t : T2 ->
		Delta |; Gamma |- \x, t : (T1 -> T2)
	| T_App : forall T1 T2 Delta Gamma t1 t2,
		Delta |; Gamma |- t1 : (T2 -> T1) ->
		Delta |; Gamma |- t2 : T2 ->
		Delta |; Gamma |- t1 t2 : T1
	| T_TLam : forall Delta Gamma a T t,
		a :: Delta |; Gamma |- t : T ->
		not_free_varctxt a Gamma ->
		Delta |; Gamma |- /\ t : (\All a .. T)
	| T_TApp : forall T T' Tsubst Delta Gamma t a,
		Delta |; Gamma |- t : (\All a .. T) ->
		Tsubst = ty_subst T T' a ->
		Delta |; Gamma |- t _ : Tsubst

where "Delta '|;' Gamma '|-' t ':' T" := (has_type Delta Gamma t T).

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
		[] |; empty |-
			\x, x x : T).
Proof.
	intros [T H]. inversion H; subst. inversion H5; subst.
	inversion H4; subst. inversion H7; subst. rewrite H3 in H6. 
	inversion H6; subst. apply (ty_not_eq T2 T3). assumption.
Qed.
(** [] *)

End SystemF.
