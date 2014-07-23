(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Basic definitions and lemmas used throughout the development *)

Require Import Basics.

Require Export Bool.
Require Export List.
Require Export Morphisms.
Require Export EquivDec.
Require Export RelationClasses.

(* These typeclasses are used to allow the same notation to be used
   for the corresponding concepts with different types *)
Class Lookup A B C :=
  lookup : forall (a:A) (b:B), C.
Class Update A B C := 
  update : forall (a:A) (b:B) (c:C), A.

Class Subst A B C := 
  subst : forall (a:A) (b:B) (c:C), A.

Notation "v [@ p ]" := (lookup v p) (at level 1, format "v [@ p ]").
Notation "a '[' b ~~> c ']'" := (update a b c) (at level 1, format "a [ b ~~> c ]").

Notation "a '[' b // c ']'" := (subst a c b) (at level 1, format "a [ b // c ]").

(* The number of places is "implicit" state throughout the development. *)
Class StaticConfig := {
 PLACES : nat;
 PLACES_gt0 : PLACES > 0
}.

Ltac poses H := let HH := (fresh "P") in pose (HH:=H); clearbody HH.

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ => idtac
  end.

Ltac extend P :=
  let t := type of P in
    notHyp t; generalize P; intro.

Hint Unfold Proper respectful compose arrow impl const flip apply complement.

Lemma equiv_decb_true A `{EqDec A} {x y : A} : x ==b y = true <-> x === y.
Proof.
  unfold equiv_decb. destruct (equiv_dec x y); intuition.
Qed.

Lemma equiv_decb_false A `{EqDec A} {x y : A} : x ==b y = false <-> x =/= y.
Proof.
  unfold equiv_decb. destruct (equiv_dec x y); intuition.
Qed.

Ltac dt tac := repeat progress (try autounfold in *; try (intros; (repeat progress try match goal with
    | [H: ?x = ?x |- _] => clear H
    | [H1: ?x = ?y, H2:?y = ?x|- _] => clear H1 || clear H2
    | [H: prod _ _ |- _ ] => destruct H
    | [H: _ && _ = true |- _] =>   apply andb_true_iff in H
    | [H: _ && _ = false |- _] =>   apply andb_false_iff in H
    | [H: _ || _ = true |- _] =>   apply orb_true_iff in H
    | [H: _ || _ = false |- _] =>   apply orb_false_iff in H
    | [H: Some _ = Some _ |- _] => inversion H; clear H
    | [H: _::_ = _::_ |- _] => inversion H; clear H
    | [|- _ && _ = true ] =>   apply andb_true_iff
    | [|- _ && _ = false ] =>   apply andb_false_iff
    | [|- _ || _ = true ] =>   apply orb_true_iff
    | [|- _ || _ = false ] =>   apply orb_false_iff
    | [H: ex _ |- _] => destruct H
    | [H: _ /\ _ |- _] => destruct H
    | [|- _ :: _ = _ :: _] => f_equal
    | [|- S _ = S _] => f_equal
    | [H:?x ==b ?y = true |- _] => apply equiv_decb_true in H
    | [H:?x ==b ?y = false |- _] => apply equiv_decb_false in H
    | [|- ?x ==b ?y = true ] => apply equiv_decb_true
    | [|- ?x ==b ?y = false] => apply equiv_decb_false
  end); intros; try simpl in *; try subst; try autorewrite with rewrites in *; trivial; try discriminate); try tac).


Ltac dts tac := dt ltac:(try tac; try intuition; try eauto).

(* Since this is declared as Opaque, Coq will not reduce it during normalization.
   However, since the type unit is only inhabited by one element, it can still 
   be reduced explicitly using pattern-matching.  This is used to control
   reduction in specific cases, where reduction is not required and takes a long time. *)
Lemma master_key : unit. 
Proof. exact tt. Qed.
