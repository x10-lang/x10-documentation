(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Properties of functional lists needed by parts of the development 
   (but not needed by CopyObj) *)
Require Export Util.
Require Export ListUtil.
Require Export Permutation.

Require Import Le.

Require Import Coq.Sorting.Sorted.
Require Import Coq.Logic.Eqdep_dec.

Require Import List.

Section ListUtil2.
Context {A:Type}.

Definition singleton (v:A) := v::(@List.nil A).

Lemma Forall_incl : forall (f1 f2:A->Prop) l, 
  (forall x, In x l -> f1 x -> f2 x) ->
  Forall f1 l -> Forall f2 l.
Proof.
  Hint Constructors Forall.
  intros.
  induction H0; dts firsorder.
Qed.

Lemma in_mid (v:A) l1 l2 : In v (l1 ++ v :: l2).
Proof.
  rewrite in_app_iff; simpl; intuition.
Qed.

Lemma map_eq {B} {f g:A->B} {l} :
  Forall (fun x => f x = g x) l ->
  map f l = map g l.
Proof.
  induction l; trivial.
  inversion 1; simpl; subst.
  f_equal; auto.
Qed.

End ListUtil2.
Hint Resolve in_mid.

Ltac eqdestr :=
match goal with
  | [ |- context [ (@equiv_dec ?a ?b ?c ?d ?e ?f)]] => destruct (@equiv_dec a b c d e f)
  | [H: context [ (@equiv_dec ?a ?b ?c ?d ?e ?f)] |- _] => destruct (@equiv_dec a b c d e f)
end.
