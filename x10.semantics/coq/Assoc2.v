(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Properties of functional association lists needed by parts of the development
   (but not needed by CopyObj) *)
Require Export ListUtil2.
Require Export Assoc.

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Sorting.Sorted.
Section Assoc2.

Context {A B:Type}.
Let assoc := list (A*B).
Context {dec:EqDec A equiv}.

Definition codomain (l:list (A*B)) := map snd l.
Lemma domain_mswap_codomain (l:list (A*B)) : domain (mswap l) = codomain l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma equal_part_upto (P:B->Prop) {f:A->B} {l1 x l2 l1' x' l2'} :
          l1 ++ x::l2 = l1'++x'::l2'
          -> Forall P (map f l1)
          -> Forall P (map f l1')
          -> ~ P (f x)
          -> ~ P (f x')
          -> l1 = l1' /\ x = x' /\ l2 = l2'.
Proof.
  revert x l2 l1' x' l2'.
  induction l1; destruct l1'; simpl; intros.
  - inversion H; auto.
  - inversion H; inversion H1; subst. intuition.
  - inversion H; inversion H0; subst. intuition.
  - inversion H; inversion H0; inversion H1; subst.
    destruct (IHl1 _ _ _ _ _ H6 H9 H13); subst; intuition.
Qed.

Lemma fold_right_flat_map (f:A->list B) l: flat_map f l = List.fold_right (fun a b => f a ++ b) nil l.
Proof.
  induction l; simpl; intuition.
Qed.

Lemma obj_compact_in_in {eqA:EqDec A equiv} {l:list (A*B)} {a}: 
  In a (obj_compact l) ->
  In a l.
Proof.
  revert a.
  induction l; simpl; intuition; subst.
  destruct a.
  destruct (l[@a0]); simpl in *; intuition.
Qed.

Lemma lookup_update1 {eqdec:EqDec A equiv} :
  forall {l:list (A*B)} {a v v'},
    (l[a~~>v])[@a] = Some v' ->
    v = v'.
Proof.
  induction l; simpl in *; intros; try discriminate.
  unfold Util.update, lookup in *; simpl in *.
  destruct a; eqdestr; simpl in *.
  - eqdestr; unfold equiv, complement in *; congruence.
  - eqdestr; eauto; congruence.
Qed.

End Assoc2.