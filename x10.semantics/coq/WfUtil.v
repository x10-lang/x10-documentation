(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Some defintions and lemmas about creating well founded relation *)
Require Import Wf.

Section wf_pullback.

(* given a well founded measure on B, 
   we can pull it back along a function (A->B) 
   to create a well founded relation on A *)

Context {A B:Type} {R:A->A->Prop} (f:B->A) (wfR:well_founded R).

Lemma acc_pullback :
  forall a, Acc R a ->
  forall b, f(b) = a -> Acc (fun x y => R (f x) (f y)) b.
clear.
intros a rA.
induction rA; simpl in *; intros.
apply Acc_intro; intros.
subst. eauto. 
Defined.

Lemma wf_pullback : well_founded (fun x y => R (f x) (f y)).
Proof.
red; intros.
eapply acc_pullback; eauto.
Defined.

End wf_pullback.

(* Given well founded relations on A and B, we can combine them to get a well
   founded relation on pairs (A,B) *)
Section wf_pair.
Context {A B:Type}.
Context (ltA:A->A->Prop).
Context (ltB:B->B->Prop).

Definition wf_pair (a a':A*B) 
  := ltA (fst a) (fst a') 
  \/ ((fst a= fst a') /\ ltB (snd a) (snd a')).

Lemma wf_pair_acc : well_founded ltA ->
 forall a, Acc ltA a -> well_founded ltB -> forall b, Acc ltB b -> Acc wf_pair (a,b).
Proof.
 intros ??; induction 1. intros ??; induction 1.
 apply Acc_intro.   
 intros [??]; destruct 1 as [?|[??]]; simpl in *; subst; auto.
Defined.

Lemma wf_pair_wf : well_founded ltA ->
  well_founded ltB -> well_founded wf_pair.
  Hint Resolve wf_pair_acc.
  intros ?? [? ?].
  auto.
Defined.

Context {C D:Type} (fC:C->A) (fD:D->B).

Definition pair_pb cd := (fC (fst cd), fD (snd cd)).

(* We can combine our pullback and our pairing *)
Definition wf_pair_pb := (fun x y => wf_pair (pair_pb x) (pair_pb y)).

Theorem wf_pair_pb_wf : well_founded ltA -> well_founded ltB -> well_founded wf_pair_pb.
Proof.
  intros; unfold wf_pair_pb; apply wf_pullback; apply wf_pair_wf; auto.
Defined.

End wf_pair.