(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Reasons about the relationship between (local) reachability and heap isomorphism. *)

Require Import Util.
Require Import Assoc.
Require Import Auxiliary.
Require Export HeapIso.
Require Export Reachable.
Require Import WfUtil.
Require Import List.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import Morphisms.
Require Coq.Vectors.Vector.
Require Import Coq.Classes.EquivDec.
Require Import Permutation.
Require Import Bool.

Ltac tcopy tac := try
  match goal with
    | [H:obj |- _ ] => let nd := fresh "nd" in 
                       destruct H as [H nd]; simpl in *; 
                       (apply sbool_nodup in nd || poses (sbool_nodup nd))
    | [|-  sbool (NoDup_dec val_eqdec (domain _)) = true ] => apply nodup_sbool
    | [ H: NoDup (_ :: _) |- _ ] => inversion H; clear H; try subst
    | [ H:forallb _ _ = true |- _ ] => rewrite forallb_forall in H
    | [ |- forallb _ _ = true ] => rewrite forallb_forall
    | [ H:forallb2 _ _ _ = true |- _ ] => rewrite forallb2_Forallb in H
    | [ |- forallb2 _ _ _ = true ] => rewrite forallb2_Forallb
    | [H:reachable_from ?h ?x (Object ?o) |- _] => 
      match x with
        | (Object _) => fail 1
        | _ => destruct (reachable_from_to_obj _ H)
      end
    | [ H:context [(@equiv_dec ?A ?B ?C ?D ?X ?Y)] |- _] => destruct (@equiv_dec A B C D X Y); unfold equiv, complement in *; try subst
    | [ |- context [(@equiv_dec ?A ?B ?C ?D ?X ?Y)]] => destruct (@equiv_dec A B C D X Y);  unfold equiv, complement in *; try subst
    | [H:match ?X with
           | Some _ => _
           | None => false
         end=true |- _] =>  let Heq := (fresh "Heq") in 
                            case_eq (X); [intros ? Heq| intros Heq]; 
                            rewrite Heq in H; [try rewrite Heq in *|discriminate]
    | [H:match ?v with 
           | Object _ => _
           | GlobalObject _ _ => _
           | Nat _ => _ 
         end = true |- _] => destruct v
  end; try tac.

Ltac t' tac := (dts ltac:(tcopy tac)).
Ltac t := t' idtac.

Ltac itac := try match goal with
  | [H1: inIso_obj ?iso (exist _ ?v1 _) (exist _ ?v2 _) = true,
     H2: ?v1[@?x] = (Some (Object _)) |- _] =>
    match goal with
      |[H:v2[@x] = _ |- _ ] => fail 1
      | _ => destruct (inIso_obj_lookup H1 H2); t
    end
end.

Ltac t' tac ::= (dts ltac:(itac; tcopy tac)).
Ltac t ::= t' idtac.

Section heap_iso_reach.
Context {sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Hint Unfold equiv complement.
Hint Constructors reachable_from.

Lemma isIso_reach : forall {src_heap dest_heap:heap}
                      {v oid iso}, isIso src_heap dest_heap iso = true ->
                                   reachable_from src_heap v (Object oid) -> 
                                   forall {v'}, inIso_val iso v v' = true ->
                               exists oid', iso[@oid]=Some oid'
                                         /\ reachable_from dest_heap v' (Object oid').
Proof.
  intros src_heap dest_heap v oid iso isiso reach.
  dependent induction reach; intros.
  - repeat t.
  - specialize (IHreach _ oid isiso (eq_refl _)).
    unfold isIso, inIso_map, inIso_oids in isiso.
    repeat t.
    poses (isiso _ (lookup_in Heq)).
    t.
    rewrite H1 in H3; t.
    poses (inIso_obj_lookup' P0 H0). 
    t.
    rewrite H1 in H4; t. clear H3 H2.
    specialize (IHreach (Object x0)).
    t.
    rewrite H1 in *.
    destruct IHreach; t.
Qed.

Lemma isIso_reach_obj : forall {src_heap dest_heap:heap}
                      {v oid iso}, isIso src_heap dest_heap iso = true ->
                                   reachable_from_obj src_heap v (Object oid) -> 
                                   forall {v'}, inIso_obj iso v v' = true ->
                               exists oid', iso[@oid]=Some oid'
                                         /\ reachable_from_obj dest_heap v' (Object oid').
Proof.
  unfold reachable_from_obj; t.
  destruct (isIso_reach H H2 (v':=(Object x0)));
  [apply inIso_val_oids; auto|].
  t.
  eexists; intuition eauto.
Qed.

Section reach_list.

Lemma reach_list_iso : forall {src_heap iso src dest_heap src'},
                        bidet iso -> 
                        reach_list src_heap (domain iso) src ->
                        isIso src_heap dest_heap iso = true ->
                        inIso_val iso src src' = true ->
                        reach_list dest_heap (domain (mswap iso)) src'.
Proof.
  unfold reach_list; intros.
  destruct (in_domain_in H3).
  apply mswap_in in H4.
  poses (isIso_reach H1 (H0 _ (in_dom H4)) H2); t' dtac.
  destruct H.
  erewrite in_lookup_nodup in H5; eauto.
  t.
Qed.

Lemma reach_list_obj_iso : forall {src_heap iso src dest_heap src'},
                        bidet iso -> 
                        reach_list_obj src_heap (domain iso) src ->
                        isIso src_heap dest_heap iso = true ->
                        inIso_obj iso src src' = true ->
                        reach_list_obj dest_heap (domain (mswap iso)) src'.
Proof.
  unfold reach_list_obj; intros.
  destruct (in_domain_in H3).
  apply mswap_in in H4.
  poses (isIso_reach_obj H1 (H0 _ (in_dom H4)) H2); t' dtac.
  destruct H.
  erewrite in_lookup_nodup in H5; eauto.
  t.
Qed.

End reach_list.

Opaque heap.

Lemma iso_val_wf_src : forall src_heap v iso v' dest_heap, 
                             inIso_val iso v v' = true
                          -> isIso src_heap dest_heap iso = true
                          -> wf_val src_heap v.
Proof.
  unfold wf_val.
  intros. revert v' H.
  dependent induction H1; intros.
  - unfold isIso, inIso_map in H0. t.
    specialize (H0 _ (lookup_in Heq)). apply inIso_oids_inv in H0.
    red; t.
  - t. specialize (IHreachable_from _ H0 _ eq_refl).
    case_eq (iso[@x]); [intros o eq1|intros eq1]; rewrite eq1 in *.
    + apply (IHreachable_from (Object o)); t.
    + unfold isIso, inIso_map in H0.
      t.
      poses (H0 _ (lookup_in Heq)).
      apply inIso_oids_inv in P0.
      t.
      rewrite H3 in H.
      t.
      cut False; intuition.
      revert H6 H2 eq1 H0.
      unfold inIso_obj; simpl.
      congruence.
Qed.

Lemma iso_val_wf_dest : forall src_heap v iso v' dest_heap,
                             bidet iso 
                          -> inIso_val iso v v' = true
                          -> isIso src_heap dest_heap iso = true
                          -> wf_val dest_heap v'.
Proof.
  intros. 
  rewrite inIso_val_sym in H0; auto.
  rewrite isIso_sym in H1; auto.
  eapply iso_val_wf_src; eauto.
Qed.

End heap_iso_reach.