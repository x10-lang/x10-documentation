(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Defines reachability for a local heap *)
Require Export Auxiliary.
Require Import WfUtil.

Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Coq.Vectors.Vector.

Section reach.
Context {sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Hint Unfold Proper respectful impl.

Section reach_def.
Context (h:heap).
Local Reserved Notation "A '|->*' B" (at level 70).

Inductive reachable_from : val -> val -> Prop :=
 | RVRefl : forall src, src |->* src
 | RVStep : forall src dest (ob:obj) (f:fname) mid, h[@src] = Some ob -> 
   ob[@f] = Some mid -> mid |->* dest -> (Object src) |->* dest
where "A '|->*' B" := (reachable_from A B).

Definition reachable_from_obj (ob:obj) (dest:val) : Prop :=
  exists f mid, ob[@f] = Some mid /\ mid |->* dest.

Hint Unfold reachable_from_obj.
Hint Constructors reachable_from.
Hint Constructors PreOrder.
Hint Unfold Reflexive Transitive.

Global Instance reach_pre : PreOrder reachable_from.
Proof. 
  split.
  - dts idtac.
  - intros x y z. 
    induction 1; dts idtac.
Qed.

Lemma RVStep_simple : forall src dest (ob:obj) (f:fname), h[@src] = Some ob -> ob[@f] = Some dest -> (Object src) |->* dest.
Proof.
  eauto.
Qed.

Lemma RVStep_r : forall src dest (ob:obj) (f:fname) mid, src |->* (Object mid) ->  h[@mid] = Some ob -> ob[@f] = Some dest -> src |->* dest.
Proof.
  dts idtac.
  intros. rewrite H. eauto.
Qed.

Global Instance reach_reach_obj : Proper (eq ==> reachable_from ++> impl) reachable_from_obj.
Proof.
  dts idtac.
  econstructor; econstructor; split; [eauto|].
  etransitivity; eauto.
Qed.

Definition acyclic_from (v:val) := forall e, v |->* e -> e |->* v -> v = e.

Definition acyclic := forall v, acyclic_from v.

Hint Unfold acyclic acyclic_from.

Lemma acylic_asym : acyclic -> Antisymmetric val eq reachable_from.
Proof.
  dts idtac.
Qed.

Lemma reachable_from_to_obj : forall {a b}, reachable_from a (Object b) -> exists c, a = Object c.
Proof.
  intros.
  destruct a; inversion H; subst; eauto.
Qed.

Lemma reachable_from_to_eqobj : forall {a b}, reachable_from a b -> a = b \/ exists c, a = Object c.
Proof.
  intros.
  destruct a; inversion H; subst; eauto.
Qed.

Lemma reachable_from_contains_src {a b}: (Object a) <> b -> reachable_from (Object a) b -> contains h a.
Proof.
  intros neq rf.
  inversion rf; subst; try congruence.
  eexists; eauto.
Qed.

End reach_def.

Hint Constructors reachable_from. 
Global Instance reach_hincl : Proper (hincl ==> eq ==> eq ==> impl) reachable_from.
Proof.
dts idtac.
induction H2; eauto.
Qed.

Global Instance reach_obj_hincl : Proper (hincl ==> eq ==> eq ==> impl) reachable_from_obj.
Proof.
repeat red; intros; subst.
destruct H2 as [?[?[??]]].
rewrite H in H1. eauto.
Qed.

Section reach_list.

Context (h:heap).

Definition reach_list (l:list oid) (src:val) 
  := forall o, In o l -> reachable_from h src (Object o).

Definition reach_list_obj (l:list oid) (src:obj) 
  := forall o, In o l -> reachable_from_obj h src (Object o).

Lemma reach_list_nil : forall v, reach_list nil v.
Proof.
  red; intuition.
Qed.

Lemma reach_list_obj_nil : forall v, reach_list_obj nil v.
Proof.
  red; intuition.
Qed.

Hint Resolve reach_list_nil reach_list_obj_nil.

Lemma reach_list_obj_back : forall {m o v}, reach_list_obj m v ->  Some v = h[@o] -> reach_list m (Object o).
Proof.
  unfold reach_list_obj, reach_list.
  intros.
  destruct (H _ H1) as [?[?[??]]].
  eauto.
Qed.

Lemma reach_list_app : forall {m1 m2 v}, reach_list (m1++m2) v <-> (reach_list m1 v /\ reach_list  m2 v).
Proof.
  intros; unfold reach_list; intuition; try eapply H; try eapply in_or_app; eauto.
  destruct (in_app_or _ _ _ H); eauto.
Qed.
  
Lemma reach_list_obj_app : forall { m1 m2 v}, reach_list_obj (m1++m2) v <-> (reach_list_obj  m1 v /\ reach_list_obj m2 v).
Proof.
  intros; unfold reach_list_obj; intuition; try eapply H; try eapply in_or_app; eauto.
  destruct (in_app_or _ _ _ H); eauto.
Qed.

Lemma reach_list_obj_cons {m1 m2 f v} {ls:obj} : 
  forall (pfnin:~ In f (domain (proj1_sig ls))),
  reach_list m1 v ->
  NoDup m2 ->
  reach_list_obj m2 ls ->
  reach_list_obj (m1 ++ m2) (obj_cons f v ls pfnin).
Proof.
  unfold reach_list_obj, reach_list, reachable_from_obj.
  dts idtac.
  app_tac.
  dts idtac.
  - eexists; dts idtac. rewrite lookup_cons_eq; eauto.
  - specialize (H1 _ H3); dts idtac.
    exists x; dts idtac.
    rewrite lookup_cons_neq; eauto.
    intro; subst.
    elim pfnin.
    eapply in_dom; eapply lookup_in; eauto.
Qed.

Lemma reach_list_obj_cons' {m1 m2 f v} {ls:list (fname*val)} pf1 pf2 : 
  reach_list m1 v ->
  NoDup m2 ->
  reach_list_obj m2 (exist _ ls pf1) ->
  reach_list_obj (m1 ++ m2) (exist _ ((f,v)::ls) pf2).
Proof.
  unfold reach_list_obj, reach_list, reachable_from_obj.
  poses (sbool_nodup pf1).
  poses (sbool_nodup pf2).
  dts idtac.
  app_tac.
  dts idtac.
  - eexists; dts idtac. rewrite lookup_cons_eq; eauto.
  - specialize (H1 _ H3); dts idtac.
    exists x; dts idtac.
    rewrite lookup_cons_neq; eauto.
    intro; subst.
    inversion P0; subst.
    elim H6.
    eapply in_dom; eapply lookup_in; eauto.
Qed.


End reach_list.

Lemma reach_list_obj_inv_lookup : forall {h iso v1}, 
                                    reach_list h iso v1 -> 
                                    forall {src f}, src[@f] = Some v1 -> 
                                                    reach_list_obj h iso src.
Proof.
  unfold reach_list_obj, reach_list, reachable_from_obj.
  dts idtac.
Qed.

Lemma reach_list_reach : forall {h l src o}, NoDup l -> 
  reach_list h l src ->
  reachable_from h o src ->
  reach_list h l o.
Proof.
  unfold reach_list; intros.
  etransitivity; eauto.
Qed.

Lemma reach_list_obj_reach : forall {h l src o}, NoDup l -> 
  reach_list h l src ->
  reachable_from_obj h o src ->
  reach_list_obj h l o.
Proof.
unfold reach_list_obj, reachable_from_obj; intros.
destruct H1 as [? [? [??]]].
exists x; econstructor; intuition eauto.
eapply reach_list_reach; eauto.
Qed.



Section wf.

Definition wf_val (h:heap) (v:val) := forall oid,
	    reachable_from h v (Object oid) ->
	    contains h oid.

Definition wf_obj (h:heap) (o:obj) := forall oid, 
	   reachable_from_obj h o (Object oid) ->
	   contains h oid.

Definition wf_heap (h:heap) := forall a, contains h a -> wf_val h (Object a).

Global Instance wf_val_reach {h} : Proper (reachable_from h ++> impl) (wf_val h).
Proof.
  unfold wf_val; dts idtac.
  rewrite H1 in H; eauto.
Qed.  

Lemma wf_obj_reach {h} o v': wf_obj h o -> reachable_from_obj h o v' -> wf_val h v'.
Proof.
  unfold wf_obj, wf_val; dts idtac; intros.
  apply H.
  eapply reach_reach_obj; eauto.
Qed.

End wf.

End reach.