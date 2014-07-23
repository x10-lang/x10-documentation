(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Defines reachability for a global heap. Unlike local reachability (defined in Reachability),
   global reachability follows global references as well as local ones. *)
Require Export Auxiliary2.
Require Import HeapIsoReachExt.
Require Import WfUtil.
Require Import ListUtil2.
Require Import TransitionLabels.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Import CopyVal.
Require Coq.Vectors.Vector.
Require Import Assoc2.

Section greach.
Context {sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Hint Unfold Proper respectful impl.

Section reach_def.
Context (g:global_heap).

Inductive greachable_from : (place*val) -> (place*val) -> Prop :=
 | GRVRefl : forall p src, contains g p -> greachable_from (p,src) (p,src)
 | GRVStep : forall p q h src dest (ob:obj) (f:fname) mid, 
              g[@p]=Some h -> 
              h[@src] = Some ob -> 
              ob[@f] = Some mid -> 
              greachable_from (p,mid) (q,dest) -> 
              greachable_from (p,(Object src)) (q,dest)
 | GRVStepGlobal : forall p q r src dest,
              greachable_from (q,(Object src)) (r,dest) -> 
              greachable_from (p,(GlobalObject q src)) (r,dest).

Definition greachable_from_obj (src:place*obj) (dest:place*val) : Prop :=
  exists f mid, (snd src)[@f] = Some mid /\ greachable_from ((fst src),mid) dest.

Hint Unfold greachable_from_obj.
Hint Constructors greachable_from.
Hint Constructors PreOrder.
Hint Unfold Reflexive Transitive.

Global Instance greach_trans : Transitive greachable_from.
Proof. 
  - induction 1; dts idtac.
Qed.

Lemma greach_refl {p} v:
  contains g p ->
  greachable_from (p,v) (p,v).
Proof.
  eauto.
Qed.

Lemma some_contains {p h} : 
  g[@p] = Some h -> 
  contains g p.
Proof.
  red; eauto.
Qed.

Hint Resolve some_contains.

Lemma greach_contains_src {p o a} : greachable_from (p,Object o) a -> contains g p.
Proof.
  inversion 1; subst; eauto.
Qed.

Lemma GRVStep_simple : 
  forall p h src dest (ob:obj) (f:fname), 
    g[@p] = Some h ->
    h[@src] = Some ob -> 
    ob[@f] = Some dest -> 
    greachable_from (p,(Object src)) (p,dest).
Proof.
  intros.
  eauto.
Qed.

Lemma GRVStep_r :
  forall p q h src dest (ob:obj) (f:fname) mid, 
    greachable_from (p,src) (q,(Object mid)) -> 
    g[@q]=Some h ->
    h[@mid] = Some ob -> 
    ob[@f] = Some dest ->
    greachable_from (p,src) (q,dest).
Proof.
  dts idtac.
  intros. rewrite H. eauto.
Qed.

Global Instance greach_reach_obj : 
  Proper (eq ==> greachable_from ++> impl) greachable_from_obj.
Proof.
  dts idtac. destruct o0; simpl in *.
  inversion H; subst.
  econstructor; econstructor; split; [eauto|].
  etransitivity; eauto.
Qed.

Definition gacyclic_from p (v:val) 
  := forall q e, greachable_from (p,v) (q,e) -> 
                 greachable_from (q,e) (p,v) -> 
                 p = q /\ v = e.

Definition gacyclic := forall p v, gacyclic_from p v.

Hint Unfold gacyclic gacyclic_from.

Lemma gacylic_asym : 
  gacyclic -> 
  Antisymmetric (place*val) eq greachable_from.
Proof.
  dts idtac.
  red.
  intros [??] [??]; eauto.
  dts idtac.
  destruct (H _ _ _ _ H0 H1); subst; auto.
Qed.

Lemma greachable_from_to_obj {a b p q} : 
  greachable_from (p,a) (q,(Object b)) ->
  (exists c, a = Object c) \/ (exists c r, a = GlobalObject c r).
Proof.
  intros.
  destruct a; inversion H; subst; eauto.
Qed.

Lemma greachable_from_to_eqobj {a b p q}:
  greachable_from (p,a) (q,b) ->
  a = b \/ (exists c, a = Object c) \/ (exists c r, a = GlobalObject c r).
Proof.
  intros.
  destruct a; inversion H; subst; eauto.
Qed.

Lemma some_lookup_contains' {A B C:Type} `{Lookup A B (option C)} {h:A} {a:B} {c} : h[@a] = Some c -> contains h a.
Proof.
  unfold contains; eauto.
Qed.

Hint Resolve some_lookup_contains some_lookup_contains'.

Lemma greachable_from_contains_src {a b p q h}:
  (Object a) <> b -> 
  greachable_from (p,(Object a)) (q,b) ->
  g[@p] = Some h ->
  contains h a.
Proof.
  intros neq rf heq.
  inversion rf; subst; try congruence.
  rewrite H3 in heq; dt idtac.
  eapply some_lookup_contains'; eauto.
Qed.

End reach_def.

Hint Constructors greachable_from. 

Section wf.

Definition gwf_val (g:global_heap) p (v:val) := forall q oid,
	    greachable_from g (p,v) (q,(Object oid)) ->
            exists qh, g[@q] = Some qh /\ contains qh oid.

Definition gwf_obj (g:global_heap) p (o:obj) := forall q oid,
	    greachable_from_obj g (p,o) (q,(Object oid)) ->
            exists qh, g[@q] = Some qh /\ contains qh oid.

Definition gwf_heap (g:global_heap) p 
  := forall h, 
       g[@p] = Some h ->
       forall a, 
         contains h a -> 
         gwf_val g p (Object a).

Definition gwf_global_heap (g:global_heap) :=
  forall p, contains g p -> gwf_heap g p.

Definition gwf_global_heap_alt (g:global_heap) :=
  forall p h, 
    g[@p] = Some h -> 
    forall a,
      contains h a ->
      gwf_val g p (Object a).

Lemma gwf_global_heap_alt_equiv (g:global_heap) :
  gwf_global_heap g <-> gwf_global_heap_alt g.
Proof.
  unfold gwf_global_heap_alt, gwf_global_heap, gwf_heap; intuition; eauto.
  eapply H; eauto; eapply some_lookup_contains'; eauto.
Qed.

Definition gwf_vals g (l:list (place*val)) := forall p v, In (p,v) l -> gwf_val g p v.

Lemma gwf_vals_cons_eq {g p v l} :
    gwf_vals g ((p,v)::l) <-> (gwf_val g p v /\ gwf_vals g l).
Proof.
  unfold gwf_vals; simpl in *; intuition.
  inversion H2; subst; trivial.
Qed.

Lemma gwf_vals_app_eq {g l1 l2} :
    gwf_vals g (l1++l2) <-> (gwf_vals g l1 /\ gwf_vals g l2).
Proof.
  unfold gwf_vals; intuition.
  rewrite in_app_iff in *.
  intuition.
Qed.

Require Import List.

Lemma gwf_vals_singleton g p v :
  gwf_vals g (singleton (p,v)) <-> gwf_val g p v.
Proof.
  unfold gwf_vals, singleton; simpl; intuition.
  inversion H1; subst; auto.
Qed.

End wf.

Hint Resolve @wf_val_nat @wf_vals_nil.

Ltac simpwf := 
  repeat match goal with
           | [H:gwf_vals _ (_::_) |- _] => rewrite gwf_vals_cons_eq in H; destruct H
           | [H:gwf_vals _ (_ ++_) |- _] => rewrite gwf_vals_app_eq in H; destruct H
           | [H:gwf_vals _ (singleton _) |- _] => rewrite gwf_vals_singleton in H
           | [|- gwf_vals _ (_::_) ] => rewrite gwf_vals_cons_eq
           | [|- gwf_vals _ (_ ++_)] => rewrite gwf_vals_app_eq
           | [|- gwf_vals _ (singleton _) ] => rewrite gwf_vals_singleton

           | [H:wf_vals _ (_::_) |- _] => rewrite wf_vals_cons_eq in H; destruct H
           | [H:wf_vals _ (_ ++_) |- _] => rewrite wf_vals_app_eq in H; destruct H
           | [H:wf_vals _ (singleton _) |- _] => rewrite wf_vals_singleton in H
           | [|- wf_vals _ (_::_) ] => rewrite wf_vals_cons_eq
           | [|- wf_vals _ (_ ++_)] => rewrite wf_vals_app_eq
           | [|- wf_vals _ (singleton _) ] => rewrite wf_vals_singleton

           | [H: _ ++ _ = nil |- _ ] => apply app_eq_nil in H; destruct H
           | [H:Some _ = Some _ |- _ ] => inversion H; clear H; try subst
           | [H:?x = ?x |- _ ] => clear H
           | [H:?x = ?y, H1:?x = ?z |- _ ] => rewrite H in H1
           | [H:?x = ?y, H1:?z = ?x |- _ ] => rewrite H in H1
         end.


Section ghincl.
Definition ghincl (g1 g2:global_heap) 
      := forall p,
           match g1[@p], g2[@p] with
               | None, None => True
               | Some h1, Some h2 => hincl h1 h2
               | _, _ => False
           end.

Global Instance ghincl_pre : PreOrder ghincl.
unfold ghincl.
split; red; unfold hincl; intuition.
- destruct (x[@p]); auto.
- specialize (H p); specialize (H0 p).
  destruct (x[@p]); destruct (y[@p]); destruct (z[@p]); intuition.
Qed.

Lemma ghincl_some_f {g g' p h} :
  ghincl g g' ->
  g[@p] = Some h ->
  exists h', g'[@p] = Some h' /\ hincl h h'.
Proof.
  unfold ghincl; intros ginc geq.
  specialize (ginc p).
  rewrite geq in ginc.
  destruct (g'[@p]); intuition eauto.
Qed.

Lemma ghincl_some_b {g g' p h'} :
  ghincl g g' ->
  g'[@p] = Some h' ->
  exists h, g[@p] = Some h /\ hincl h h'.
Proof.
  unfold ghincl; intros ginc geq.
  specialize (ginc p).
  rewrite geq in ginc.
  destruct (g[@p]); intuition eauto.
Qed.

Lemma ghincl_contains_f {g g' p} :
  ghincl g g' ->
  contains g p ->
  contains g' p.
Proof.
  unfold contains.
  dt idtac.
  destruct (ghincl_some_f H H0).
  intuition eauto.
Qed.

Lemma ghincl_contains_b {g g' p} :
  ghincl g g' ->
  contains g' p ->
  contains g p.
Proof.
  unfold contains.
  dt idtac.
  destruct (ghincl_some_b H H0).
  intuition eauto.
Qed.

Hint Resolve ghincl_contains_f ghincl_contains_b.

Hint Resolve GRVStep_simple.
Lemma gwf_val_ghincl_reach_f {g g' p v} : 
  ghincl g g' -> 
  gwf_val g p v ->
  forall q oid, 
    greachable_from g (p,v) (q,(Object oid)) ->
    greachable_from g' (p,v) (q,(Object oid)).
Proof.
  Hint Constructors greachable_from.
  unfold gwf_val.
  intros.
  revert H0.
  dependent induction H1; simpl; intros.
  - eauto.
  - destruct (greachable_from_to_obj _ H2) as [[??]|[?[??]]]; subst. 
    + destruct (ghincl_some_f H H3) as [h' [geq' hincl]].
      transitivity (p, Object x); eauto.
    + destruct (ghincl_some_f H H3) as [h' [geq' hincl]].
      transitivity (p, (GlobalObject x x0)); eauto.
  - econstructor; eauto.
Qed.

Hint Resolve greach_refl some_contains.
Lemma gwf_val_ghincl_reach_b {g g' p v} : 
  ghincl g g' -> 
  gwf_val g p v ->
  forall q oid, 
    greachable_from g' (p,v) (q,(Object oid)) ->
    greachable_from g (p,v) (q,(Object oid)).
Proof.
  Hint Constructors greachable_from.
  unfold gwf_val.
  intros.
  revert H0.
  dependent induction H1; simpl; intros.
  - eauto.
  - destruct (greachable_from_to_obj _ H2) as [[??]|[?[??]]]; subst. 
    + destruct (ghincl_some_b H H3) as [h' [geq' hincl]].
      destruct (H4 p src) as [?[geq con]]; eauto.
      unfold place in *.
      rewrite geq in geq'; dt idtac.
      rewrite (hincl_back hincl con) in H0.
      eauto.
    + destruct (ghincl_some_b H H3) as [h' [geq' hincl]].
      destruct (H4 p src) as [?[geq con]]; eauto.
      unfold place in *;
      rewrite geq in geq'; dt idtac.
      rewrite (hincl_back hincl con) in H0.
      eauto.
   - eauto.
Qed.

Hint Resolve some_lookup_contains'.

Lemma gwf_val_greach {g p v q v'} :
  gwf_val g p v ->
  greachable_from g (p,v) (q,v') ->
  gwf_val g q v'.
Proof.
  unfold gwf_val.
  intros.
  apply H.
  etransitivity; eauto.
Qed.

Lemma gwf_val_ghincl_f {g g' p v} :
  ghincl g g' -> 
  gwf_val g p v ->
  gwf_val g' p v.
Proof.
  Hint Resolve hincl_contains gwf_val_greach.
  red; intros ginc gwf q oid gr.

  poses (gwf_val_ghincl_reach_b ginc gwf _ _ gr).
  destruct (gwf _ _ P) as [h[heq hc]].
  destruct (ghincl_some_f ginc heq) as [?[??]].
  eauto.
Qed.

Global Instance gwf_val_ghincl_proper : Proper (ghincl ==> eq ==> eq ==> impl) gwf_val.
Proof.
  Hint Resolve gwf_val_ghincl_f.
  dts idtac.
Qed.

Lemma gwf_vals_ghincl_f {g g' l} :
  ghincl g g' ->
  gwf_vals g l ->
  gwf_vals g' l.
Proof.
  Hint Resolve gwf_val_ghincl_f.
  unfold gwf_vals.
  induction l; simpl in *; eauto.
Qed.

Lemma gwf_vals_incl_f {g l l'} :
  gwf_vals g l ->
  incl l' l ->
  gwf_vals g l'.
Proof.
  unfold gwf_vals, incl; intuition.
Qed.

Global Instance gwf_vals_incl_proper : Proper (ghincl ==> (inverse (@incl _) )==> impl) gwf_vals.
Proof.
  Hint Resolve gwf_vals_ghincl_f gwf_vals_incl_f.
  dts idtac.
Qed.

Lemma hincl_update_ghincl {g p h h'} :
    g[@p] = Some h ->
    hincl h h' ->
    ghincl g g[p~~>Some h'].
Proof.
  unfold ghincl; intros.
  destruct (p == p0); unfold equiv, complement in *; subst.
  - rewrite H. rewrite lookup_update_eq; dt idtac.
  - rewrite lookup_update_neq; eauto.
    destruct (g[@p0]); intuition.
Qed.

Lemma gwf_vals_cons {g p v l} :
  gwf_val g p v ->
  gwf_vals g l ->
  gwf_vals g ((p,v)::l).
Proof.
  intros. rewrite gwf_vals_cons_eq; auto.
Qed.

End ghincl.
    
Lemma gwf_val_wrap {g p oid} :
    gwf_val g p (Object oid) ->
    gwf_val g p (GlobalObject p oid).
Proof.
  unfold gwf_val; intros.
  inversion H0; subst.
  eauto.
Qed.

Lemma gwf_val_step_o {g p h oid o} :
  g[@p] = Some h ->
  h[@oid] = Some o ->
  (forall f v, o[@f] = Some v -> gwf_val g p v) ->
  gwf_val g p (Object oid).
Proof.
  red; intros geq heq oeq q oid' gre.
  dependent induction gre.
  - unfold contains; eauto.
  - rewrite geq in H; inversion H; clear H; subst.
    rewrite heq in H0; inversion H0; clear H0; subst.
    poses (oeq _ _ H1).
    destruct (greachable_from_to_obj _ gre) as [[??]|[?[??]]]; subst; eauto.
Qed.

Lemma gwf_val_nat g p n : gwf_val g p (Nat n).
Proof.
  red; intros.
  inversion H.
Qed.

Lemma gwf_vals_nil p : gwf_vals p nil.
Proof.
  red; intuition.
Qed.

Lemma gwf_val_step_obj {g p oid h o} :
    gwf_val g p (Object oid) ->
    Some h = g[@p] ->
    h[@oid] = Some o ->
    gwf_obj g p o.
Proof.
  unfold gwf_obj, gwf_val, greachable_from_obj; intros.
  dts idtac.
Qed.

Lemma gwf_obj_step {g p h f o o'} :
  g[@p] = Some h ->
  gwf_obj g p o ->
  o[@f] = Some o' ->
  gwf_val g p o'.
Proof.
  Hint Constructors greachable_from.
  unfold gwf_obj, gwf_val, greachable_from_obj; intros.
  eauto. 
Qed.

Lemma gwf_val_step_gobject {g p q o} :
  contains g q ->
  gwf_val g p (GlobalObject q o) -> 
  gwf_val g q (Object o).
Proof.
  Hint Constructors greachable_from.
  unfold gwf_obj, gwf_val, greachable_from_obj; intros.
  eauto.
Qed.

Lemma gwf_obj_field_update {g p o f v} :
  gwf_obj g p o ->
  gwf_val g p v ->
  gwf_obj g p o[f~~>v].
Proof.
  unfold gwf_obj, greachable_from_obj; intros go gv q oid [f' [v' [??]]]; simpl in *.
  destruct (f == f'); unfold equiv, complement in *; subst.
  - poses (Assoc2.lookup_update1 H); subst; eauto.
  - unfold lookup, obj_lookup in *; destruct o; dt idtac. 
    poses (Assoc.lookup_update2 x _ _ v c).
    unfold lookup, Util.update in P. rewrite P in H.
    eauto.
Qed.

Lemma gwf_val_update {g p q h v o} {oid:oid} {pf} :
  g[@q] = Some h ->
  gwf_val g p v ->
  gwf_obj g q o ->
  gwf_val g[q~~>Some (update h oid pf o)] p v.
Proof.
  Hint Resolve gwf_obj_step gwf_val_step_obj.
  red;
  intros.
  dependent induction H2.
  - destruct (q == q0); unfold equiv, complement in *; subst.
    + unfold place. rewrite lookup_update_eq.
      eexists; intuition.
      eapply contains_update_strengthen. 
      edestruct H0; intuition.
      * eapply greach_refl; red; eauto.
      * rewrite H4 in H; dt idtac.
    + unfold place; rewrite lookup_update_neq; eauto 2.
      edestruct H0; intuition; eauto.
      eapply greach_refl.
      eapply contains_update_b; eauto; red; eauto.
  -  specialize (IHgreachable_from oid0 q0 oid o mid h pf q p g ).
     intuition.
     destruct (q == p); unfold equiv, complement in *; subst.
     + unfold place in H3; rewrite lookup_update_eq in H3.
       dt idtac.
       destruct (src == oid); unfold equiv, complement in *; subst.
       * rewrite Heap.lookup_update1 in H4.
         dt idtac. poses (gwf_obj_step H H1 H5).
         intuition.
       * rewrite lookup_update2 in H4; eauto.
     + unfold place in H3; rewrite lookup_update_neq in H3; eauto 2.
       poses (gwf_val_step_obj H0 (symmetry H3) H4).
       poses (gwf_obj_step H3 P H5). intuition.
  - assert (cg1: contains g q1)
     by (eapply contains_update_b; [red; eauto | eapply greach_contains_src; eauto]).

    poses (gwf_val_step_gobject cg1 H0).
    clear H0.
    eapply IHgreachable_from; eauto.
Qed.

Section reach.
Require Import Reachable.
Lemma reachable_greachable {g p h v v'} :
  g[@p] = Some h ->
  reachable_from h v v' ->
  greachable_from g (p,v) (p,v').
Proof.
  Hint Constructors greachable_from.
  intros.
  dependent induction H0; intuition eauto.
  eapply greach_refl; red; eauto.
Qed.

Lemma gwf_val_wf {g p h v} :
  g[@p] = Some h ->
  gwf_val g p v -> wf_val h v.
Proof.
  unfold gwf_val, wf_val.
  Hint Resolve reachable_greachable.
  intuition.
  destruct (H0 p oid); intuition; eauto.
  rewrite H in H3; dts idtac.
Qed.

Lemma greachable_split {g p h v q v'} :
  g[@p] = Some h ->
  greachable_from g (p,v) (q,v') ->
     (p = q /\ reachable_from h v v') 
  \/ (exists r mid, 
        reachable_from h v (GlobalObject r mid) 
     /\ greachable_from g (p,(GlobalObject r mid)) (q,v')).
Proof.
  Hint Constructors reachable_from.
  Hint Constructors greachable_from.
  intros.
  dependent induction H0; [intuition|..]; intros.
  - destruct (IHgreachable_from _ _ _ _ _ H3 (eq_refl _) (eq_refl _));
    rewrite H in H3; dt idtac; intuition eauto.
  - right. exists q0; exists src; intuition.
Qed.

End reach.

Lemma gwf_greachable {g p o q v} :
  gwf_val g p o ->
  greachable_from g (p,o) (q,v) ->
  gwf_val g q v.
Proof.
  unfold gwf_val in *; intros.
  eapply H; transitivity (q,v); eauto.
Qed.


Lemma copy_gwf_val {g p q ph qh o o' ph'} :
  Some ph = g[@p] ->
  Some qh = g[@q] ->
  Some (o', ph') = copy qh o ph ->
  gwf_val g q o ->
  gwf_val g[p~~>Some ph'] p o'.
Proof.
  intros; red; intros.
  symmetry in H1.
  poses (copy_spec_some _ _ _ _ _ H1).
  dt idtac.
  assert(phl:g[p~~>Some ph'][@p] = Some ph')
        by (unfold place; rewrite lookup_update_eq; trivial).
  destruct (greachable_split phl H3); dt idtac.
  - dt idtac.
    poses (copy_is_wf_dest _ H1).
    eexists; eauto.
  - symmetry in H0. poses (gwf_val_wf H0 H2).
    assert(rqh:reachable_from qh o (GlobalObject x0 x1)).
    + rewrite isIso_sym in H8; [|destruct H5; intuition]. 
      eapply (isIso_reach_global H8); eauto 2.
      rewrite <- inIso_val_sym; [trivial|destruct H5; intuition]. 
    + eapply reachable_greachable in rqh; eauto.
      poses (gwf_greachable H2 rqh).
      assert (gwf_val g[p~~>Some ph'] q (GlobalObject x0 x1))
             by (eapply gwf_val_ghincl_f; eauto; eapply hincl_update_ghincl; eauto).
      assert(gre':greachable_from g[p~~>Some ph'] (q, GlobalObject x0 x1)
          (q0, Object oid)); [|eauto].
      inversion H11; subst; eauto.
Qed.

Lemma gwf_vals_wf {g p h v} :
  g[@p] = Some h ->
  gwf_vals g (placed_vals p v) ->
  wf_vals h v.
Proof.
  Hint Resolve in_placed_vals gwf_val_wf.
  unfold gwf_vals, wf_vals.
  eauto.
Qed.

Lemma gwf_can_transCopy {b g p src λ} dest :
  gwf_vals g (ptrans_vals p λ ) ->
  g[@p]=Some src ->
  {λ':trans_type & {dest':heap |
    Some (λ', dest') = transCopy b src λ dest}}.
Proof.
  intros; eapply wf_can_transCopy.
  eapply gwf_vals_wf; eauto.
Qed.

Hint Resolve gwf_val_nat gwf_vals_nil.

Lemma copy_list_other_gwf_vals {g p q ph qh vs ph' vs'} :
  p <> q ->
   Some qh = g[@q] ->
   Some ph = g[@p] ->
   Some (vs', ph') = copy_list_other qh vs ph ->
   gwf_vals g (placed_vals q vs) ->
   gwf_vals g[p~~>Some ph'] (placed_vals p vs').
Proof.
  revert g p q ph qh ph' vs'.
  induction vs; intros g p q ph qh ph' vs'; intros; simpl in *; dt idtac.
  simpwf.
  symmetry in H0.
  destruct (wf_can_copy qh (gwf_val_wf H0 H3) ph) as [?[? eqb]].
  rewrite eqb in H2.
  destruct (wf_can_copy_list_other x0 (gwf_vals_wf H0 H4)) as [?[? eqc]].
  rewrite <- eqc in H2; inversion H2; clear H2; subst.
  simpl; simpwf. split.
  - assert (gwf_val g[p~~>Some x0] p x) 
      by (eapply copy_gwf_val; try eapply H3; eauto).
    eapply gwf_val_ghincl_f; eauto. 
    assert (ghi:ghincl g[p~~>Some x0] g[p~~>Some x0][p~~>Some x2]).
     (eapply hincl_update_ghincl; dts idtac).
    unfold place in ghi; rewrite update_update in ghi; trivial.
  -  rewrite <- (update_update g p (Some x0)).
     eapply IHvs; try eapply eqc; eauto 2.
     + unfold place; rewrite lookup_update_neq; eauto.
     + unfold place; rewrite lookup_update_eq; eauto.
     + eapply gwf_vals_ghincl_f; eauto.
       eapply hincl_update_ghincl; eauto.
Qed.

Lemma copy_list_same_gwf_vals {g q qh vs qh' vs'} :
   Some qh = g[@q] ->
   Some (vs', qh') = copy_list_same qh vs ->
   gwf_vals g (placed_vals q vs) ->
   gwf_vals g[q~~>Some qh'] (placed_vals q vs').
Proof.
  revert g q qh qh' vs'.
  induction vs; intros g q qh qh' vs'; intros; simpl in *; dt idtac.
  simpwf.
  symmetry in H.
  destruct (wf_can_copy qh (gwf_val_wf H H1) qh) as [?[? eqb]].
  rewrite eqb in H0.
  assert (lo:g[q~~>Some x0][@q] = Some x0)
    by (unfold place; rewrite lookup_update_eq; trivial).
  assert(gwf:gwf_vals g[q~~>Some x0] (placed_vals q vs))
    by (eapply gwf_vals_ghincl_f; eauto; eapply hincl_update_ghincl; eauto).

  destruct (wf_can_copy_list_same (gwf_vals_wf lo gwf)) as [?[? eqc]].
  rewrite <- eqc in H0; inversion H0; clear H0; subst.
  simpl; simpwf. split.
  - assert (gwf_val g[q~~>Some x0] q x) 
      by (eapply copy_gwf_val; try eapply H3; eauto).
    eapply gwf_val_ghincl_f; eauto. 
    assert (ghi:ghincl g[q~~>Some x0] g[q~~>Some x0][q~~>Some x2])
           by (eapply hincl_update_ghincl; dts idtac).
    unfold place in ghi; rewrite update_update in ghi; trivial.
  -  rewrite <- (update_update g q (Some x0)).
     eapply IHvs; try eapply eqc; eauto 2.
Qed.

Lemma copy_list_gwf_vals {g p q ph qh vs ph' vs'} :
   Some qh = g[@q] ->
   Some ph = g[@p] ->
   Some (vs', ph') = copy_list (q ==b p) qh vs ph ->
   gwf_vals g (placed_vals q vs) ->
   gwf_vals g[p~~>Some ph'] (placed_vals p vs').
Proof.
  Hint Resolve copy_list_same_gwf_vals copy_list_other_gwf_vals.
  case_eq (q ==b p); dt idtac; unfold equiv, complement in *; subst; eauto.
Qed.  

Lemma transCopy_gwf_vals {g p q ph qh λ ph' λ'} :
   Some qh = g[@q] ->
   Some ph = g[@p] ->
   Some (λ', ph') = transCopy (q ==b p) qh λ ph ->
   gwf_vals g (placed_vals q (trans_vals λ)) ->
   gwf_vals g[p~~>Some ph'] (placed_vals p (trans_vals λ')).
Proof.
  Hint Resolve copy_list_gwf_vals.
  unfold transCopy in *; intros.
  destruct λ; simpl in *; dt idtac; intuition;
  (case_eq (copy_list (q==b p) qh l ph); 
    [intros s eq| intros eq]; rewrite eq in *; dt idtac);
  symmetry in eq; eapply copy_list_gwf_vals; try eapply eq; eauto.
Qed.  

End greach.

Hint Resolve @some_lookup_contains'.
Hint Resolve @gwf_val_nat @gwf_vals_nil.

Hint Rewrite @gwf_vals_app_eq.

Ltac simpwf := 
  repeat match goal with
           | [H:gwf_vals _ (_::_) |- _] => rewrite gwf_vals_cons_eq in H; destruct H
           | [H:gwf_vals _ (_ ++_) |- _] => rewrite gwf_vals_app_eq in H; destruct H
           | [H:gwf_vals _ (singleton _) |- _] => rewrite gwf_vals_singleton in H
           | [|- gwf_vals _ (_::_) ] => rewrite gwf_vals_cons_eq
           | [|- gwf_vals _ (_ ++_)] => rewrite gwf_vals_app_eq
           | [|- gwf_vals _ (singleton _) ] => rewrite gwf_vals_singleton

           | [H:wf_vals _ (_::_) |- _] => rewrite wf_vals_cons_eq in H; destruct H
           | [H:wf_vals _ (_ ++_) |- _] => rewrite wf_vals_app_eq in H; destruct H
           | [H:wf_vals _ (singleton _) |- _] => rewrite wf_vals_singleton in H
           | [|- wf_vals _ (_::_) ] => rewrite wf_vals_cons_eq
           | [|- wf_vals _ (_ ++_)] => rewrite wf_vals_app_eq
           | [|- wf_vals _ (singleton _) ] => rewrite wf_vals_singleton

           | [H: _ ++ _ = nil |- _ ] => apply app_eq_nil in H; destruct H
           | [H:Some _ = Some _ |- _ ] => inversion H; clear H; try subst
           | [H:?x = ?x |- _ ] => clear H
           | [H:?x = ?y, H1:?x = ?z |- _ ] => rewrite H in H1
           | [H:?x = ?y, H1:?z = ?x |- _ ] => rewrite H in H1
         end.
 