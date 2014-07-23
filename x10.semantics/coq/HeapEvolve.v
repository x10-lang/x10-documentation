(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Definition and properties of heap evolution.  A heap x is said to evolve into heap y if all addresses in x are also in y.  
   Unlike heap inclusion (hincl), this does not require that the corresponding values agree *)
Require Import Program.
Require Import Eqdep_dec.
Require Import Auxiliary2.
Require Import GloballyReachable.
Require Import Util.
Require Import CopyVal.
Require Import TransitionLabels.

Section hevolve.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Definition hevolve (h1 h2:heap) := forall x, contains h1 x -> contains h2 x.

Lemma hevolve_dom {h1 h2} : hevolve h1 h2 -> incl (dom h1) (dom h2).
Proof.
  unfold hevolve, incl; intros.
  apply dom_lookup in H0.
  apply dom_lookup.
  auto.
Qed.

Global Instance hevolve_pre : PreOrder hevolve.
Proof.
  unfold hevolve; constructor; red; intros; eauto.
Qed.

Definition gevolve (g1 g2:global_heap) 
      := forall p,
           match g1[@p], g2[@p] with
               | None, None => True
               | Some h1, Some h2 => hevolve h1 h2
               | _, _ => False
           end.

Global Instance gevolve_pre : PreOrder gevolve.
Proof.
  unfold gevolve; constructor; red; intros.
  - destruct (x[@p]); auto. reflexivity.
  - specialize (H p).
    specialize (H0 p).
    destruct (x[@p]); destruct (y[@p]); destruct (z[@p]); intuition eauto.
    etransitivity; eauto.
Qed.

Lemma hincl_hevolve {h1 h2} : hincl h1 h2 -> hevolve h1 h2.
Proof.
  red; intros.
  eapply hincl_contains; eauto.
Qed.

Lemma ghincl_gevolves {g g'} :
  ghincl g g' -> 
  gevolve g g'.
Proof.
  Hint Resolve hincl_hevolve.
  unfold ghincl, gevolve; intros ghi p.
  specialize (ghi p).
  destruct g[@p]; destruct g'[@p]; eauto.
Qed.

Lemma gevolve_update {g p h h'} :
  g[@p] = Some h ->
  hevolve h h' ->
  gevolve g g[p~~>Some h'].
Proof.
  red; intros.
  destruct (p==p0); unfold equiv, complement in *; subst.
  - rewrite H. rewrite lookup_update_eq; auto.
  - repeat rewrite lookup_update_neq; auto.
    destruct (g[@p0]); intuition.
Qed.

Lemma hevolve_update h oid pf o : hevolve h (Heap.update h oid pf o).
Proof.
  intros ? ?.
  apply contains_update_strengthen; auto.
Qed.

Lemma copy_hevolve {ph v rh v' rh'} :
  Some (v', rh') = copy ph v rh ->
  hevolve rh rh'.
Proof.
  Hint Resolve hincl_hevolve copy_hincl.
  eauto.
Qed.

Lemma transCopy_hevolve {b ph λ rh λ' rh'} :
  Some (λ', rh') = transCopy b ph λ rh ->
  hevolve (if b then ph else rh) rh'.
Proof.
  Hint Resolve transCopy_hincl hincl_hevolve.
  eauto.
Qed.

Lemma transCopy_hevolve_eqs {g:global_heap} {p q:place} {rh ph λ λ' rh'} :
      Some (λ', rh') = transCopy (p ==b q) ph λ rh ->
      Some ph = g[@p] ->
      Some rh = g[@q] ->
      hevolve rh rh'.
Proof.
  Hint Resolve transCopy_hincl_eqs hincl_hevolve.
  eauto.
Qed.

End hevolve.