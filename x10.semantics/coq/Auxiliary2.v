(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Some generally useful lemmas.  Unlike Auxiliary, these can depend on CopyVal *)

Require Export Auxiliary.
Require Import Eqdep_dec.
Require Import Reachable.
Require Import ListUtil2.
Require Import TransitionLabels.
Require Import CopyVal.
Require Import Program.

Require Import ListVector.
Section aux.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

(* a list of size n, all with the same element *)
Fixpoint list_const {A:Type} (a:A) (len:nat) : list A :=
    match len with
      | 0 => nil
      | S len => a :: list_const a len
    end.

Lemma list_const_length {A:Type} (a:A) (n:nat) : length (list_const a n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Definition vector_const {A:Type} (a:A) (n:nat) : list_vector A n
  := exist _ _ (list_const_length a n).

Lemma const_nth {A:Type} (e:A) n a: vector_lookup (vector_const e n) a = e.
Proof.
  destruct a as [a alt]; simpl.
  revert n alt.
  dependent induction a; simpl; trivial;
    destruct n; simpl; intuition.
  assert (alt':a < n) by omega.
  specialize (IHa _ alt').
  etransitivity; try eassumption.
  apply vector_lookup'_ext.
Qed.

(* the global heap that is nowhere defined *)
Definition global_empty : global_heap := vector_const (Some empty) _.

Lemma global_empty_contains : forall p, contains global_empty p.
Proof.
  intros; exists empty.
  apply const_nth.
Qed.

Lemma contains_update_b {g:global_heap} {r h q} :
    contains g r ->
    contains g[r~~>Some h] q ->
    contains g q.
Proof.
  intros cg cgu.
  destruct (r == q); unfold equiv, complement in *; subst; eauto.
  red in cgu; rewrite lookup_update_neq in cgu; eauto.
Qed.

(* given a proof that g contains p, we can find an explicit witness heap that g maps p to. *)
Lemma contains_strengthen {g:global_heap} {p} : contains g p -> {h:heap | g[@p] = Some h}.
Proof.
  case_eq (g[@p]); intros; eauto.
  assert False; [|intuition]. 
  destruct H0; congruence.
Qed.

Lemma contains_all_strengthen {g:global_heap} : (forall p, contains g p) -> (forall p, {h:heap | g[@p] = Some h}).
Proof.
  intros.
  apply contains_strengthen; auto.
Qed.

Hint Rewrite lookup_update_eq : rewrites.

Lemma eq_nth_error_if {A:Type} {l1 l2:list A} : 
  (forall n, n < length l1 \/ n < length l2 -> nth_error l1 n = nth_error l2 n) -> l1 = l2.
Proof.
  revert l2.
  induction l1; destruct l2; simpl; intros; trivial.
  - specialize (H 0); simpl in H;
    cut (error = value a); simpl in *; [discriminate | apply H]; intuition omega.
  - specialize (H 0); simpl in H;
    cut (value a = error); simpl in *; [discriminate | apply H]; intuition omega.
  - f_equal.
    + specialize (H 0); simpl in H; intuition. apply some_eq; apply H0. 
      omega.
    + apply IHl1; intros x; specialize (H (S x)); simpl in H.
      intros; apply H. omega.
Qed.

Lemma vector_eq_nth_if {A:Type} {BOUND:nat} (l1 l2:list_vector A BOUND) :
      (forall n, vector_lookup l1 n = vector_lookup l2 n) -> l1 = l2.
Proof.
  intros eqs.
  destruct l1 as [l1 l1len]; destruct l2 as [l2 l2len].
  cut (l1 = l2); [(intros; subst; f_equal; apply UIP_refl)|].
  simpl in eqs.
  apply eq_nth_error_if; intros n nlts.
  assert (nlt : n < BOUND) by intuition.
  specialize (eqs (exist _ n nlt)).
  simpl in eqs.
  poses (f_equal Some eqs).
  repeat rewrite <- vector_lookup'_nth_err in P; trivial.
Qed.
Lemma update_same_eq {g:global_heap} {p h} :
  g[@p]=Some h ->
  g[p~~>Some h] = g.
Proof.
  intros.
  apply vector_eq_nth_if. 
  intros.
  subst.
  destruct (p == n); unfold equiv, complement in *; subst.
  - poses (lookup_update_eq g n (Some h)).
    unfold Util.lookup in *; congruence.
  - poses (lookup_update_neq g p n (Some h) c).
    unfold Util.lookup in *; congruence.
Qed.

Lemma contains_new h o :
  contains (fst (new h o)) (snd (new h o)).
Proof.
  poses (lookup_new1 h o).
  destruct (new h o).
  red; eauto.
Qed.

Lemma lookup_new h o :
  (fst (new h o))[@ snd (new h o)] = Some o.
Proof.
  poses (lookup_new1 h o).
  destruct (new h o); eauto.
Qed.  

Section wf.
(* lift wf_val to a list of values *)
Definition wf_vals h (l:list val) := forall v, In v l -> wf_val h v.

Lemma wf_vals_singleton h v :
  wf_vals h (singleton v) <-> wf_val h v.
Proof.
  unfold wf_vals, singleton; simpl; intuition.
  inversion H1; subst; auto.
Qed.

Lemma wf_vals_cons_eq {h l v} :
    wf_vals h (v::l) <-> (wf_val h v /\ wf_vals h l).
Proof.
  unfold wf_vals; simpl in *; intuition.
  inversion H2; subst; trivial.
Qed.

Lemma wf_vals_app_eq {h l1 l2} :
    wf_vals h (l1++l2) <-> (wf_vals h l1 /\ wf_vals h l2).
Proof.
  unfold wf_vals; intuition.
  rewrite in_app_iff in *.
  intuition.
Qed.

Lemma wf_val_nat h n : wf_val h (Nat n).
Proof.
  red; intros.
  inversion H.
Qed.

Lemma wf_vals_nil h : wf_vals h nil.
Proof.
  red; intuition.
Qed.

End wf.

Section copy.

Lemma copy_hincl {ph a rh v h} :
  copy ph a rh = Some (v, h) -> hincl rh h.
Proof.
 intros.
 destruct (copy_spec_some _ _ _ _ _ H); trivial.
Qed.

Lemma copy_list_other_hincl {ph l rh l' rh'} :
  Some (l', rh') = copy_list_other ph l rh ->
  hincl rh rh'.
Proof.
  Hint Resolve copy_hincl.
  revert rh l' rh'.
  induction l; simpl; dt idtac; intuition.
  case_eq (copy ph a rh); [intros p heq|intros heq]; rewrite heq in *; try discriminate.
  destruct p; simpl in *.
  case_eq (copy_list_other ph l h); [intros p' heq'|intros heq']; rewrite heq' in *; try discriminate.
  destruct p'; simpl in *. dt idtac.
  transitivity h; eauto.
Qed.

Lemma copy_list_same_hincl {rh l l' rh'} :
  Some (l', rh') = copy_list_same rh l ->
  hincl rh rh'.
Proof.
  Hint Resolve copy_hincl.
  revert rh l' rh'.
  induction l; simpl; dt idtac; intuition.
  case_eq (copy rh a rh); [intros p heq|intros heq]; rewrite heq in *; try discriminate.
  destruct p; simpl in *.
  case_eq (copy_list_same h l); [intros p' heq'|intros heq']; rewrite heq' in *; try discriminate.
  destruct p'; simpl in *. dt idtac.
  transitivity h; eauto.
Qed.

Lemma copy_list_hincl {b ph l rh l' rh'} :
  Some (l', rh') = copy_list b ph l rh ->
  hincl (if b then ph else rh) rh'.
Proof.
  Hint Resolve copy_list_same_hincl copy_list_other_hincl.
  destruct b; eauto.
Qed.

Lemma transCopy_hincl {b ph λ rh λ' rh'} :
      Some (λ', rh') = transCopy b ph λ rh ->
        hincl (if b then ph else rh) rh'.
Proof.
  Hint Resolve copy_list_hincl.
  intros.
  destruct λ; simpl; dt idtac; intuition; unfold copy_list in *; destruct b.
    - case_eq (copy_list_same ph l); [intros p heq|intros heq]; rewrite heq in *; try discriminate.
     destruct p; dts idtac.
  -  case_eq (copy_list_other ph l rh); [intros p heq|intros heq]; rewrite heq in *; try discriminate.
     destruct p; dts idtac.
  -  case_eq (copy_list_same ph l); [intros p heq|intros heq]; rewrite heq in *; try discriminate.
     destruct p; dts idtac.
  -  case_eq (copy_list_other ph l rh); [intros p heq|intros heq]; rewrite heq in *; try discriminate.
     destruct p; dts idtac.
Qed.


Ltac simpwf := 
  repeat match goal with
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


Lemma transCopy_hincl_eqs {g:global_heap} {p q:place} {rh ph λ λ' rh'} :
      Some (λ', rh') = transCopy (p ==b q) ph λ rh ->
      Some ph = g[@p] ->
      Some rh = g[@q] ->
      hincl rh rh'.
Proof.
  intros.
  poses (transCopy_hincl H).
  case_eq (p ==b q); intros eqq; rewrite eqq in *;
  dt idtac.
  unfold equiv in *; subst.
  rewrite <- H0 in H1; simpwf; trivial.
Qed.


Lemma wf_can_copy_strong {src v}:
  wf_val src v ->
  forall dest_heap,  
    {v': val & {h':heap | copy src v dest_heap = Some (v',h')}}.
Proof.
  intros.
  case_eq (copy src v dest_heap); dts idtac.
  apply copy_spec_none in H0.
  assert False; dts idtac.
Qed.  

Lemma wf_can_copy_list_other {src vs} dest :
  wf_vals src vs ->
  {vs':list val & {dest':heap |
    Some (vs', dest') = copy_list_other src vs dest}}.
Proof.
  revert dest.
  induction vs; simpl; eauto; intros.
  rewrite wf_vals_cons_eq in H; destruct H.
  
  destruct (wf_can_copy_strong H dest) as [?[? eqc]].
  rewrite eqc.
  destruct (IHvs x0 H0) as [?[? eqcl]].
  rewrite <- eqcl.
  eauto.
Qed.

Lemma copy_preserves_wf_vals : forall {src dest_heap v v' h'},
                         copy src v dest_heap = Some (v',h')
                         -> forall {a}, wf_vals dest_heap a
                                     -> wf_vals  h' a.
Proof.
  Hint Resolve copy_preserves_wd.
  unfold wf_vals; eauto.
Qed.

Lemma wf_can_copy_list_same {src vs} :
  wf_vals src vs ->
  {vs':list val & {dest':heap |
    Some (vs', dest') = copy_list_same src vs}}.
Proof.
  revert src.
  induction vs; simpl; eauto; intros.
  rewrite wf_vals_cons_eq in H; destruct H.
  
  destruct (wf_can_copy_strong H src) as [?[? eqc]].
  rewrite eqc.
  
  poses (copy_preserves_wf_vals eqc H0).
  destruct (IHvs x0 P) as [?[? eqcl]].
  rewrite <- eqcl.
  eauto.
Qed.

Lemma wf_can_copy_list b {src vs} dest :
  wf_vals src vs ->
  {vs':list val & {dest':heap |
    Some (vs', dest') = copy_list b src vs dest}}.
Proof.
  Hint Resolve wf_can_copy_list_other wf_can_copy_list_same.
  destruct b; simpl; eauto.
Qed.


Lemma wf_can_transCopy b {src λ} dest :
  wf_vals src (trans_vals λ) ->
  {λ':trans_type & {dest':heap |
    Some (λ', dest') = transCopy b src λ dest}}.
Proof.
  destruct λ; simpl in *; eauto; intros;
  destruct (wf_can_copy_list b dest H) as [?[? eqc]];
  rewrite <- eqc; eauto.
Qed.

Lemma list_replace_replace {A:Type} (g:list A) q a b :
  list_replace (list_replace g q a) q b = list_replace g q b.
Proof.
  revert q; induction g; simpl; trivial.
  destruct q; simpl; congruence.
Qed.
Require Import Coq.Arith.Peano_dec.

Lemma list_vector_ext {A:Type} {BOUND:nat} x y P1 P2 : x = y -> exist (fun l : list A => length l = BOUND) x P1 = exist (fun l : list A => length l = BOUND) y P2.
Proof.
  intros. subst.
  f_equal. apply UIP_dec.
  apply eq_nat_dec.
Qed.

Lemma vector_replace_replace {A} {BOUND:nat} (g:list_vector A BOUND) q (a b:A) :
  vector_replace (vector_replace g q a) q b = vector_replace g q b.
Proof.
  destruct q as [q qlt].
  destruct g as [g glen].
  simpl.
  apply list_vector_ext.
  apply list_replace_replace.
Qed.

Lemma update_update (g:global_heap) q a b : g[q~~>a][q~~>b] = g[q~~>b].
Proof.
  apply vector_replace_replace.
Qed.

End copy.

End aux.
Hint Rewrite @lookup_update_eq : rewrites.
Hint Resolve @wf_val_nat @wf_vals_nil.

Hint Resolve @copy_hincl @copy_list_same_hincl @copy_list_other_hincl.