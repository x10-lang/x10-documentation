(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Defines a Heap structure, which will be used to to model a local heap in our semantics. *)
Require Export Util.

Require Import Coq.Logic.Eqdep_dec.

Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Gt.

Require Import Assoc.

Definition contains {A B C:Type} `{Lookup A B (option C)} (h:A) (a:B)
  := exists v, h[@a] = Some v.

(* Defines what a HEAP is *)
Class HEAP (addr:Type) `{@EqDec addr eq (@eq_equivalence addr)} (val:Type) := 
  { heap : Type;
    empty : heap;
    heap_lookup :> Lookup heap addr (option val);
    update : forall (h:heap) (a:addr), contains h a -> val -> heap;
    new : heap -> val -> heap*addr;

    lookup_empty : forall a, lookup empty a = None;
    lookup_update1 : forall h a p v, (update h a p v)[@a] = Some v;
    lookup_update2 : forall h a1 p v a2, a1 <> a2 -> (update h a1 p v)[@a2] = lookup h a2;

    new_fresh : forall h v, let '(_,a):=new h v in h[@a] = None;
    lookup_new1 : forall h v, let '(h',a):=new h v in h'[@a] = Some v;
    lookup_new2 : forall h v, let '(h',a'):=new h v in forall a, a <> a' -> h'[@a] = h[@a];

    (* This can be used to obtain the domain of the keap, 
       which is important for reasoning about the heap. *)
    dom : heap -> list addr;
    
    dom_nodup : forall h, NoDup (dom h);
    dom_lookup : forall h a, In a (dom h) <-> contains h a;

    (* much simpler then dealing with equivalence/setoid relations *)
    extensionality : forall h h', (forall a, lookup h a = lookup h' a) -> h = h'
  }.

Opaque heap empty heap_lookup update new dom.

Section MakeHeap.
(* Given a key type with decidable equality, a decidable strict order, 
   and a way to create a new address larger than any given address, 
   we can construct a HEAP instance *)
  Context (addr:Type) {addr_eqdec:@EqDec addr eq (@eq_equivalence addr)} (val:Type).
  Context (gt:addr -> addr -> Prop).
  Context (gt_dec : forall (a1 a2:addr), {gt a1 a2} + {~ gt a1 a2}).
  
  Context {gt_order : StrictOrder gt}.
  Context (addr_zero : addr).
  Context (addr_succ : forall (a:addr), {sa:addr | gt sa a}).

  Existing Instance addr_eqdec.
  Existing Instance gt_order.

  Hint Resolve gt_order.

  Ltac tac :=
  repeat progress (match goal with 
    | [H: ?a = S ?a |- _ ] => elim (n_Sn _ H)
    | [H: S ?a = ?a |- _ ] => elim (n_Sn _ (symmetry H))
    | [H:?X = ?X |- _ ] => clear H
    | [H: gt ?X ?X |- _] => elim (irreflexivity H)
    | [H: ex _ |- _ ] => destruct H
    | [H:context [(addr_succ ?a)] |- _] => destruct (addr_succ a); simpl in H
    | [|- context [(addr_succ ?a)]] => destruct (addr_succ a); simpl
    | [H: context [gt_dec ?a ?n] |-_ ] => destruct (gt_dec a n); subst; try congruence
    | [|- context [gt_dec ?a ?n]] => destruct (gt_dec a n); subst; try congruence

    | [H: prod _ _ |- _] => destruct H
    | [H: ?X _ = ?X _  |- _] => inversion_clear H
    | [H: _ /\ _ |- _] => destruct H
    | [H:context [(addr_eqdec ?X ?Y)] |- _] => destruct (addr_eqdec X Y); unfold equiv, complement in *; try subst; try congruence
    | [|- context [(addr_eqdec ?X ?Y)]] => destruct (addr_eqdec X Y);  unfold equiv, complement in *; try subst; try congruence
    | [H:context [(addr_eqdec  ?X ?Y)] |- _] => destruct (addr_eqdec X Y); unfold equiv, complement in *; try subst; try congruence
    | [|- context [(addr_eqdec ?X ?Y)]] => destruct (addr_eqdec X Y);  unfold equiv, complement in *; try subst; try congruence
    end; intros; simpl in *; trivial).

  Program Definition new_ (l:list (addr*val)) (v:val) : list (addr*val)*addr
    := match l with 
         | nil => ((addr_zero,v)::nil,addr_zero)
         | ((a,_)::ls) =>
           ((addr_succ a,v)::l,addr_succ a)
       end.

  Program Instance mk_heap : HEAP addr val := {
  (* our heap will be built using a sorted functional assocation lists *)
    heap := {l : list (addr * val) | sorted_nd_domain gt_dec l = true};
    empty := nil;
    heap_lookup h v := (proj1_sig h)[@v];
    dom h := domain h;
    new h v := new_ h v;
    update  h a pf v  := (proj1_sig h)[a~~>v]
    }.
  Next Obligation.
    unfold new_, sorted_nd_domain in *; destruct h; simpl; trivial.
    rewrite update_domain; trivial.
  Qed.    
  Next Obligation.
    unfold new_, sorted_nd_domain in *; destruct h; simpl; trivial.
    tac.
  Qed.
  Next Obligation.
    destruct p; simpl in *.
    eapply Assoc.lookup_update1.
    eexact e.
  Qed.
  Next Obligation.
    destruct p; simpl in *.
    eapply Assoc.lookup_update2; eauto.
  Qed.
  Next Obligation.
    destruct h; simpl; try reflexivity.
    apply Forall_gt_nodup; simpl.
    unfold sorted_nd_domain in *.
    apply sorted_StronglySorted in H; auto.
    tac.
    inversion H; subst; simpl.
    constructor; auto.
    eapply Forall_impl; [|eauto].
    intros; eapply transitivity; eauto.
Qed.
Next Obligation.
  destruct h; compute; tac.
Qed.
Next Obligation. 
  destruct h; compute; tac; try congruence.
Qed.
Next Obligation.
  unfold sorted_nd_domain in *.
  eapply sorted_nd_NoDup; eauto.
Qed.
Next Obligation.
  unfold contains. unfold sorted_nd_domain in *.
  unfold lookup; simpl.
  rewrite sorted_StronglySorted in H; auto.
  induction h; simpl; split; intros; try solve [intuition]; simpl in *; tac; try (discriminate || eauto); inversion H; subst.
  - destruct H0. 
    + eexists; compute; tac.
    + destruct (IHh H3); destruct (H1 H0).
      exists x. unfold equiv_dec; tac.
      poses (Forall_gt_nodup H4).
      unfold lookup in *; congruence.
  - unfold equiv_dec in *; tac; try solve[intuition].
    destruct (IHh H3). right; apply H2. eauto.
Qed.
Next Obligation.
  unfold lookup in *; simpl in *.
  cut (h = h'); intros.
    subst. f_equal; auto. apply sorted_nd_ext.
  eapply extensionality_; eauto. 
Qed.

End MakeHeap.

(* Various derived properties of heap operations *)
Section heap_props.
Context {addr val} {addr_eqdec:@EqDec addr eq (@eq_equivalence addr)} `{Heap:@HEAP addr addr_eqdec val}.
Existing Instance Heap.
Existing Instance addr_eqdec.

Lemma lookup_dec : forall h a, {o : val | lookup h a = Some o} + {lookup h a = None}.
Proof.
intros; destruct (lookup h a); eauto.
Qed.

Lemma contains_dec : forall h a, {contains h a} + {~ (contains h a)}.
unfold contains; intros. destruct (lookup_dec h a). 
  destruct s; eauto. 
  right; intros [??]. congruence.
Qed.

Lemma dom_lookup1 : forall h a, In a (dom h) -> exists v, lookup h a = Some v.
Proof.
  intros; apply dom_lookup; auto.
Qed.

Lemma dom_lookup2 : forall h a v, lookup h a = Some v -> In a (dom h).
Proof.
  intros; apply dom_lookup; red; eauto.
Qed.

Hint Resolve dom_lookup1 dom_lookup2.

Lemma lookup_new_preserves : forall h v a, contains h a -> let '(h',a'):=new h v in lookup h' a = lookup h a.
Proof.
  unfold contains; intros. generalize (lookup_new2 h v); intro.
  case_eq (new h v); intros; rewrite H1 in *.
  destruct (a == a0); subst; auto.
  generalize (new_fresh h v); intros.
  rewrite H1 in *.  
  destruct H.
  congruence.
Qed.

Lemma update_update1 : forall h a p1 v1 p2 v2, update (update h a p1 v1) a p2 v2 = (update h a p1 v2).
Proof.
  unfold contains; intros; apply extensionality; intros.
  destruct (a == a0); unfold complement, equiv in *; subst.
    repeat rewrite lookup_update1; trivial.
    repeat rewrite lookup_update2; trivial.
Qed.

Lemma contains_update_strengthen : forall {h a} a1 p1 v1, contains h a -> contains (update h a1 p1 v1) a.
Proof.
unfold contains; intros.
destruct (equiv_dec a a1); unfold equiv, complement in *; subst;
  [rewrite lookup_update1 | rewrite lookup_update2]; eauto.
Qed.

Lemma contains_update_weaken : forall {h a a1 p1 v1}, contains (update h a1 p1 v1) a -> contains h a.
Proof.
unfold contains; intros.
destruct (equiv_dec a a1); unfold equiv, complement in *; subst; trivial.
rewrite lookup_update2 in H; auto.
Qed.

Lemma update_update2 : forall h a1 p1 v1 a2 p2 v2, a1 <> a2 -> update (update h a1 p1 v1) a2 p2 v2 = update (update h a2 (contains_update_weaken p2) v2) a1 (contains_update_strengthen a2 (contains_update_weaken p2) v2 p1) v1.
Proof.
  intros; apply extensionality; intros.
  destruct (a == a1); unfold complement, equiv in *; subst.
    repeat rewrite lookup_update1; rewrite lookup_update2;
      try repeat rewrite lookup_update1; auto.
  destruct (a == a2); unfold complement, equiv in *; subst.
    repeat rewrite lookup_update1; rewrite lookup_update2;
      try repeat rewrite lookup_update1; auto.
    repeat rewrite lookup_update2; auto.
Qed.

Lemma update_proof_irrelevance : forall (h:heap) (a:addr) p1 p2 v, update h a p1 v = update h a p2 v.
Proof.
  intros.
  apply extensionality. 
  intros.
  destruct (a == a0); unfold complement, equiv in *; subst;
  [ repeat rewrite lookup_update1 | repeat rewrite lookup_update2]; auto.
Qed.

Lemma dom_empty : dom empty = nil.
Proof.
  cut (forall l, dom empty = l -> l = nil); [auto|].
  induction l; trivial.
  intros.
    generalize (dom_lookup empty a).
    unfold contains in *.
    rewrite H; intros [F _].
    generalize (lookup_empty a); intros.
    assert (HI : In a (a :: l)); [intuition|].
    destruct (F HI).
    congruence.
Qed.

Lemma dom_update h a p v : Permutation (dom (update h a p v)) (dom h).
Proof.
  intros.
  apply NoDup_Permutation; try apply dom_nodup.
  intros.
  repeat rewrite dom_lookup.
  Hint Resolve contains_update_strengthen contains_update_weaken.
  intuition eauto.
Qed.

Definition hincl (h1 h2:heap) := forall {x:addr} {v:val}, h1[@x] = Some v -> h2[@x] = Some v.

Global Instance hincl_pre : PreOrder hincl.
split; red; unfold hincl; intuition.
Defined.

Lemma hincl_dom_incl {h1 h2:heap} : hincl h1 h2 -> incl (dom h1) (dom h2).
Proof.
  unfold hincl, incl; intros hi a ina.
  apply dom_lookup in ina.
  destruct ina.
  apply dom_lookup.
  eexists; eauto.
Qed.

Lemma hincl_contains {h1 h2:heap} {x} : hincl h1 h2 -> contains h1 x -> contains h2 x.
Proof.
  unfold hincl, contains. 
  intros hi [? ?]; eauto.
Qed.

Lemma hincl_new : forall h v, hincl h (fst (new h v)).
Proof.
  unfold hincl; intros h v x v' lx.
  poses (new_fresh h v); poses (lookup_new1 h v); poses (lookup_new2 h v);
    destruct (new h v); simpl; intros.
  destruct (a == x); unfold equiv, complement in *; subst.
  congruence.
  rewrite P1; eauto.
Qed.

Lemma hincl_update_inv {h v pf x} : hincl h (update h v pf x) -> h[@v] = Some x.
Proof.
  intros.
  destruct pf.
  poses (H _ _ e).
  rewrite lookup_update1 in P.
  congruence.
Qed.

Lemma hincl_inv {h1 h2 x} : hincl h1 h2 -> h2[@x] = None -> h1[@x] = None.
Proof.
  intros H ln.
  poses (H x).
  destruct (h1[@x]); trivial.
  erewrite P in ln; eauto.
Qed.

Lemma hincl_back {h1 h2 x} : hincl h1 h2 -> contains h1 x -> h2[@x] = h1[@x].
Proof.
  unfold contains.
  intros hi [??].
  specialize (hi x).
  destruct (lookup h1 x); [eauto|congruence].
Qed.

Lemma hincl_update_fresh {h1 h2 v} pf x : h1[@v] = None -> 
                                          hincl h1 h2 ->
                                          hincl h1 (update h2 v pf x).
Proof.
  unfold hincl; intros.
  destruct (x0 == v); unfold equiv, complement in *; subst.
  - congruence.
  - rewrite lookup_update2; auto.
Qed.

Lemma hincl_update {h1 h2} v pf1 pf2 x : hincl h1 h2 -> hincl (update h1 v pf1 x) (update h2 v pf2 x).
Proof.
  unfold hincl; intros.
  destruct (v == x0); unfold equiv, complement in *; subst.
  - rewrite lookup_update1 in H0 |- *; auto.
  - rewrite lookup_update2 in H0 |- *; auto.
Qed.

Lemma hincl_incl {h1 h2 a}: 
  hincl h1 h2 ->
  incl a (dom h1)
  -> incl a (dom h2).
Proof.
  intros.
  rewrite <- (hincl_dom_incl H); trivial.
Qed.


End heap_props.

(* nats have the required operations to be keys for our heap implementation *)
Section nat_heap.

Context (val:Type).

Instance gt_order : StrictOrder gt.
unfold gt; split; repeat red; [apply gt_irrefl|apply gt_trans].
Qed.

Program Definition addr_succ : forall (a:nat), {sa:nat | gt sa a} := S.

Instance mk_nat_heap : HEAP nat val
  := @mk_heap nat nat_eq_eqdec val gt gt_dec gt_order 0 addr_succ.

End nat_heap.

Ltac dnew := match goal with 
    [H: (_, _) = new ?h ?v |- _ ] =>
    poses (new_fresh h v);
    poses (lookup_new1 h v);
    poses (lookup_new2 h v);
    poses (hincl_new h v);
    destruct (new h v);
    inversion H; clear H; try subst; simpl in *
end.

Ltac dupdate_pf := 
  match goal with
    | [|- context [update ?h ?o ?p ?v]] => generalize p; intros
  end.
