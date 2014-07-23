(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Defines objects and the local and global heaps used in TX10 and Resilient X10 *)
Require Export Assoc.
Require Export Heap.
Require Export Value.
Require Import Eqdep_dec.

Require Import ListVector.

Section aux.
Context {sc:StaticConfig}.

Definition sbool {A B:Prop} (v:{A} + {B}) :=
  if v then true else false.

(* objects are association lists mapping field names to values, 
   where the field names are all distinct.
   Using (sbool NoDup_dec _ (domain l)) = true instead of the simpler (NoDup (domain l))
   ensures that proof irrelevance holds (without axioms) for the proof.  This allows us to
   prove that equality on objects is decidable.
 *)
Definition obj := { l:list (fname*val) | sbool (NoDup_dec fname_eqdec (domain l)) = true}.

Program Lemma obj_nodup (o:obj) : NoDup (domain o).
Proof.
  destruct o. unfold sbool in *; simpl in *.
  destruct (NoDup_dec fname_eqdec (domain x)); intuition.
Qed.

Program Definition build_obj (l:list(fname*val)) (pfnd:NoDup (domain l)) : obj
  := l.
Next Obligation.
destruct (NoDup_dec fname_eqdec (domain l)); simpl; intuition.
Qed.

Global Program Instance obj_eqdec : EqDec obj eq.
Next Obligation.
destruct x; destruct y.
destruct (x == x0).
- red in e1. subst.
  left. f_equal. 
  eapply UIP_dec.
  apply bool_dec.
- right; intro. inversion H; congruence.
Defined.

Lemma build_obj_pf_irrel l pf1 pf2 : build_obj l pf1 = build_obj l pf2.
Proof.
  unfold build_obj.
  f_equal. eapply UIP_dec. apply bool_dec.
Qed.

(* define Lookup for objects *)
Global Program Instance obj_lookup : Lookup obj fname (option val) := lookup_assoc.

Lemma obj_lookup_simpl : forall (o:obj) a, o[@a] = (proj1_sig o)[@a].
Proof.
  unfold lookup, obj_lookup; simpl; auto.
Qed.

Lemma sbool_nodup {l:list(fname*val)} : sbool (NoDup_dec fname_eqdec (domain l)) = true -> NoDup (domain l).
Proof.
unfold sbool.
destruct (NoDup_dec fname_eqdec (domain l)); intuition.
Qed.

Lemma nodup_sbool {l:list(fname*val)} :  NoDup (domain l) -> sbool (NoDup_dec fname_eqdec (domain l)) = true.
Proof.
unfold sbool.
destruct (NoDup_dec fname_eqdec (domain l)); intuition.
Qed.

(* define Update for objects *)
Global Program Instance obj_update : Update obj fname val := update_assoc.
Next Obligation.
apply nodup_sbool.
destruct x; simpl.
poses (update_domain x x0 x1). unfold Util.update in P.
rewrite P.
apply sbool_nodup; trivial.
Qed.

Ltac dobj := repeat match goal with
    | [H:obj |- _ ] => let nd := fresh "nd" in 
                       destruct H as [H nd]; simpl in *; 
                       (apply sbool_nodup in nd || poses (sbool_nodup nd))
  end.

Program Definition obj_nil : obj := nil.

Program Definition obj_cons f v (o:obj) (pf:~ In f (domain o)) : obj := build_obj ((f,v)::o) _.
Next Obligation.
  dobj; constructor; auto.
Qed.

Lemma obj_lookup_cons_eq : forall (l:obj) a b pf, (obj_cons a b l pf)[@a] = Some b.
Proof.
  unfold obj_cons, lookup, obj_lookup.
  intros; dobj; simpl.  
  destruct (@equiv_dec fname (@eq fname) (@eq_equivalence fname) oid_eqdec a a); try congruence.
Qed.

Hint Resolve obj_lookup_cons_eq.

Lemma obj_lookup_cons_neq : forall (l:obj) a b pf c, a <> c -> (obj_cons a b l pf)[@c] = l[@c].
Proof.
  unfold obj_cons, lookup, obj_lookup.
  intros; dobj; simpl.
  destruct (@equiv_dec fname (@eq fname) (@eq_equivalence fname) oid_eqdec c a); congruence.
Qed.

Lemma build_obj_inj l1 l2 pf1 pf2 : l1 = l2 -> build_obj l1 pf1 = build_obj l2 pf2.
Proof.
  intros; subst. apply build_obj_pf_irrel.
Qed.

(* We can now define an instance of the TX10 and Resilient X10 (local) heap, which maps 
   object identifiers to objects *)
Instance obj_heap : HEAP oid obj := mk_nat_heap obj.

End aux.

Ltac dobj := repeat match goal with
    | [H:obj |- _ ] => let nd := fresh "nd" in 
                       destruct H as [H nd]; simpl in *; 
                       (apply sbool_nodup in nd || poses (sbool_nodup nd))
  end.

Hint Rewrite @obj_lookup_simpl : rewrites.

(* Given our definition of local heaps, we can define the global heap *)
Section global.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

(* a global heap is a partial map from each place to its local heap.
   This is modeled by using a list with one element per place.  Each element is 
   an option type, modelling the partial nature of the map.
   If a place does not have a local heap, it is assigned None, otherwise
   it is assigned Some (the_local_heap). *)
Definition global_heap := list_vector (option heap) PLACES.

Lemma lookup_update_eq (g:global_heap) q a : (g[q~~>a])[@q] = a.
Proof.
  apply vector_lookup_replace_eq.
Qed.

Lemma lookup_update_neq (g:global_heap) p q a : p <> q -> (g[p~~>a])[@q] = g[@q].
Proof.
  apply vector_lookup_replace_neq.
Qed.

Lemma contains_update {g:global_heap} {q p h}: contains g q -> contains g[p~~>Some h] q.
Proof.
  unfold contains. destruct (p == q); unfold equiv in *; subst; intuition.
  - rewrite lookup_update_eq; eauto.
  - rewrite lookup_update_neq; eauto.
Qed.

Lemma contains_update_back {g:global_heap} {q p h}: contains g p -> contains g[p~~>Some h] q -> contains g q.
Proof.
  unfold contains. destruct (p == q); unfold equiv, complement in *; subst; intuition.
  rewrite lookup_update_neq in *; eauto.
Qed.

Lemma some_lookup_contains {A B C:Type} `{Lookup A B (option C)} {h:A} {a:B} {c} : Some c  = h[@a] -> contains h a.
Proof.
  unfold contains; eauto.
Qed.

End global.