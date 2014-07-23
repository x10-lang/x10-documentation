(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Defines lists with a known size. An alternative would be to use Coq.Vectors.Vector.
   In fact, an earlier version of this development did this, however proving required lemmas
   about the basic operations required on vectors was very difficult.
   This version instead uses a dependent pair of a list with a proof that is has the required    size.
   *)

Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.Peano_dec.
Require Import Eqdep_dec.
Require Import Arith.
Require Export Assoc.

(* defines a natural number guaranteed to be less than a given bound *)
Section BoundedNat.
  Definition bounded (BOUND:nat) := {n:nat | n < BOUND}.

(* From the Coq FAQ *)
Theorem K_nat :
  forall (x:nat) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
Proof.
intros; apply K_dec_set with (p := p).
apply eq_nat_dec.
assumption.
Qed.


Theorem eq_rect_eq_nat :
  forall (p:nat) (Q:nat->Type) (x:Q p) (h:p=p), x = eq_rect p Q x p h.
Proof.
intros; apply K_nat with (p := h); reflexivity.
Qed.

Scheme le_ind' := Induction for le Sort Prop.

Theorem le_uniqueness_proof {n m : nat} (p q : n <= m) : p = q.
Proof.
  revert p q.
induction p using le_ind'; intro q.
 replace (le_n n) with
  (eq_rect _ (fun n0 => n <= n0) (le_n n) _ (refl_equal n)).
 2:reflexivity.
  generalize (refl_equal n).
    pattern n at 2 4 6 10, q; case q; [intro | intros m l e].
     rewrite <- eq_rect_eq_nat; trivial.
     contradiction (le_Sn_n m); rewrite <- e; assumption.
 replace (le_S n m p) with
  (eq_rect _ (fun n0 => n <= n0) (le_S n m p) _ (refl_equal (S m))).
 2:reflexivity.
  generalize (refl_equal (S m)).
    pattern (S m) at 1 3 4 6, q; case q; [intro Heq | intros m0 l HeqS].
     contradiction (le_Sn_n m); rewrite Heq; assumption.
     injection HeqS; intro Heq; generalize l HeqS.
      rewrite <- Heq; intros; rewrite <- eq_rect_eq_nat.
      rewrite (IHp l0); reflexivity.
Qed.

Definition bounded_eqdec {BOUND} : EqDec (bounded BOUND) eq.
Proof.
  red; unfold equiv, complement in *; intros.
  destruct x as [x xlt]; destruct y as [y ylt].
  destruct (eq_nat_dec x y); subst.
  - left; rewrite (le_uniqueness_proof xlt ylt); trivial.
  - right; inversion 1; congruence.
Defined.

End BoundedNat.

Require Import Omega.
(* defines a list with a known size *)
Section ListVector.

Definition list_vector (A:Type) (BOUND:nat) := {l:list A | length l = BOUND}.

Context {A:Type}.

Program Fixpoint vector_lookup' (BOUND:nat) (l:list A) (llen:length l = BOUND) (n:nat) (nlt:n<BOUND)  : A
  := match n, l with
       | 0, nil => _       
       | 0, (x::_) => x
       | S m, nil => _       
       | S m, (_::ls) => match BOUND with
                           | 0 => _
                           | S b =>
                             vector_lookup' b ls _ m _ 
                         end
     end.
Next Obligation.
simpl in *; assert False; intuition.
Defined.
Next Obligation.
simpl in *; assert False; intuition.
Qed.
Next Obligation.
simpl in *; omega.
Qed.

(* since the index is known to be less than the size of the list, 
   this lookup operation is total *)
Global Instance vector_lookup {BOUND:nat} : Lookup (list_vector A BOUND) (bounded BOUND) A.
Proof.
  intros [g glen] [p plt].
  exact (vector_lookup' BOUND g glen p plt).
Defined.

Fixpoint list_replace (l:list A) (n:nat) (newA:A) : list A
  := match l with 
       | nil => nil
       | (x::ls) => match n with 
                        | 0 => newA::ls
                        | S m => x::(list_replace ls m newA)
                    end
     end.

Lemma list_replace_length l n newA : length (list_replace l n newA) = length l.
Proof.
  revert n.
  induction l; simpl; trivial.
  destruct n; simpl; auto.
Qed.

Global Instance vector_replace {BOUND:nat} : Update (list_vector A BOUND) (bounded BOUND) A .
Proof.
  intros [g glen] [p plt] newA.
  refine (exist _ (list_replace g p newA) _).
  rewrite list_replace_length; trivial.
Defined.

Lemma vector_lookup'_ext BOUND l llen1 n nlt1 llen2 nlt2 : 
  vector_lookup' BOUND l llen1 n nlt1 = vector_lookup' BOUND l llen2 n nlt2.
Proof.
  revert BOUND llen1 llen2 n nlt1 nlt2.
  induction l; destruct n; destruct BOUND; try solve[simpl in *; subst; intuition].
Qed.

Lemma vector_lookup'_nhead BOUND a l sllen n snlt llen nlt :
  vector_lookup' (S BOUND) (a::l) sllen (S n) snlt = vector_lookup' BOUND l llen n nlt.
Proof.
  simpl; apply vector_lookup'_ext.
Qed.

Lemma vector_lookup'_nth_err {BOUND:nat} (l:list A) (llen:length l = BOUND) (n:nat) (nlt:n<BOUND)  : nth_error l n = Some (vector_lookup' BOUND l llen n nlt). 
Proof.
  revert BOUND l llen nlt. 
  induction n; destruct l; intros; simpl in *; subst; simpl; intuition.
Qed.

Lemma vector_lookup_replace_eq {BOUND} (l:list_vector A BOUND) n (a:A) :
  vector_lookup (vector_replace l n a) n = a.
Proof.
  destruct l as [l llen].
  destruct n as [n nlt].
  simpl.
  revert l BOUND llen nlt.
  induction n; destruct l; intros; simpl in *; subst; simpl; intuition.
  assert (nlt':n < length l) by omega.
  poses (IHn l (length l) (eq_refl) nlt').
  etransitivity; try eassumption.
  eapply vector_lookup'_ext.
Qed.

Lemma some_eq {B:Type} {a b:B} : Some a = Some b -> a = b.
Proof.
  inversion 1; trivial.
Qed.

Lemma nth_error_list_replace_neq l n1 a n2 : n1 <> n2 -> nth_error (list_replace l n1 a) n2 = nth_error l n2.
Proof.
  revert n1 l; induction n2; simpl;
   destruct l; simpl; trivial;
    destruct n1; intuition.
Qed.

Lemma vector_lookup_replace_neq {BOUND} (l:list_vector A BOUND) n1 n2 (a:A) : n1 <> n2 ->
  vector_lookup (vector_replace l n1 a) n2 = vector_lookup l n2.
Proof.
  destruct l as [l llen].
  destruct n1 as [n1 nlt1].
  destruct n2 as [n2 nlt2].
  intros.
  apply some_eq; simpl.
  repeat rewrite <- vector_lookup'_nth_err.
  apply nth_error_list_replace_neq.
  intro; elim H; subst.
  assert (nlt1 = nlt2) by apply le_uniqueness_proof.
  congruence.
Qed.

End ListVector.