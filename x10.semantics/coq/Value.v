(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Defines the values used in TX10 and Resilient X10 *)
Require Import Util.

Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.Peano_dec.
Require Import Eqdep_dec.
Require Import Arith.

Require List.
Require Import ListVector.

Section val.

Context `{sc:StaticConfig}.

(* the type of a place: a natural number less than the total number of PLACES,
   which is specified via the StaticConfig *)
Definition place := bounded PLACES.
(* the type of variables.  We just use natural numbers *)
Definition var := nat.
(* the type of field names.  We just use natural numbers *)
Definition fname := nat.
(* The type of object identifiers (addresses in the heap) *)
Definition oid := nat.

(* equality is decidable for these types *)
Global Instance finplace_eqdec : EqDec place eq := (@bounded_eqdec PLACES).

Global Instance place_eqdec : EqDec place eq := @finplace_eqdec.
Global Instance var_eqdec : EqDec var eq := eq_nat_dec.
Global Instance fname_eqdec : EqDec fname eq := eq_nat_dec.
Global Instance oid_eqdec : EqDec oid eq := eq_nat_dec.

Inductive val : Set :=
   (* a (local) reference *)
  | Object : oid -> val
  (* a global reference *)
  | GlobalObject : place -> oid -> val
  (* natural numbers.  Other types could be easily added as well. *)
  | Nat : nat -> val.

(* equality on values is decidable (computable) *)
Global Instance val_eqdec : EqDec val eq.
Proof.
  Hint Resolve place_eqdec oid_eqdec fname_eqdec eq_nat_dec.
  red; unfold equiv, complement. 
  intros x y. 
  change ({x=y}+{x<>y}).
  decide equality.
  apply place_eqdec.
Defined.

Lemma place_eqb_eq (p:place) : p ==b p = true.
Proof. dts idtac. Qed.

Lemma oid_eqb_eq (p:oid) : p ==b p = true.
Proof. dts idtac. Qed.

Hint Rewrite place_eqb_eq oid_eqb_eq : rewrite_eqs.

End val.
