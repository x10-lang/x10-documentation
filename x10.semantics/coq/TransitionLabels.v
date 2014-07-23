(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Defines transition labels and operations on them. *)
Require Import Util.
Require Export Value.
Require Export Auxiliary.
Require Import CopyVal.

Section trans_labels.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

(* transition labels *)
(* Note that, unlike the paper version, we allow arbitrary values to be embedded in 
   exception labels. This complicates the development, and forces us to formalize 
   copying them between heaps. *)
Inductive trans_type :=
  | ε : trans_type
  | SyncFail : list val -> trans_type
  | AsyncFail : list val -> trans_type.

Global Instance trans_type_dec : EqDec trans_type eq.
red; unfold equiv, complement; intros.
fold (not (x=y)).
decide equality;
apply list_eq_dec; apply val_eqdec.
Qed.

Notation "⊗" := SyncFail.
Notation "×" := AsyncFail.

Definition toAsyncTrans (λ:trans_type) :=
  match λ with
    | ε => ε
    | SyncFail v => × v
    | AsyncFail v => × v
  end.

Definition toSyncTrans (λ:trans_type) :=
  match λ with
    | ε => ε
    | SyncFail v => ⊗ v
    | AsyncFail v => ⊗ v
  end.

Definition asSyncTrans (μ:list val) :=
  match μ with
      | nil => ε
      | _ => ⊗ μ
  end.

Definition vals_plus_trans_type (μ:list val) (λ:trans_type)
  := match λ with
         | ε => μ
         | SyncFail v => v++μ
         | AsyncFail v => v++μ
     end.

Definition isSyncTrans (λ:trans_type) : bool :=
  match λ with
    | ε => false
    | SyncFail v => true
    | AsyncFail v => false
  end.

Lemma toAsyncTrans_sync {λ v} : toAsyncTrans λ <> ⊗ v.
Proof. destruct λ; simpl; congruence. Qed.

(* copying a list of values from one heap to another *)
Fixpoint copy_list_other (source:heap) (vs:list val) (dest:heap) : option (list val*heap)
  := match vs with
         | nil => Some (nil, dest)
         | v::vss => 
           match copy source v dest with
             | None => None 
             | Some (v',dest') => 
                 match copy_list_other source vss dest' with
                     | None => None
                     | Some (vss',dest'') => Some (v'::vss', dest'')
                 end
           end
     end.

(* copying a list of value from one heap back to the same heap.  
   This is different from copy_list_other, since the same list is passed through recursively *)
Fixpoint copy_list_same (source:heap) (vs:list val) : option (list val*heap)
  := match vs with
         | nil => Some (nil, source)
         | v::vss => 
           match copy source v source with
             | None => None 
             | Some (v',dest') => 
                 match copy_list_same dest' vss with
                     | None => None
                     | Some (vss',dest'') => Some (v'::vss', dest'')
                 end
           end
     end.

Definition copy_list (sameHeap:bool) (source:heap) (vs:list val) (dest:heap) : option (list val*heap)
  := if sameHeap 
     then copy_list_same source vs
     else copy_list_other source vs dest.

Definition transCopy (sameHeap:bool) (source:heap) (λ:trans_type) (dest:heap)
  := match λ with
       | ε => Some (ε,if sameHeap then source else dest)
       | SyncFail v => match (copy_list sameHeap source v dest) with
                           | None => None
                           | Some (v', dest') => Some (⊗ v', dest')
                       end
       | AsyncFail v => match (copy_list sameHeap source v dest) with
                           | None => None
                           | Some (v', dest') => Some (× v', dest')
                       end
     end.

Lemma transCopy_sync {ph λ rh ve' rh' b} :
  Some (⊗ ve', rh') = transCopy b ph λ rh ->
  {ve | λ = ⊗ ve}.
Proof.
  unfold transCopy, copy_list.
  destruct λ; destruct b; dt idtac;
   match goal with 
      | [H: context[copy_list_same ?a ?b] |- _] => destruct (copy_list_same a b); dts idtac
      | [H: context[copy_list_other ?a ?b ?c] |- _] => destruct (copy_list_other a b c); dts idtac
    end.
Qed.

Lemma transCopy_async {ph λ rh ve' rh' b} :
  Some (× ve', rh') = transCopy b ph λ rh ->
  {ve | λ = × ve}.
Proof.
  unfold transCopy, copy_list.
  destruct λ; destruct b; dt idtac;
   match goal with 
      | [H: context[copy_list_same ?a ?b] |- _] => destruct (copy_list_same a b); dts idtac
      | [H: context[copy_list_other ?a ?b ?c] |- _] => destruct (copy_list_other a b c); dts idtac
    end.
Qed.

(* projecting out the values stored in a transition label, if any *)
Definition trans_vals λ : list val
  := match λ with
    | ε => nil
    | SyncFail v => v
    | AsyncFail v => v
  end.

(* associating a given place with a list of values *)
Definition placed_vals (p:place) (vs:list val) := map (fun x => (p,x)) vs.

Definition ptrans_vals p λ : list (place*val)
  := placed_vals p (trans_vals λ).

Lemma in_placed_vals {a v} p :
  In a v ->
  In (p,a) (placed_vals p v).
Proof.
  Hint Resolve in_map.
  unfold placed_vals; eauto.
Qed.

Lemma trans_vals_asSync ve : trans_vals (asSyncTrans ve) = ve.
Proof.
  unfold trans_vals, asSyncTrans.
  destruct ve; auto.
Qed.

Lemma vals_plus_trans_vals μ λ : 
  vals_plus_trans_type μ λ = trans_vals λ ++ μ.
Proof.
  unfold vals_plus_trans_type, trans_vals.
  destruct λ; auto.
Qed.

Lemma placed_vals_app p l1 l2 :
  placed_vals p (l1 ++ l2) = placed_vals p l1 ++ placed_vals p l2.
Proof.
  unfold placed_vals.
  apply map_app.
Qed.

Hint Rewrite trans_vals_asSync vals_plus_trans_vals placed_vals_app : rewrites.

Lemma trans_vals_toAsyncTrans λ : trans_vals (toAsyncTrans λ) = trans_vals λ.
Proof.
  destruct λ; trivial.
Qed.

Hint Rewrite trans_vals_toAsyncTrans : rewrites.

Lemma asSyncTrans_nasync {l vs} : asSyncTrans l = × vs -> False.
Proof.
  destruct l; simpl; congruence.
Qed.


End trans_labels.

Notation "⊗" := SyncFail.
Notation "×" := AsyncFail.

Hint Rewrite @trans_vals_asSync @vals_plus_trans_vals @placed_vals_app : rewrites.
Hint Rewrite @trans_vals_toAsyncTrans : rewrites.
