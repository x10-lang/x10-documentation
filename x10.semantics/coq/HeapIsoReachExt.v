(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Some additional properties of heap isomorphism and reachability *)
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

(* This should be in HeapIsoReach *)
Section reach.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Ltac reach_tcopy tac := try
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

Ltac reach_t' tac := (dts ltac:(reach_tcopy tac)).
Ltac reach_t := reach_t' idtac.

Ltac reach_itac := try match goal with
  | [H1: inIso_obj ?iso (exist _ ?v1 _) (exist _ ?v2 _) = true,
     H2: ?v1[@?x] = (Some (Object _)) |- _] =>
    match goal with
      |[H:v2[@x] = _ |- _ ] => fail 1
      | _ => destruct (inIso_obj_lookup H1 H2); reach_t
    end
end.

Ltac reach_t' tac ::= (dts ltac:(reach_itac; reach_tcopy tac)).
Ltac reach_t ::= reach_t' idtac.

Lemma inIso_obj_lookup_global : forall {iso a b f a' r},
                           inIso_obj iso a b = true -> a[@f] = Some (GlobalObject r a') ->
                           b[@f] = Some (GlobalObject r a').
Proof.
  unfold inIso_obj. intros iso a. dobj.
  induction a; intro b; reach_t.
  specialize (IHa (nodup_sbool H4) H4).
  destruct b; try discriminate.
  reach_t.
  destruct (f1 == f); unfold equiv, complement in *; subst.
  - rewrite lookup_cons_eq in H0 |- *.
    reach_t.
    unfold equiv in *; congruence.
  - rewrite lookup_cons_neq in H0 |- *; auto. 
    eapply (IHa (build_obj b H8)); reach_t.
Qed.

Lemma isIso_reach_global {ph qh iso o o' r v} :
  isIso ph qh iso = true ->
  inIso_val iso o o' = true ->
  reachable_from ph o (GlobalObject r v) ->
  reachable_from qh o' (GlobalObject r v).
Proof.
  Hint Constructors reachable_from.
  intros isiso iniso reach.
  revert o' iniso.
  dependent induction reach; intros.
  - repeat reach_t. unfold equiv in *; subst; eauto.
  - poses isiso. 
    unfold isIso, inIso_map in P.
    rewrite forallb_forall in P.
    apply inIso_val_inv in iniso.
    destruct iniso as [? [??]]; subst.
    poses (P _ (lookup_in H2)).
    apply inIso_oids_inv in P0.
    dt idtac.
    rewrite H in H1; dt idtac.
    destruct (reachable_from_to_eqobj _ reach); subst.
    + poses (inIso_obj_lookup_global H4 H0); eauto.
    + destruct H1; subst.
      destruct (inIso_obj_lookup H4 H0) as [?[??]].
      eapply RVStep; try eassumption.
      eapply IHreach; eauto 2.
      simpl. rewrite H5.
      dt congruence.
Qed.

End reach.
