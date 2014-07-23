(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Defines a heap isomorphism between two values/objects in two (possibly different) local heaps *)
Require Export Assoc.
Require Export Auxiliary.
Require Import WfUtil.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Equality.
Require Coq.Vectors.Vector.

Section heap_iso.
Context {sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

(* First we define what it means to be isomorphic under a given witness iso,
   which maps object ids between the two heaps *)

Definition inIso_val (iso:list(oid*oid)) (v1 v2:val) : bool
  := match v1, v2 with
       | Object oid1, Object oid2 =>
         match iso[@oid1] with
           | None => false
           | Some oid2' => oid2 ==b oid2'
         end
       | GlobalObject p1 o1, GlobalObject p2 o2 =>  (p1 ==b p2)  && (o1 ==b o2)
       | Nat n1, Nat n2 => n1 ==b n2
       | _, _ => false
     end.

Definition inIso_pval (iso:list(oid*oid)) (fv1 fv2:fname*val) : bool
  := match fv1, fv2 with
       | (f1,v1), (f2,v2) => (f1 ==b f2) && (inIso_val iso v1 v2)
     end.

Program Definition inIso_obj (iso:list(oid*oid)) (o1 o2:obj) : bool
  := forallb2 (inIso_pval iso) o1 o2.

Definition inIso_oids (src_heap dest_heap:heap) (iso:list(oid*oid)) (p:oid*oid) 
  := match src_heap[@(fst p)], dest_heap[@(snd p)] with
         | Some o1, Some o2 => inIso_obj iso o1 o2
         | _, _ => false
     end.

Definition inIso_map (src_heap dest_heap:heap)
                     (iso:list(oid*oid)) (map:list(oid*oid)) :=
  forallb (inIso_oids src_heap dest_heap iso) map.

(* a witness iso is a heap isomorphism if every pair in it
   is isomorphic under iso. *)
Definition isIso (src_heap dest_heap:heap) (iso:list(oid*oid)) 
  := inIso_map src_heap dest_heap iso iso.

Hint Unfold Proper respectful impl equiv complement.

Ltac tcopy tac := try
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

Ltac t' tac := (dts ltac:(tcopy tac)).
Ltac t := t' idtac.

Hint Unfold equiv.

Program Lemma inIso_obj_dom : forall (iso:list(oid*oid)) (o1 o2:obj), 
                        inIso_obj iso o1 o2 = true -> domain o1 = domain o2.
Proof.
  unfold inIso_obj, inIso_pval.
  intros iso o1. dobj.
  induction o1; intros o2; dobj; destruct o2; repeat t. 
  eapply (H (build_obj o2 H5)); t.
Qed.

Section inclusions.

Lemma inIso_val_lincl : forall (iso1 iso2:list(oid*oid)) v1 v2,
                    lincl iso1 iso2 ->
                    inIso_val iso1 v1 v2 = true ->
                    inIso_val iso2 v1 v2 = true.
Proof.
  unfold inIso_val, lincl. t.
  erewrite H; [|eassumption]; t.
Qed.

Lemma inIso_pval_lincl : forall (iso1 iso2:list(oid*oid)) pv1 pv2,
                    lincl iso1 iso2 ->
                    inIso_pval iso1 pv1 pv2 = true ->
                    inIso_pval iso2 pv1 pv2 = true.
Proof.
  Hint Resolve inIso_val_lincl.
  t.
Qed.
  
Lemma inIso_obj_lincl : forall (iso1 iso2:list(oid*oid)) o1 o2,
                    lincl iso1 iso2 ->
                    inIso_obj iso1 o1 o2 = true ->
                    inIso_obj iso2 o1 o2 = true.
Proof.
  Hint Resolve inIso_pval_lincl.
  unfold inIso_obj.
  t.
  eapply Forall2_incl; [|eassumption]; eauto.
Qed.

Lemma inIso_oids_lincl : forall {src_heap dest_heap:heap} {iso1 iso2:list(oid*oid)} {p},
                    lincl iso1 iso2 ->
                    inIso_oids src_heap dest_heap iso1 p = true ->
                    inIso_oids src_heap dest_heap iso2 p = true.
Proof.
  Hint Resolve inIso_obj_lincl.
  unfold inIso_oids.
  t.
Qed.

Lemma inIso_oids_hincl1 : forall {src_heap src_heap' dest_heap:heap} {iso:list(oid*oid)} {p},
                    hincl src_heap src_heap' ->
                    inIso_oids src_heap  dest_heap iso p = true ->
                    inIso_oids src_heap' dest_heap iso p = true.
Proof.
  unfold inIso_oids; t.
  erewrite H; eauto.
Qed.

Lemma inIso_oids_hincl2 : forall {src_heap dest_heap dest_heap':heap} {iso:list(oid*oid)} {p},
                    hincl dest_heap dest_heap' ->
                    inIso_oids src_heap dest_heap  iso p = true ->
                    inIso_oids src_heap dest_heap' iso p = true.
Proof.
  unfold inIso_oids; t.
  erewrite H; eauto.
Qed.
  
Lemma inIso_map_lincl1 : forall (src_heap dest_heap:heap) (iso1 iso2:list(oid*oid)) map,
                    lincl iso1 iso2 ->
                    inIso_map src_heap dest_heap iso1 map = true ->
                    inIso_map src_heap dest_heap iso2 map = true.
Proof.
  Hint Resolve inIso_oids_lincl.
  unfold inIso_map; t.
Qed.

Lemma inIso_map_incl2 : forall (src_heap dest_heap:heap) (iso:list(oid*oid)) map1 map2,
                    incl map2 map1 ->
                    inIso_map src_heap dest_heap iso map1 = true ->
                    inIso_map src_heap dest_heap iso map2 = true.
Proof.
  unfold inIso_map; t.
Qed.

Lemma inIso_map_hincl1 : forall (src_heap src_heap' dest_heap:heap) (iso:list(oid*oid)) map,
                    hincl src_heap src_heap' ->
                    inIso_map src_heap dest_heap iso map = true ->
                    inIso_map src_heap' dest_heap iso map = true.
Proof.
  Hint Resolve inIso_oids_hincl1.
  unfold inIso_map; t. 
Qed.

Lemma inIso_map_hincl2 : forall (src_heap dest_heap dest_heap':heap) (iso:list(oid*oid)) map,
                    hincl dest_heap dest_heap' ->
                    inIso_map src_heap dest_heap iso map = true ->
                    inIso_map src_heap dest_heap' iso map = true.
Proof.
  Hint Resolve inIso_oids_hincl2.
  unfold inIso_map; t. 
Qed.

Lemma isIso_lincl : forall {src_heap dest_heap:heap} {iso1 iso2:list(oid*oid)},
                      lincl iso1 iso2 -> incl iso2 iso1 ->
                      isIso src_heap dest_heap iso1 = true ->
                      isIso src_heap dest_heap iso2 = true.
Proof.
  Hint Resolve inIso_map_lincl1 inIso_map_incl2.
  unfold isIso; eauto.
Qed.

Lemma isIso_hincl1 : forall {src_heap src_heap' dest_heap:heap} {iso:list(oid*oid)},
                      hincl src_heap src_heap' ->
                      isIso src_heap dest_heap iso = true ->
                      isIso src_heap' dest_heap iso = true.
Proof.
  Hint Resolve inIso_map_hincl1.
  unfold isIso; eauto.
Qed.

Lemma isIso_hincl2 : forall {src_heap dest_heap dest_heap':heap} {iso:list(oid*oid)},
                      hincl dest_heap dest_heap' ->
                      isIso src_heap dest_heap iso = true ->
                      isIso src_heap dest_heap' iso = true.
Proof.
  Hint Resolve inIso_map_hincl2.
  unfold isIso; eauto.
Qed.

End inclusions.

Ltac app_tac := try match goal with 
    | [H: In _ (_ ++ _) |- _ ] => apply in_app_iff in H
end.

Lemma inIso_map_app : forall (src_heap dest_heap:heap) (iso:list(oid*oid)) map1 map2,
                    inIso_map src_heap dest_heap iso map1 = true ->
                    inIso_map src_heap dest_heap iso map2 = true
                    -> inIso_map src_heap dest_heap iso (map1 ++ map2) = true.
Proof.
  unfold inIso_map; t' app_tac.
Qed.

Lemma isIso_app : forall {src_heap dest_heap:heap} {iso1 iso2:list(oid*oid)},
                    disjoint (domain iso1) (domain iso2) ->
                    isIso src_heap dest_heap iso1 = true ->
                    isIso src_heap dest_heap iso2 = true
                    -> isIso src_heap dest_heap (iso1 ++ iso2) = true.
Proof.
  unfold isIso.
  intros.
  apply inIso_map_app.
  - eapply inIso_map_lincl1; eauto; eapply lincl_appr.
  - eapply inIso_map_lincl1; eauto; eapply lincl_appl; auto.
Qed.

Lemma inIso_val_oids : forall iso oid oid', inIso_val iso (Object oid) (Object oid') = true <-> iso[@oid] = Some oid'.
Proof.
  repeat t; rewrite H; t.
Qed.

Lemma inIso_val_inv : forall {iso a b}, inIso_val iso (Object a) b = true -> exists b', b = Object b' /\ iso[@a] = Some b'.
Proof.
  t.
Qed.

Lemma inIso_oids_inv : forall {src_heap dest_heap iso p}, 
                         inIso_oids src_heap dest_heap iso p = true -> 
                         exists o1 o2, src_heap[@(fst p)] = Some o1 
                                    /\ dest_heap[@(snd p)] = Some o2 
                                    /\ inIso_obj iso o1 o2 = true.
Proof.
unfold inIso_oids; t.
Qed.

Lemma inIso_obj_lookup : forall {iso a b f a'},
                           inIso_obj iso a b = true -> a[@f] = Some (Object a') ->
                           exists b', b[@f] = Some (Object b')
                                      /\ iso[@a'] = Some b'.
Proof.
  unfold inIso_obj. intros iso a. dobj.
  induction a; intro b; t.
  specialize (IHa (nodup_sbool H4) H4).
  destruct b; try discriminate.
  t.
  destruct (f1 ==  f); t.
  - rewrite lookup_cons_eq in H0 |- *.
    t.
  - rewrite lookup_cons_neq in H0 |- *; auto.
    edestruct (IHa (build_obj b H8)); t.
Qed.

Lemma inIso_obj_lookup' : forall {iso a pf b f a'},
                           inIso_obj iso (exist _ a pf) b = true -> a[@f] = Some (Object a') ->
                           exists b', (proj1_sig b)[@f] = Some (Object b')
                                      /\ iso[@a'] = Some b'.
Proof.
  intros.
  poses (@inIso_obj_lookup iso (exist _ a pf) b f a' H).
  rewrite obj_lookup_simpl in P.
  destruct (P H0).
  rewrite obj_lookup_simpl in H1.
  eauto.
Qed.

Section sym.

Context {iso:list(oid*oid)} (diso:bidet iso).
  
Hint Unfold equiv_decb.

Lemma inIso_val_sym : forall (v1 v2:val), inIso_val iso v1 v2 = inIso_val (mswap iso) v2 v1.
Proof.
  unfold bidet, inIso_val in *.
  
  destruct v1; destruct v2; intuition; try solve[t].
  case_eq (iso[@o]); case_eq ((mswap iso)[@o0]); 
  t' ltac:(repeat match goal with
                    | [H1:NoDup (domain (mswap ?iso)), H2:?iso[@?o1] = Some ?o2 |- _ ] =>
                      extend (swap_lookup_nodup H1 H2)
                    | [H1:NoDup (domain ?iso), H2:(mswap ?iso)[@?o1] = Some ?o2 |- _ ] =>
                      extend (swap_lookup_nodup' H1 H2)
                  end); congruence.
Qed.

Lemma inIso_pval_sym : forall pv1 pv2, inIso_pval iso pv1 pv2 = inIso_pval (mswap iso) pv2 pv1.
Proof.
  Hint Resolve inIso_val_sym.
  unfold inIso_pval; t.
Qed.

Lemma inIso_obj_sym : forall ob1 ob2, inIso_obj iso ob1 ob2 = inIso_obj (mswap iso) ob2 ob1.
Proof.
  Hint Resolve inIso_pval_sym.
  unfold inIso_obj; t.
  rewrite forallb2_sym.
  apply forallb2_eq; auto.
Qed.

Lemma inIso_oids_sym : forall src_heap dest_heap oids, inIso_oids src_heap dest_heap iso oids = inIso_oids dest_heap src_heap (mswap iso) (swap oids).
 Proof.
  Hint Resolve inIso_obj_sym.
  unfold inIso_oids; t.
  destruct (src_heap[@o]);
    destruct (dest_heap[@o0]); auto.
Qed.


Lemma inIso_map_sym : forall {src_heap dest_heap map}, 
                         inIso_map src_heap dest_heap iso map =
                         inIso_map dest_heap src_heap (mswap iso) (mswap map).
Proof.
  Hint Resolve inIso_oids_sym.
  unfold inIso_map; t.
  unfold mswap; rewrite forallb_map.
  apply forallb_eq; auto.
Qed.

Lemma isIso_sym : forall {src_heap dest_heap}, 
                     isIso src_heap dest_heap iso = isIso dest_heap src_heap (mswap iso).
Proof.
  Hint Resolve inIso_map_sym.
  unfold isIso; t.
Qed.

End sym.

Lemma inIso_oids_nin_update1 : forall (src_heap dest_heap : heap) (iso : list (oid * oid)) a0 a p v,
                                 (fst a0) <> a  ->
                                 inIso_oids (update src_heap a p v) dest_heap iso a0 =
                                 inIso_oids src_heap dest_heap iso a0.
Proof.
  unfold inIso_oids; intros.
  rewrite lookup_update2; auto.
Qed.

Lemma inIso_map_nin_update1 : forall (src_heap dest_heap : heap) (iso : list (oid * oid)) map
     (a : oid) (p : contains src_heap a) v,
   ~ In a (domain map) ->
   inIso_map (update src_heap a p v) dest_heap iso map =
   inIso_map src_heap dest_heap iso map.
Proof.
  Hint Resolve in_dom.
  unfold inIso_map; intros.
  apply forallb_eq; intros.
  apply inIso_oids_nin_update1.
  t.
Qed.

Lemma isIso_nin_update1 : forall src_heap dest_heap iso a p v, ~ In a (domain iso) -> 
  isIso (update src_heap a p v) dest_heap iso = isIso src_heap dest_heap iso. 
Proof.
  Hint Resolve inIso_map_nin_update1.
  unfold isIso; auto.  
Qed. 

Hint Unfold contains.

Lemma inIso_map_incl_src src_heap dest_heap iso m : inIso_map src_heap dest_heap iso m = true -> incl (domain m) (dom src_heap).
Proof.
  Opaque heap dom.
  unfold incl, inIso_map; t.
  destruct (in_domain_in H0).
  unfold inIso_oids in *.
  specialize (H _ H1).
  t.
  apply dom_lookup.
  t.
Qed.

Lemma inIso_map_incl_dest src_heap dest_heap iso m : inIso_map src_heap dest_heap iso m = true -> incl (domain (mswap m)) (dom dest_heap).
Proof.
 unfold incl, inIso_map; t.
  destruct (in_domain_in H0).
  rewrite <- mswap_in in H1.
  specialize (H _ H1).
  unfold inIso_oids in *.
  t.
  apply dom_lookup.
  t.
Qed.

End heap_iso.
