(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* defines copy_obj, which copies the object graph rooted at an object from one (local) heap to another *)
Require Import Auxiliary.
Require Import WfUtil.
Require Import HeapIsoReach.

Require Import Omega.  
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Wf.
Require Import Coq.Sorting.Permutation.
Require Import Program.

Section copy_obj.
Context {sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Section c.
Variable src_heap:heap.
Let src_heap_dom : list oid := dom src_heap.
Let src_heap_size := length src_heap_dom.

Definition remaining (mappings:(list (oid*oid))):= S src_heap_size - length mappings.

(* define the well founded measure that we will use to prove termination of our graph copy algorithm *)
Program Definition measure_fun :  (list (oid*oid)) * obj -> (list (oid*oid)) * obj -> Prop 
  := wf_pair_pb lt lt remaining (@length (fname*val)).
Lemma measure_fun_wf : well_founded measure_fun.
Proof. 
  apply wf_pair_pb_wf; auto; apply lt_wf.
Defined.

Definition good_map (m:(list (oid*oid))) := bidet m /\ incl (domain m) src_heap_dom.

Theorem good_map_lt : forall {m}, good_map m -> length m <= src_heap_size.
  unfold good_map, bidet, src_heap_size, domain; intuition.
  erewrite <- (map_length fst).
  apply (@nodup_incl_le _ equiv_dec); auto.
Qed.

Lemma good_map_add_lt : forall s oid oid', good_map (s) -> remaining ((oid, oid') :: s) < remaining s.
Proof.
  unfold remaining; intros.
  generalize (good_map_lt H); intro.
  unfold remaining.
  simpl.
  destruct (length s); simpl; omega.
Qed.

Lemma good_map_lt_remain : forall a b, good_map b -> length a < length b -> remaining b < remaining a.
Proof.
  unfold remaining; intros.
  generalize (good_map_lt H).
  omega.
Qed.

Global Instance good_map_perm : Proper (@Permutation (oid*oid) ==> iff) good_map.
Proof.
Hint Resolve Permutation_map.
unfold good_map; repeat red; intros.
rewrite <- H; intuition.
Qed.

Lemma good_map_app_inv : forall {a b}, good_map (a++b) -> good_map a.
Proof.
  Hint Resolve bidet_app_inv.
  unfold good_map, incl; dts idtac.
Qed.

Lemma good_map_cons_lookup {oid1 oid2 s y} : ~ In oid1 (domain s) ->
                                             ~ In oid2 (domain (mswap s)) ->
                                             src_heap[@oid1] = Some y ->
                                             good_map s -> good_map ((oid1,oid2)::s).
Proof.
  Hint Constructors NoDup.
  unfold good_map, bidet, incl, src_heap_dom; dts idtac.
  eapply dom_lookup2; eauto.
Qed.

Unset Transparent Obligations.

(* Since reasoning about well founded recursion functions is difficult, we give it a strong type that embeds all the properties we want *)
(* given a well formed map between heaps (corresponding to the objects we have already created during this traversal), we modify the destination heap
   to add in a copy of the input object.  The function is fairly simple, however the need to explicitly write out various proof types makes it look rather scary.
 *)
Program Fixpoint copy_obj (mo:{m:(list (oid*oid)) | good_map m}*obj) (dest_heap:heap) (pf:incl (domain (mswap (fst mo))) (dom dest_heap)) {wf measure_fun mo}:
   (({ret:(list (oid*oid))*obj*heap | let '(m',o',h'):=ret in 
                                  good_map (m'++(fst mo))
                               /\ reach_list_obj src_heap (domain m') (snd mo)
                               /\ inIso_map src_heap h' (m'++(fst mo)) m' = true
                               /\ hincl dest_heap h' 
                               /\ incl (dom h') (domain (mswap (m'++(fst mo))) ++ (dom dest_heap))
                               /\ inIso_obj (m'++(fst mo)) (snd mo) o' = true}) + ({ret:oid|reachable_from_obj src_heap (snd mo) (Object ret) /\ ~ contains src_heap ret})) :=
  let '(mappings, o) := mo in
  match o with
       | nil => inl (exist (fun (ret:(list (oid*oid))*obj*heap) => 
                               let '(m',o',h'):=ret in 
                                  good_map (m'++mappings)
                               /\ reach_list_obj src_heap (domain m') o
                               /\ inIso_map src_heap h' (m'++mappings) m' = true
                               /\ hincl dest_heap h' 
                               /\ incl (dom h') (domain (mswap (m'++mappings)) ++ (dom dest_heap))
                               /\ inIso_obj (m'++mappings) o o' = true) (nil, o, dest_heap) _)
       | a::ls => let v := (snd a) in
         match 
           match v return 
                  (({ret:(list (oid*oid))*val*heap | let '(m',v',h'):=ret in 
                                                 good_map (m'++mappings) 
                                              /\ reach_list src_heap (domain m') v
                                              /\ inIso_map src_heap h' (m'++mappings) m' = true
                                              /\ hincl dest_heap h' 
                                              /\ incl (dom h') (domain (mswap (m'++mappings)) ++ (dom dest_heap))
                                              /\ inIso_val (m'++mappings) v v' = true}) + ({ret:oid|reachable_from src_heap v (Object ret) /\ ~ contains src_heap ret})) with
             | Object oi => match (proj1_sig mappings) [@ oi] with
                               | Some v' => inl (exist (fun ret:((list (oid*oid))*val*heap) => let '(m',v',h'):=ret in 
                                                 good_map (m'++mappings) 
                                              /\ reach_list src_heap (domain m') (Object oi)
                                              /\ inIso_map src_heap h' (m'++mappings) m' = true
                                              /\ hincl dest_heap h' 
                                              /\ incl (dom h') (domain (mswap (m'++mappings)) ++ (dom dest_heap))
                                              /\ inIso_val (m'++mappings) (Object oi) v' = true) (nil, Object v', dest_heap) _)
                               | None => match src_heap[@oi] with
                                           | None => @inr ({ret:(list (oid*oid))*val*heap | let '(m',v',h'):=ret in 
                                                               good_map (m'++mappings) 
                                                         /\ reach_list src_heap (domain m') (Object oi)
                                                         /\ inIso_map src_heap h' (m'++mappings) m' = true
                                                         /\ hincl dest_heap h' 
                                                         /\ incl (dom h') (domain (mswap (m'++mappings)) ++ (dom dest_heap))
                                                         /\ inIso_val (m'++mappings) (Object oi) v' = true}) 
                                                         ({ret:oid|reachable_from src_heap (Object oi) (Object ret) /\ ~ contains src_heap ret})
                                                         oi
                                           | Some obj => 
                                             let '(dest_heap', oi') := new dest_heap nil in
                                               match copy_obj (((oi, oi')::mappings), obj) dest_heap' _ with
                                                 | inr (exist ret pf) =>  inr ret
                                                 | inl (exist (mappings', newobj, dest_heap3) pf) =>
                                                   let dest_heap4 := update dest_heap3 oi' _ newobj in
                                                    inl (exist (fun ret:((list (oid*oid))*val*heap) => let '(m',v',h'):=ret in 
                                                         good_map (m'++mappings) 
                                                         /\ reach_list src_heap (domain m') (Object oi)
                                                         /\ inIso_map src_heap h' (m'++mappings) m' = true
                                                         /\ hincl dest_heap h' 
                                                         /\ incl (dom h') (domain (mswap (m'++mappings)) ++ (dom dest_heap))
                                                         /\ inIso_val (m'++mappings) (Object oi) v' = true) ((oi, oi')::mappings', Object oi', dest_heap4) _)
                                               end
                                         end
                             end
             | GlobalObject p r => inl (exist (fun ret:((list (oid*oid))*val*heap) => let '(m',v',h'):=ret in 
                                                 good_map (m'++mappings) 
                                              /\ reach_list src_heap (domain m') (GlobalObject p r)
                                              /\ inIso_map src_heap h' (m'++mappings) m' = true
                                              /\ hincl dest_heap h' 
                                              /\ incl (dom h') (domain (mswap (m'++mappings)) ++ (dom dest_heap))
                                              /\ inIso_val (m'++mappings) (GlobalObject p r) v' = true) (nil, GlobalObject p r, dest_heap) _)
             | Nat n => inl (exist (fun ret:((list (oid*oid))*val*heap) => let '(m',v',h'):=ret in 
                                                 good_map (m'++mappings) 
                                              /\ reach_list src_heap (domain m') (Nat n)
                                              /\ inIso_map src_heap h' (m'++mappings) m' = true
                                              /\ hincl dest_heap h'
                                              /\ incl (dom h') (domain (mswap (m'++mappings)) ++ (dom dest_heap))
                                              /\ inIso_val (m'++mappings) (Nat n) v' = true) (nil, Nat n, dest_heap) _)
           end with
           | inr (exist ret pf) => inr ret
           | inl vhm => let vhm' := @id ({ret:(list (oid*oid))*val*heap | let '(m',v',h'):=ret in 
                                                 good_map (m'++mappings) 
                                              /\ reach_list src_heap (domain m') v
                                              /\ inIso_map src_heap h' (m'++mappings) m' = true
                                              /\ hincl dest_heap h' 
                                              /\ incl (dom h') (domain (mswap (m'++mappings)) ++ (dom dest_heap))
                                              /\ inIso_val (m'++mappings) v v' = true})%type vhm in 
             let '(mappings', v', dest_heap') :=
              proj1_sig vhm in
             match copy_obj (mappings'++mappings, ls) dest_heap' _ with
               | inr (exist ret pf) => inr ret
               | inl ohm => let '(mappings'', ls', dest_heap'') := ohm in
                             inl (exist (fun (ret:(list (oid*oid))*obj*heap) => 
                               let '(m',o',h'):=ret in 
                                  good_map (m'++mappings)
                               /\ reach_list_obj src_heap (domain m') o
                               /\ inIso_map src_heap h' (m'++mappings) m' = true
                               /\ hincl dest_heap h' 
                               /\ incl (dom h') (domain (mswap (m'++mappings)) ++ (dom dest_heap))
                               /\ inIso_obj (m'++mappings) o o' = true) ((mappings'++mappings''), (obj_cons (fst a) v' ls' _), dest_heap'') _)

             end
         end
     end.
Require Import Program.Tactics.
Ltac invs :=  try match goal with 
  | [H: ?f _ _ = ?f _ _ |- _] => inversion Heq_mo
end.
Ltac deq := repeat (match goal with
         | [H: (?X,?Y)=(?X,?Y) |- _] => clear H
         | [H: (_, _) = (_, _) |- _] => inversion H
end;
subst).
Hint Resolve reach_list_nil reach_list_obj_nil.
Next Obligation.
t.
Qed.
Next Obligation.
t.
Qed.
Ltac dnewc := match goal with 
    [H: context [ new ?h ?v ] |- _ ] => 
    poses (new_fresh h v);
    poses (lookup_new1 h v);
    poses (lookup_new2 h v);
    poses (hincl_new h v);
    destruct (new h v)
end.
Next Obligation.
split.
- constructor.
- unfold contains. rewrite <- Heq_anonymous0. destruct 1; discriminate.
Qed.
Next Obligation.
invs; intuition.
Hint Resolve lookup_none_nin.
eapply good_map_cons_lookup; eauto; deq.
- eapply lookup_none_nin; eauto.
- intro iin. apply pf in iin.
  dnewc. apply dom_lookup in iin.
  destruct iin.
  congruence.
Qed.
Next Obligation.
invs. intros ? ?.
dnewc.
apply dom_lookup; red.
inversion Heq_anonymous1; subst.
t. 
eapply (hincl_contains P2). apply dom_lookup; t.
Qed.
Next Obligation.
unfold measure_fun, wf_pair; simpl in *; left.
invs.
apply good_map_add_lt; auto.
Qed.
Next Obligation.
intuition.
destruct r as [?[?[??]]].
econstructor; eauto.
Qed.
Next Obligation.
clear Heq_anonymous2.
dnew. red; t.
Qed.
Next Obligation.
dupdate_pf; invs. 
clear Heq_anonymous2. 
dnew.
assert (pl:lincl (mappings' ++ (oi, o1) :: s) ((oi, o1) :: mappings' ++  s)).
       eapply lincl_perm. unfold good_map, bidet in *; t.
       rewrite <- Permutation_middle. reflexivity.
Hint Unfold equiv complement.
intuition.
  - eapply good_map_perm; [|apply g]; eapply Permutation_middle.
  - unfold good_map, reach_list_obj, reach_list in *. t; simpl in *; subst.
    specialize (r _ H). unfold reachable_from_obj in *; t.
    rewrite <- H1.
    Hint Constructors reachable_from.
    rewrite H7 in H9; t.
  -  eapply inIso_map_lincl1 in e; [|exact pl].
     eapply inIso_obj_lincl in e0; [|exact pl].
     t.
     + unfold inIso_oids. t. rewrite <- Heq_anonymous0.
       rewrite lookup_update1.
       trivial.
     + unfold inIso_map, inIso_oids. t.
       unfold inIso_map, inIso_oids in e. t.
       poses (e _ H1); t.
       destruct (o1 == o0); t.
       * rewrite lookup_update1.
         destruct g as [[gnd gnds] _].
         autorewrite with rewrites in gnds.
         apply NoDup_app_dis in gnds.
         elim (gnds o0).
           eapply in_dom. rewrite <- mswap_in. eassumption.
           simpl; intuition.
       * rewrite lookup_update2; trivial. 
         rewrite Heq0; trivial.
  - unfold hincl in *; intros.
    destruct (o1 == x); t.
    * congruence. 
    * rewrite lookup_update2; trivial.
      apply h; trivial.
      apply P2; trivial.
  - rewrite dom_update.
    intros elem inelem.
    specialize (i elem inelem).
    app_tac.
    change (In elem ((o1 :: domain (mswap (mappings' ++ s))) ++ dom dest_heap)).
    apply in_app_iff.
    destruct i as [i|i].
    * left. autorewrite with rewrites in *.
      rewrite Permutation_middle. trivial.
    * destruct (elem == o1); unfold equiv, complement in *. 
      subst; simpl; intuition.
      right. specialize (P1 _ c0).
      destruct (dom_lookup1 _ _ i).
      rewrite P1 in H1. 
      eapply dom_lookup2; eauto.
  - clear. rewrite lookup_cons_eq; t.
Qed.
Next Obligation.
clear copy_obj.
t.
Qed.
Next Obligation.
clear copy_obj.
t.
Qed.
Next Obligation.
split; trivial.
unfold reachable_from_obj.
simpl in r.
invs. subst.
exists f; exists v.
split; trivial.
rewrite obj_lookup_simpl.
rewrite <- Heq_o. rewrite lookup_cons_eq. trivial.
Qed.
Next Obligation.
clear Heq_anonymous copy_obj.
invs; t.
apply nodup_sbool; auto.
Qed.
Next Obligation.
clear Heq_anonymous copy_obj.
invs; t.
apply incl_app; auto.
 - eapply inIso_map_incl_dest; eauto.
 - eapply hincl_incl; eauto.
Qed.
Next Obligation.
invs; t.
unfold measure_fun, wf_pair, wf_pair_pb, wf_pair; simpl.
clear Heq_anonymous copy_obj Heq_mo nd.
inversion Heq_anonymous0; subst; clear Heq_anonymous0.
destruct l; simpl.
- right; auto.
- left. apply good_map_lt_remain; auto.
  simpl. rewrite app_length.
  apply le_n_S; apply le_plus_r.
Qed.
Next Obligation.
split; trivial.
unfold reachable_from_obj.
invs; subst.
inversion Heq_anonymous0; subst.
destruct r as [?[?[??]]].
clear Heq_anonymous1.
rewrite obj_lookup_simpl in e1. simpl in e1.
exists x; exists x0.
split; trivial.
rewrite obj_lookup_simpl.
rewrite <- Heq_o. 
rewrite lookup_cons_neq; trivial.
intro; subst.
clear Heq_anonymous copy_obj.
destruct o0.
simpl in Heq_o. clear Heq_mo.
rewrite <- Heq_o in e2.
apply sbool_nodup in e2.
inversion e2; subst.
elim H3.
eapply in_dom.
eapply lookup_in.
eauto.
Qed.
Next Obligation.
inversion Heq_anonymous0; invs.
clear Heq_anonymous1.
rewrite <- (inIso_obj_dom _ _ _ e0).
simpl.
dobj; subst.
inversion P0.
trivial.
Qed.
Next Obligation.
inversion Heq_ohm; invs. simpl in *.
dobj. simpl in *; subst.
inversion Heq_anonymous0; subst.
poses g.
rewrite app_assoc in P3.
assert (g': (good_map ((l0 ++ l) ++ s))) by
    (eapply good_map_perm; [|eassumption]; 
     apply Permutation_app; [|reflexivity];
     apply Permutation_app_swap).
split; trivial. split; [|split;[|split;[|split]]].
- 
rewrite domain_app.
eapply reach_list_obj_cons'; eauto.
  destruct P3.
  eapply bidet_app_inv; eauto.
- clear Heq_ohm Heq_anonymous1.
  apply inIso_map_app.
  + eapply inIso_map_hincl2; [eassumption|].
    eapply inIso_map_lincl1; [|eassumption].
    apply incl_lincl.
    * destruct g' as [[??]?]; auto.
    * rewrite app_ass.
      intros x xin.
      apply in_app_iff in xin.
      apply in_app_iff.
      rewrite in_app_iff.
      tauto.
  +  eapply inIso_map_lincl1; [|eassumption].
     apply lincl_perm.
     * rewrite app_ass in P3. destruct P3 as [[??]?]; trivial.
     * rewrite <- app_ass. apply Permutation_app_tail. apply Permutation_app_comm.
- transitivity h1; eauto.
- eapply incl_trans_app.
+ eapply (incl_perm2 i).
  eapply Permutation_app_tail.  clear; t.
  rewrite <- app_ass.
  apply Permutation_app_tail.
  apply Permutation_app_comm.
+ etransitivity; [eexact i0|].
  clear; t. unfold incl.
  intros.
  repeat rewrite in_app_iff.
  repeat (app_tac; intuition).
- eapply (@inIso_obj_lincl _ (l ++ l0 ++ s)).
  + apply lincl_perm.
     * rewrite app_ass in P3. destruct P3 as [[??]?]; trivial.
     * rewrite <- app_ass. apply Permutation_app_tail. apply Permutation_app_comm.
  + unfold inIso_obj in *; simpl in *.
    inversion H3; subst.
    rewrite e0.
  assert (li1:lincl (l0 ++ s) (l ++ l0 ++ s)).
    apply incl_lincl.
       rewrite app_ass in P3. destruct P3 as [[??]?]; trivial.
           intros x xin.
           apply in_app_iff in xin.
           apply in_app_iff.
           rewrite in_app_iff.
           tauto.
  rewrite (inIso_val_lincl _ _ _ _ li1 e2). 
  clear; t.
Qed.
Next Obligation.
  apply measure_wf; apply measure_fun_wf.
Defined.

Global Opaque copy_obj.

End c.

End copy_obj.

Global Opaque copy_obj.

