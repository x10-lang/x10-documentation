(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* defines copy, which copies the object graph rooted at a value from one (local) heap to another *)
Require Import Auxiliary.
Require Import WfUtil.
Require Import HeapIsoReach.
Require Import CopyObj.

Require Import Omega.  
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Program.Wf.
Require Import Coq.Sorting.Permutation.
Require Import Program.

Section copy_val.
Context {sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Section c.
Variable src_heap:heap.

(* The definition of copy_obj is transparent, since it was defined (it is
    not a lemma).  Declaring it opaque does not inhibit normalization.
    This trick (due to Gonthier?) ``blocks'' normalization behind the
    ``really opaque'' master key.  This is critical, since we do not
    want coq to unfold the definition of copy_obj (since it runs out
    of memory and crashes).

   We ``lock'' copy as well, since we will (after proving the spec)
   only need to reason about it via its spec.  *)

(* The embedded proofs are causing a lot of problems, since it is very
   difficult to pattern match.  Since the relevant proofs are
   decidable anyway, we test them again and use the new proofs.  We
   then prove after the fact that we know which branch was taken.
   This greatly simplifies the proof *)


Definition locked_copy_obj sh mo dh pf := let 'tt := master_key 
                                          in copy_obj sh mo dh pf.

Definition locked_copy_obj_base sh mo dh :=
  match (incl_dec (domain (mswap (fst (` (fst mo), snd mo)))) (dom dh)) with
    | left pf => match locked_copy_obj sh mo dh pf with
                     | inl x => Some (proj1_sig x)
                     | inr _ => None
                 end
    | right pf => Some ((` (fst mo)), (snd mo), dh)
  end.

Program Definition copy_obj_spec sh mo dest_heap m' o' h' :=
  good_map sh (m'++ (fst mo))
     /\ reach_list_obj sh (domain m') (snd mo)
     /\ inIso_map sh h' (m'++(fst mo)) m' = true
     /\ hincl dest_heap h' 
     /\ incl (dom h') (domain (mswap (m'++(fst mo))) ++ (dom dest_heap))
     /\ inIso_obj (m'++(fst mo)) (snd mo) o' = true.

Program Lemma locked_copy_obj_base_spec sh mo dest_heap (pf:(incl (domain (mswap (fst (` (fst mo), snd mo)))) (dom dest_heap))) m' o' h' :
     locked_copy_obj_base sh mo dest_heap = Some (m', o', h') 
  ->  copy_obj_spec sh mo dest_heap m' o' h'.
Proof.
  unfold locked_copy_obj_base, copy_obj_spec.
  intros.
  destruct (incl_dec (domain (mswap (fst (` (fst mo), snd mo)))) (dom dest_heap)); [|intuition].
  destruct (locked_copy_obj sh mo dest_heap i); try congruence.
  destruct s. simpl in *. destruct x as [[??]?].
  inversion H; subst. trivial.
Qed.

Definition update_if (h:heap) (a:oid) (o:obj) :=
  match contains_dec h a with
      | left pf => update h a pf o
      | right pf => h
  end.

Lemma good_map_singleton (oid oid':oid) (pf:contains src_heap oid) : good_map src_heap ((oid,oid')::nil).
Proof.
Hint Constructors NoDup.
unfold good_map, domain, incl; simpl; intuition.
- unfold bidet; intuition; simpl; eauto.
- subst. apply dom_lookup; red; eauto.
Qed.

Definition copy'_part (oid:oid) (pf:contains src_heap oid) (dest_heap:heap) : option (val*heap) 
  := match src_heap [@ oid] with
           | None => None
           | Some obj => 
             let '(dest_heap', oid') := new dest_heap obj in
             match (locked_copy_obj_base src_heap ((exist _ ((oid, oid')::nil) (good_map_singleton oid oid' pf)), obj) dest_heap') with
               | None => None
               | Some (mappings', newobj, dest_heap3) =>
                 let dest_heap4 := update_if dest_heap3 oid' newobj in
                   Some (Object oid', dest_heap4)
             end
         end.

(* copying a value is simple, once we know how to copy an object *)
Definition copy' (v:val) (dest_heap:heap) : option (val*heap) 
  := match v with
       | Object oid => match (contains_dec src_heap oid) with
                           | left pf => copy'_part oid pf dest_heap
                           | right pf => None
                       end
       | GlobalObject p o => Some (GlobalObject p o,dest_heap)
       | Nat n =>  Some (Nat n,dest_heap)
     end.

Definition copy v dh := let 'tt := master_key in copy' v dh.
Lemma copy_simpl v dh : copy v dh = copy' v dh.
Proof. unfold copy; case master_key; reflexivity. Qed.

Ltac some_inv := match goal with
                     | [H:Some _ = Some _ |- _] => inversion H; subst; clear H
                 end.

Ltac destr :=
  match goal with
      [H: _ (@eq_refl ?A ?x) = _ |- _] => revert H; generalize (@eq_refl A x); 
                                          pattern x at 1 3; destruct x;
                                          intros; try discriminate
    | [H:@sig _ _ |- _ ] => destruct H
    | [H:prod _ _ |- _ ] => destruct H
    | [H:_ /\ _ |- _ ] => destruct H
    | [H: Some _ = Some _ |- _ ] => inversion H; clear H; try subst
  end; simpl in *.

Ltac dnewc := match goal with 
    [H: context [ new ?h ?v ] |- _ ] => 
    poses (new_fresh h v);
    poses (lookup_new1 h v);
    poses (lookup_new2 h v);
    poses (hincl_new h v);
    destruct (new h v)
end.

Hint Rewrite place_eqb_eq oid_eqb_eq : rewrite_eqs.

Lemma incl_nil : forall {A:Type} (l:list A), incl nil l.
Proof. red; intuition. Qed.

Hint Resolve incl_nil.

(* now we establish the properties we get from copy *)
Lemma copy_spec_some : forall v dest_heap v' h', copy v dest_heap = Some (v',h') -> 
                                                 hincl dest_heap h'
                                              /\ exists iso:(list (oid*oid)), 
                                                   good_map src_heap iso
                                                 /\   reach_list src_heap (domain iso) v
                                                 /\ incl (dom h') (domain (mswap iso) ++ (dom dest_heap))
                                                 /\ isIso src_heap h' iso = true
                                                 /\ inIso_val iso v v' = true.
Proof.
  Hint Resolve reach_list_nil incl_refl.
  destruct v; simpl; intros; rewrite copy_simpl in *; simpl in *; try some_inv;
  try solve[  intuition; eexists nil; autorewrite with rewrite_eqs; repeat split; simpl; eauto].

  destruct (contains_dec src_heap o); try discriminate.
  unfold copy'_part in *.
  case_eq (src_heap[@o]); [intros ? eq|intros eq]; rewrite eq in *; try discriminate.
  dnewc.
  case_eq (locked_copy_obj_base src_heap
          (exist (good_map src_heap) ((o, o1)::nil) (good_map_singleton o o1 c),
          o0) h); [intros ? eq2|intros eq2]; rewrite eq2 in H; try discriminate.
  destruct p as [[??] ?].
  apply locked_copy_obj_base_spec in eq2.
  unfold copy_obj_spec in *; simpl in *.

  inversion H; subst; clear H.
  unfold update_if.
  destruct (contains_dec h0 o1).
  - intuition.
    + intros i vi ii.
      rewrite lookup_update2 by congruence. eauto.
    + exists ((o,o1)::l); intuition.
      * rewrite Permutation_app_swap in H. simpl in H. trivial.
      * Hint Constructors reachable_from.
        unfold reach_list, reach_list_obj in *. simpl. intuition; subst; eauto.
        destruct (H1 _ H6) as [?[?[??]]].
        eauto.
      * rewrite dom_update. 
        unfold incl in *; intros.
        specialize (H3 _ H4).
        autorewrite with rewrites in * |- *. simpl in *.
        app_tac; intuition.
        app_tac; simpl in *; intuition.
        destruct (a == o1); unfold equiv, complement in *; subst; [intuition|].
        right. apply in_app_iff; right.
        rewrite dom_lookup in H6. destruct H6.
        eapply dom_lookup. eexists.
        rewrite <- P1; eauto.
      * unfold isIso. 
        change  (inIso_map src_heap (update h0 o1 c0 o2) ((o, o1) :: l) (((o, o1) :: nil) ++ l) =
                 true).
        apply inIso_map_app.
          simpl. unfold inIso_oids; simpl.
          rewrite eq. rewrite lookup_update1. erewrite inIso_obj_lincl; eauto.
          destruct H as [[??]?]. apply lincl_perm; eauto.  apply Permutation_app_swap.
          rewrite inIso_map_sym. rewrite inIso_map_nin_update1. rewrite <- inIso_map_sym.
          eapply inIso_map_lincl1; [|eassumption].
            apply lincl_perm. destruct H as [[??]?]; auto.
            apply Permutation_app_swap.
            destruct H; rewrite Permutation_app_swap in H; simpl in H; trivial.
            destruct H as [[??]?].
            rewrite mswap_app, domain_app in H4.
            apply NoDup_app_dis in H4.
            intro nin. apply (H4 o1 nin).
            simpl; intuition.
            destruct H; rewrite Permutation_app_swap in H; simpl in H; trivial.
      * rewrite lookup_cons_eq; t.
 - elim n. intuition. specialize (H2 _ _ P0). red; eauto.
 - red; simpl. intuition; subst. apply dom_lookup; red; eauto.
Qed.

(* if copy fails, then we can produce a witness showing that the object graph rooted at the source node
   has a dangling reference *)
Lemma copy_spec_none : forall v dest_heap,
                         copy v dest_heap = None ->
                         exists ret:oid, 
                           reachable_from src_heap v (Object ret)
                         /\ ~ contains src_heap ret.
Proof.
  destruct v; simpl; intros; rewrite copy_simpl in *; simpl in *; try discriminate. 
  case_eq (contains_dec src_heap o); [intros ? eq1|intros ? eq1]; rewrite eq1 in H.
  - unfold copy'_part in *.
    case_eq (src_heap[@o]); [intros ? eq2|intros eq2]; rewrite eq2 in H.
    + dnewc. unfold locked_copy_obj_base in H. simpl in H.
      case_eq (incl_dec (o1::nil) (dom h)); [intros ? eq3|intros eq3].
      * rewrite eq3 in H.
        case_eq (locked_copy_obj src_heap
            (exist (good_map src_heap) ((o, o1)::nil) (good_map_singleton o o1 c),
            o0) h i); simpl in *; [intros s eq4|intros s eq4].
        rewrite eq4 in H; destruct s as [[[??]?]]; simpl in H; discriminate.
        destruct s as [?[??]]. destruct r as [?[?[??]]].
        eexists; split; [|eassumption]. econstructor; eauto.
      * elim eq3. red; simpl; intuition; subst. apply dom_lookup; red; eauto.
    + exists o; intuition. destruct H0. congruence.
  - eexists; intuition; eauto.
Qed.

Lemma copy_is_wf_src : forall dest_heap v v' h',
                         copy v dest_heap = Some (v',h') -> 
                         wf_val src_heap v.
Proof.
  intros.
  apply copy_spec_some in H; destruct H as [?[??]]; intuition; eapply iso_val_wf_src; eauto.
Qed.

Lemma copy_is_wf_dest : forall {dest_heap v v' h'},
                         copy v dest_heap = Some (v',h') -> 
                         wf_val h' v'.
Proof.
  intros.
  apply copy_spec_some in H; unfold good_map in H; destruct H as [?[??]]; intuition.
  eapply iso_val_wf_dest; eauto.
Qed.

Lemma copy_dest_reach : forall {dest_heap v v' h'},
                         copy v dest_heap = Some (v',h')
                         -> forall {a}, ~ contains dest_heap a
                                     -> contains h' a
                                     -> reachable_from h' v' (Object a).
Proof.
  intros.
  apply copy_spec_some in H; unfold good_map in H; destruct H as [?[??]]; intuition.
  poses (reach_list_iso H2 H3 H6 H8).
  apply (P a).
  apply dom_lookup in H1.
  poses (H4 _ H1).
  app_tac; intuition.
  apply dom_lookup in H7; intuition.
Qed.

Lemma copy_is_wf_dest_new : forall {dest_heap v v' h'},
                         copy v dest_heap = Some (v',h')
                         -> forall {a}, ~ contains dest_heap a
                                     -> contains h' a
                                     -> wf_val h' (Object a).
Proof.
  red; intros.
  poses (copy_is_wf_dest H).
  poses (copy_dest_reach H H0 H1).
  rewrite P0 in P.
  apply P; trivial.
Qed.

(* note that we need to prevent the trivial wf because not in heap case *)
Lemma wf_val_hincl_reach {h h' a} : hincl h h' -> wf_val h (Object a) ->
                              contains h a ->
                              forall oid, reachable_from h' (Object a) (Object oid)
                                          -> reachable_from h (Object a) (Object oid).
Proof.
  unfold wf_val.
  intros.
  revert H0 H1.
  dependent induction H2; simpl; intros.
  - eauto.
  - destruct (reachable_from_to_obj _ H2); subst. 
    destruct H4.
    poses (H _ _ H4).
    rewrite P in H1. inversion H1; subst; clear H1.    
    transitivity (Object x); [eauto|].
    apply IHreachable_from; eauto.
Qed.

Lemma wf_val_hincl {h h' a} : hincl h h' -> wf_val h (Object a) ->
                              contains h a -> wf_val h' (Object a).
Proof.
  unfold wf_val; intros.
  eapply hincl_contains; eauto.
  eapply H0.
  eapply wf_val_hincl_reach; eauto.
Qed.

Lemma copy_preserves_wd : forall {dest_heap v v' h'},
                         copy v dest_heap = Some (v',h')
                         -> forall {a}, wf_val dest_heap a
                                     -> wf_val h' a.
Proof.
  intros.
  apply copy_spec_some in H; destruct H as [?[??]]; intuition.
  destruct a; try solve[red; inversion 1].
  eapply wf_val_hincl; eauto.
Qed.  

Lemma copy_is_wf_dest_heap : forall {dest_heap v v' h'},
                            wf_heap dest_heap ->
                            copy v dest_heap = Some (v',h') -> 
                            wf_heap h'.
Proof.
  Hint Resolve copy_preserves_wd copy_is_wf_dest_new.
  red; intros.
  case_eq (contains_dec dest_heap a); intros eq1 pf; eauto.
Qed.

Lemma wf_can_copy : forall {v}, wf_val src_heap v ->
                              forall dest_heap, exists v' h',
                                copy v dest_heap = Some (v',h').
Proof.
  intros.
  case_eq (copy v dest_heap); t.
  apply copy_spec_none in H0.
  t.
Qed.  

End c.

(* since copy suceeds if and only if the source value is well formed in the source heap,
   the decidability (computability) of well-formedness for values is a corrollary of the definition of copy
*)
Lemma wf_val_dec h v : {wf_val h v} + {~ wf_val h v}.
Proof.
  case_eq (copy h v empty); [intros ? eq|intros eq].
  - destruct p. left. eapply copy_is_wf_src; eauto.
  - right. apply copy_spec_none in eq. t.
Qed.

(* We can provide a total copy operation for well formed values *)
Program Definition wf_copy (src_heap:heap) (v:val) (dest_heap:heap) (pf:wf_val src_heap v) : (val*heap) 
:= match copy src_heap v dest_heap with
       | Some x => x
       | None => _
   end.
Next Obligation.
assert False; intuition.
symmetry in Heq_anonymous. apply copy_spec_none in Heq_anonymous.
t.
Defined.

End copy_val.