(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Properties of the expression semantics for Resilient X10.  Includes many proporties from Section 4 of the paper. *)
Require Export ResilientSemantics.
Require Import Program.
Require Import Eqdep_dec.
Require Export StmtProps.
Require Import EvalExprProps.
Require Import HeapIsoReachExt.
Require Import Auxiliary2.
Require Import ListVector.
Require Export ResilientSemantics.
Require Import Arith.
Require Import Coq.Classes.EquivDec.

Section valid.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Definition countSome {A:Type} (a:option A) 
  := match a with
       | None => 0
       | Some _ => 1
     end.

Program Definition valid_places' {BOUND:nat} (g:list_vector (option heap) BOUND)
  := (fold_right (fun a b => countSome a + b) 0 g).

Program Definition valid_places (g:global_heap) 
  := valid_places' g.

End valid.

Section valid_props.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Lemma vector_lookup'_head {A:Type} {BOUND:nat} (a:A) l llen nlt :
  vector_lookup' BOUND (a::l) llen 0 nlt = a.
Proof.
  destruct BOUND; simpl; trivial.
Qed.

Lemma valid_places'_dec b g glen p :
   contains (exist (fun l : list (option heap) => length l = b) g glen) p ->
   valid_places' (exist (fun l : list (option heap) => length l = b) g glen)[p~~>None] <
   valid_places' (exist (fun l : list (option heap) => length l = b) g glen).
Proof.
  destruct p as [p plt].
  revert b glen p plt.
  induction g; unfold valid_places'; destruct b; simpl; intros; try omega.
  destruct p; simpl in *; destruct H; unfold lookup in H; simpl in H.
  * subst; simpl; omega.
  * apply plus_lt_compat_l.
    inversion glen. 
    assert (plt' : p  < b) by omega.
    apply (IHg _ H1 _ plt').
    exists x. 
    unfold lookup, vector_lookup.
    rewrite <- H. apply vector_lookup'_ext.
Qed.

Lemma valid_places_dec g p :
  contains g p ->
  valid_places g[p~~>None] < valid_places g.
Proof.
  unfold valid_places.
  destruct g as [g glen]. simpl.
  destruct p as [p plt].
  apply valid_places'_dec.
Qed.

Lemma valid_places'_update_some b g glen p h':
   contains (exist (fun l : list (option heap) => length l = b) g glen) p ->
   valid_places' (exist (fun l : list (option heap) => length l = b) g glen)[p~~>Some h'] =
   valid_places' (exist (fun l : list (option heap) => length l = b) g glen).
Proof.
  destruct p as [p plt].
  revert b glen p plt.
  induction g; unfold valid_places'; destruct b; simpl; intros; try omega.
  destruct p; simpl in *; destruct H; unfold lookup in H; simpl in H.
  * subst; simpl; omega.
  * f_equal.
    inversion glen. 
    assert (plt' : p  < b) by omega.
    apply (IHg _ H1 _ plt').
    exists x. 
    unfold lookup, vector_lookup.
    rewrite <- H. apply vector_lookup'_ext.
Qed.

Lemma valid_places_update_some {g p} h':
  contains g p ->
  valid_places g[p~~>Some h'] = valid_places g.
Proof.
  unfold valid_places.
  destruct g as [g glen]. simpl.
  destruct p as [p plt].
  apply valid_places'_update_some.
Qed.

Lemma valid_places_update_some' {g} {p} {h} h':
  Some h = g[@p] ->
  valid_places g[p~~>Some h'] = valid_places g.
Proof.
  intros. apply valid_places_update_some; eauto.
Qed.

End valid_props.

Section res_semantics_props.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Ltac eval_r_tac := 
  idtac; match goal with
(*
    | [H: _ || _ = true |- _] =>   apply orb_true_iff in H
    | [|- _ || _ = true ] =>   apply orb_true_iff
*)
    | [H: toAsyncTrans _ = ⊗ _ |- _] => destruct (toAsyncTrans_sync H)
    | [H: _ -e[ ?p | ?λ ]-> _ |- _ ] => poses (eval_e_ε H); try subst; try discriminate
  end.

Proposition eval_r_sync_fail_sync {p s g k ve} : (s,g) -r[p|⊗ ve]->? k -> isSync s = true.
Proof.
  intros ev.
  dependent induction ev; dts eval_r_tac;
  try (destruct (transCopy_sync H1); eauto);
  try (destruct λ; simpl in *; try discriminate; eauto).
Qed.

Proposition eval_r_sync_fail_async {p s g s' g' ve} : (s,g) -r[p|⊗ ve]-> (s',g') -> isAsync s' = true.
Proof.
  intros ev.
  dependent induction ev; dts eval_r_tac;
  try (destruct (transCopy_sync H1); eauto);
  try (destruct λ; simpl in *; try discriminate; eauto).  
Qed.

Proposition eval_r_async_to_async {p λ s g s' g'} : 
  (s,g) -r[p|λ]-> (s',g') ->
  isAsync s = true ->
  isAsync s' = true.
Proof.
  intros ev.
  dependent induction ev; dts eval_r_tac.
  - poses (eval_r_sync_fail_sync ev).
    rewrite isSync_not_isAsync in P; rewrite H0 in P.
    simpl in *; intuition.
  - poses (eval_r_sync_fail_sync ev).
    rewrite isSync_not_isAsync in P; rewrite H0 in P.
    simpl in *; intuition.
Qed.

Proposition eval_r_sync_from_sync {p λ s g s' g'} : 
  (s,g) -r[p|λ]-> (s',g') ->
  isSync s' = true ->
  isSync s = true.
Proof.
  intros ev iss.
  case_eq (isSync s); trivial; intros isa.
  rewrite isSync_not_isAsync in isa.
  rewrite negb_false_iff in isa.
  poses (eval_r_async_to_async ev isa).
  rewrite isSync_not_isAsync in iss.
  rewrite P in iss; simpl in iss.
  discriminate.
Qed.

Hint Rewrite free_vars_subst  : rewrites.
Lemma eval_r_reduces_fvars {p λ s g s' g'} : 
     (s,g) -r[p|λ]-> (s',g') 
  -> incl (free_vars s') (free_vars s).
Proof.
  unfold incl.
  intros ev; dependent induction ev; dt eval_r_tac;
  try match goal with 
      [H: (_, _) -e[_|_]-> (_,_) |- _ ] => rewrite (eval_e_preserves_free_vars H) in *
  end; trivial; try congruence; try rewrite in_app_iff in *; intuition.
  
  erewrite <- free_vars_subst; trivial; eauto.
Qed.

Lemma eval_r_preserves_topClosed {p λ s g s' g'} : 
     (s,g) -r[p|λ]-> (s',g') 
  -> isTopClosed s = true -> isTopClosed s' = true.
Proof.
  intros ev. unfold isTopClosed.
  dt idtac; unfold equiv in *; simpl in *.
  poses (eval_r_reduces_fvars ev).
  rewrite H in P; red in P; simpl in P.
  destruct (free_vars s'); simpl in P; trivial.
  elim (P v); intuition.
Qed.

Hint Rewrite topClosed_seq : rewrites.

Lemma eval_r_preserves_placeClosed {p λ s g s' g'} : 
     (s,g) -r[p|λ]-> (s',g') 
  -> isPlaceClosed s = true -> isPlaceClosed s' = true.
Proof.
  Hint Resolve eval_r_preserves_topClosed placeClosed_subst topAlmostClosed_subst_eq.
  intros ev; dependent induction ev; dt eval_r_tac; eauto;
    intuition; dt idtac.
Qed.

Lemma eval_r_preserves_closed {p λ s g s' g'} : 
     (s,g) -r[p|λ]-> (s',g') 
  -> isClosed s = true -> isClosed s' = true.
Proof.
  Hint Resolve eval_r_preserves_topClosed eval_r_preserves_placeClosed.
  unfold isClosed; dts idtac.
Qed.

Lemma eval_r_to_isSync{p λ s g s' g'} : 
     (s,g) -r[p|λ]-> (s',g') 
  -> isSync s' = true -> isSync s = true.
Proof.
  Hint Resolve eval_r_sync_fail_sync.
  intros ev; dependent induction ev; simpl; dt idtac; intuition; eauto 2.
Qed.

Hint Rewrite properStmt_subst: rewrites.

Lemma eval_r_preserves_properStmt {p λ s g s' g'} : 
     (s,g) -r[p|λ]-> (s',g') 
  -> properStmt s = true -> properStmt s' = true.
Proof.
  Hint Resolve staticOnly_properStmt.
  Hint Rewrite isAsync_not_isSync : rewrites.
  Ltac t_sync := idtac; repeat match goal with 
     | [H:context [if isSync ?s then _ else _] |- _] => case_eq (isSync s); let HH:=(fresh "iss") in intros HH; try rewrite HH in *
     | [|- context [if isSync ?s then _ else _]] => case_eq (isSync s); let HH:=(fresh "iss") in intros HH; try rewrite HH in *
     | [Hev: (?s, _) -r[ _ | _ ]-> (?s', _), Hsync: isSync ?s' = true |- _] => extend (eval_r_to_isSync Hev Hsync)
  end.

  intros ev; dependent induction ev; dt t_sync; intuition; try congruence.
  
  poses (IHev s0[v//x] g s' g'); simpl in *.
  rewrite properStmt_subst in P.
  eauto.
Qed.

Lemma eval_r_preserves_wfStmt {p λ s g s' g'} : 
     (s,g) -r[p|λ]-> (s',g') 
  -> wfStmt s = true -> wfStmt s' = true.
Proof.
  Hint Resolve eval_r_preserves_closed eval_r_preserves_properStmt.
  unfold wfStmt; dts idtac.
Qed.

Lemma eval_r_preserves_places_term p s g g' λ: (s, g) -r[p|λ]->! g' -> 
                                          forall q,
                                          contains g q <-> contains g' q.
Proof.
  Hint Resolve some_lookup_contains contains_update contains_update_back.
  intros ev.
  dependent induction ev; intuition eauto;
    unfold place; try solve[apply -> IHev; eauto | apply <- IHev; eauto].
  - apply contains_update, IHev; trivial.
  - apply IHev. eapply contains_update_back; try eassumption; eauto.
Qed.             

Lemma eval_r_preserves_places_b p s g s' g' λ: (s, g) -r[p|λ]-> (s', g') -> 
                                          forall q,
                                          contains g' q -> contains g q.
Proof.
  Hint Resolve some_lookup_contains contains_update contains_update_back.
  Hint Resolve eval_r_preserves_places_term.
  intros ev.
  dependent induction ev; intuition; unfold place in *;
    try solve[apply -> IHev; eauto 
           | apply <- IHev; eauto
           | apply -> eval_r_preserves_places_term; eauto
           | apply <- eval_r_preserves_places_term; eauto
           | eauto].
  - case_eq (p == q); unfold equiv, complement, contains in *; intros; subst.
    + rewrite lookup_update_eq in H0; dt idtac.
    + rewrite lookup_update_neq in H0; auto.
  - eapply contains_update_back; try eassumption; eauto.
  - apply IHev; eapply contains_update_back; try eassumption; eauto.
Grab Existential Variables.
destruct (contains_strengthen H); eauto.
Qed.


Theorem eval_r_term_valid_notincreasing {p λ s g g'} : 
     (s,g) -r[p | λ]->! g' 
  -> valid_places g' <= valid_places g.
Proof.
  Hint Resolve valid_places_update_some'.
  intros ev.
  dependent induction ev; intuition eauto; unfold place in *;
  try solve[erewrite valid_places_update_some'; eauto].
Qed.

Theorem eval_r_valid_notincreasing {p λ s g s' g'} : 
     (s,g) -r[p | λ]-> (s',g')
  -> valid_places g' <= valid_places g.
Proof.
  Hint Resolve  valid_places_dec eval_r_term_valid_notincreasing valid_places_update_some'.
  intros ev.
  dependent induction ev; intuition eauto; unfold place in *;
  try solve[erewrite valid_places_update_some'; eauto].  

  poses (valid_places_dec _ _ H); omega.
Qed.

Theorem eval_r_decreases_complexity {p λ s g s' g'} : 
  (s,g) -r[p | λ]-> (s', g') ->
     complexity_s s' < complexity_s s
  \/ valid_places g' < valid_places g.
Proof.
  Hint Resolve eval_r_valid_notincreasing eval_e_decreases_complexity.
  intros ev.
  dependent induction ev; unfold place in *;
    try solve[simpl; dt idtac; intuition; left; intuition eauto;
              match goal with
                  [H: _ -e[ p | λ ]-> _ |- _ ] => extend (eval_e_decreases_complexity H)
              end; try omega].
  - poses (IHev s0[v//x] g s' g'); intuition.
    left; dt omega.
  - simpl; dt idtac; intuition. 
    rewrite valid_places_update_some; eauto.
Qed.

Hint Resolve eval_r_decreases_complexity.

Require Import GloballyReachable.

Ltac hyp_app hyp :=
  match goal with
      [H: (?s, _) -r[ ?p | ?λ ]->? _ |- _] => solve[eapply (hyp p _ λ s); eauto 3; dt omega]
  end.

Ltac t s inv hyp := 
  destruct s; simpl in *; inversion inv; subst; simpl in *; 
  simpwf;
  dt idtac; 
  try solve[intuition; eauto 3| hyp_app hyp].



Lemma eval_r_term_preserves_gwf_val {g λ p q s g' v} :
  isPlaceClosed s = true ->
  (s,g) -r[p | λ]->! g' ->
  gwf_vals g (free_vals p s) ->
  gwf_val g q v ->
  gwf_val g' q v.
Proof.
  Hint Resolve complexity_s_0.

  Hint Resolve gwf_vals_free_vals_on_subst_f.
  Hint Resolve gwf_val_step_obj.
  Hint Resolve gwf_vals_incl_f.
  Hint Resolve gwf_vals_ghincl_f eval_e_term_ghincl.

  Hint Resolve incl_appl incl_refl.
  Hint Resolve eval_e_term_preserves_gwf_val.

  assert (ccs:{x : nat | complexity_s s <= x}) by eauto.
  destruct ccs as [c cs].
  revert p q λ s g g' v cs.
  induction c; intros; [assert False by eauto 3; intuition|].
  t s H0 IHc.
  - eapply gwf_val_update; eauto.
    eapply gwf_obj_field_update; eauto.
  - eapply gwf_val_ghincl_f.
    + eapply hincl_update_ghincl; eauto.
      eapply transCopy_hincl_eqs; eauto.
    + hyp_app IHc.
Qed.

Lemma some_update_none_b {g:global_heap} {r q h} :
  g[r~~>None][@q] = Some h-> 
  g[@q] = Some h.
Proof.
  destruct (q == r); unfold equiv, complement in *; subst.
  - rewrite lookup_update_eq; discriminate.
  - rewrite lookup_update_neq; eauto.
Qed.

Lemma contains_update_none_b {g:global_heap} {r q} :
  contains g[r~~>None] q -> 
  contains g q.
Proof.
  Hint Resolve some_update_none_b.
  destruct 1.
  eauto.
Qed.

Hint Resolve contains_update_none_b greach_refl.
Lemma greachable_from_none {g r p q a b} :
  greachable_from g[r~~>None] (p,a) (q,b) ->
  greachable_from g (p,a) (q,b).
Proof.
  Hint Resolve some_update_none_b. Hint Constructors greachable_from.
  intros gr.
  dependent induction gr; eauto.
Qed.

Lemma greach_contains_dest {g a p oid} :
  greachable_from g a (p, Object oid) ->
  contains g p.
Proof.
  intros.
  dependent induction H; trivial.
Qed.

Hint Resolve greach_contains_dest.

Lemma gwf_oid_to_none {g q o} p :
  gwf_val g q (Object o) -> 
  gwf_val g[p~~>None] q (Object o).
Proof.
  unfold gwf_val.  
  Hint Resolve greachable_from_none.
  intros.
  poses (greachable_from_none H0).
  destruct (H _ _ P) as [?[??]].
  destruct (greach_contains_dest H0).
  rewrite H3.
  unfold place in *;
  rewrite (some_update_none_b H3) in H1.
  dts idtac.
Qed.

Lemma gwf_val_to_none {g q v} p :
  gwf_val g q v -> 
  gwf_val g[p~~>None] q v.
Proof.
  Hint Resolve gwf_oid_to_none.
  destruct v; eauto.
  red; intros.
  inversion H0; subst.
  poses (greachable_from_none H0).
  destruct (H _ _ P) as [?[??]].
  destruct (greach_contains_dest H0).
  rewrite H4.
  unfold place in *;
  rewrite (some_update_none_b H4) in H1.
  dts idtac.
Qed.  

Lemma gwf_vals_to_none {g v} p :
  gwf_vals g v -> 
  gwf_vals g[p~~>None] v.
Proof.
  Hint Resolve gwf_val_to_none.
  unfold gwf_vals; eauto.
Qed.

Lemma eval_r_preserves_gwf_val {g λ p q s g' s' v} :
  isPlaceClosed s = true ->
  (s,g) -r[p | λ]-> (s',g') ->
  gwf_vals g (free_vals p s) ->
  gwf_val g q v ->
  gwf_val g' q v.
Proof.
  Hint Resolve complexity_s_0.

  Hint Resolve eval_r_term_preserves_gwf_val.
  Hint Resolve gwf_vals_free_vals_on_subst_f.
  Hint Resolve gwf_val_step_obj.
  Hint Resolve gwf_vals_incl_f.
  Hint Resolve eval_e_preserves_gwf_val.
  Hint Resolve gwf_val_to_none.


  Hint Resolve incl_appl incl_refl.
  assert (ccs:{x : nat | complexity_s s <= x}) by eauto.
  destruct ccs as [c cs].
  revert p q λ s g s' g' v cs.
  induction c; intros; [assert False by eauto; intuition|].
  t s H0 IHc.
  - eapply gwf_val_ghincl_f; eauto.
    eapply hincl_update_ghincl; eauto.
  - eapply gwf_val_ghincl_f.
    + eapply hincl_update_ghincl; eauto.
      eapply transCopy_hincl_eqs; eauto.
    + hyp_app IHc.
Qed.

Lemma eval_r_term_preserves_gwf_vals {g λ p s g' l} :
  isPlaceClosed s = true ->
  (s,g) -r[p | λ]->! g' ->
  gwf_vals g (free_vals p s) ->
  gwf_vals g l ->
  gwf_vals g' l.
Proof.
  intros; red; intros.
  eapply eval_r_term_preserves_gwf_val; eauto.
Qed.

Lemma eval_r_preserves_gwf_vals {g λ p s g' s' l} :
  isPlaceClosed s = true ->
  (s,g) -r[p | λ]-> (s',g') ->
  gwf_vals g (free_vals p s) ->
  gwf_vals g l ->
  gwf_vals g' l.
Proof.
  intros; red; intros.
  eapply eval_r_preserves_gwf_val; eauto.
Qed.

Ltac hyp_apps hyp :=
  match goal with
      [H: (?s, _) -r[ ?p | ?λ ]->? _ |- _] => solve[eapply (hyp p _ λ s); eauto 3; dts omega]
  end.

Ltac t2 s inv hyp := 
  destruct s; simpl in *; inversion inv; subst; simpl in *; 
  unfold FieldNotFoundException, BadPlaceException, BadTypeException, DeadPlaceException, MaskedException;
  unfold ptrans_vals in *; simpl in *;
  simpwf;
  dt idtac; 
  try solve[intuition; eauto 3| hyp_apps hyp].

Lemma gwf_vals_placed_toDP g p λ:
  gwf_vals g (placed_vals p (toDP λ)).
Proof.
  destruct λ; simpl; simpwf; unfold DeadPlaceException; eauto.
Qed.

Hint Resolve gwf_vals_placed_toDP.

Lemma gwf_vals_mask_trans {g v} p λ :
  gwf_val g p v -> 
  gwf_vals g (placed_vals p (trans_vals (mask_trans v λ))).
Proof.
  destruct λ; simpl; intros; simpwf; eauto.
Qed.

Hint Resolve gwf_vals_mask_trans.

Lemma eval_r_term_preserves_gwf_vals_trans {p λ s g g'} :
  isPlaceClosed s = true ->
  gwf_vals g (free_vals p s) ->
  (s,g) -r[p | λ]->! g' ->
  gwf_vals g' (ptrans_vals p λ).
Proof.
  Hint Resolve gwf_val_nat gwf_vals_nil eval_e_term_preserves_gwf_vals_trans.
  Hint Resolve gwf_val_ghincl_f.
  Hint Resolve eval_e_term_preserves_gwf_vals_trans_final.

  Hint Resolve gwf_vals_free_vals_subst_b.
  Hint Resolve complexity_s_0.
  Hint Resolve eval_r_term_preserves_gwf_vals.
  Hint Resolve eval_r_preserves_gwf_val.
  Hint Resolve eval_r_preserves_gwf_vals.
  Hint Resolve gwf_val_update gwf_obj_field_update.
  Hint Resolve gwf_val_to_none.

  assert (ccs:{x : nat | complexity_s s <= x}) by eauto.
  destruct ccs as [c cs].
  revert p λ s g g' cs.
  induction c; intros; [assert False by eauto; intuition|].
  t2 s H1 IHc.
 - eapply IHc; try eapply H10; eauto.
    rewrite complexity_s_subst; omega.
 - replace ve with (trans_vals (⊗ ve)) by reflexivity.
   eapply IHc; try eapply H9; dts omega.
 - simpwf; split; eauto 2.
   eapply IHc; try eapply H9; dts omega.
 - eapply IHc; try eapply H9; dts omega.
 - assert (gwf_vals g'0 (placed_vals p0 (trans_vals λ0)))
   by (eapply IHc; try eapply H8; dts omega).
   eapply  transCopy_gwf_vals; eauto.
 - eapply IHc; try eapply H5; dts omega.
Qed.

Lemma eval_r_preserves_gwf_vals_trans {p λ s g s' g'} :
  isPlaceClosed s = true ->
  gwf_vals g (free_vals p s) ->
  (s,g) -r[p | λ]-> (s',g') ->
  gwf_vals g' (ptrans_vals p λ).
Proof.
  Hint Resolve eval_r_term_preserves_gwf_vals_trans.
  Hint Resolve gwf_val_nat gwf_vals_nil eval_e_term_preserves_gwf_vals_trans.
  Hint Resolve gwf_val_ghincl_f.
  Hint Resolve eval_e_term_preserves_gwf_vals_trans_final.
  Hint Resolve eval_e_preserves_gwf_vals_trans_final.

  Hint Resolve gwf_vals_free_vals_subst_b.
  Hint Resolve complexity_s_0.
  Hint Resolve eval_r_term_preserves_gwf_vals.
  Hint Resolve eval_r_preserves_gwf_val.
  Hint Resolve eval_r_preserves_gwf_vals.
  Hint Resolve gwf_val_update gwf_obj_field_update.
  Hint Resolve gwf_val_to_none.

  assert (ccs:{x : nat | complexity_s s <= x}) by eauto.
  destruct ccs as [c cs].
  revert p λ s g s' g' cs.
  induction c; intros; [assert False by eauto; intuition|].
  t2 s H1 IHc.
 - eapply IHc; try eapply H11; eauto.
    rewrite complexity_s_subst; omega.
 - eapply IHc; try eapply H10; dts omega.
 - replace ve with (trans_vals (⊗ ve)) by reflexivity.
   eapply IHc; try eapply H5; dts omega.
 - eapply IHc; try eapply H10; dts omega.
 - eapply IHc; try eapply H10; dts omega.
 - assert (gwf_vals g'0 (placed_vals p0 (trans_vals λ0)))
   by (eapply IHc; try eapply H9; dts omega).
   eapply  transCopy_gwf_vals; eauto.
 - eapply IHc; try eapply H5; dts omega.
Qed.

Lemma gwf_oid_in_none g p o :
  gwf_val g[p~~>None] p (Object o).
Proof.
  red; intros.
  destruct (greach_contains_src _ H).
  unfold place in *.
  rewrite lookup_update_eq in H0. discriminate.
Qed.  

Lemma eval_r_preserves_gwf_vals_final {p λ s g s' g'} :
  isPlaceClosed s = true ->
  gwf_vals g (free_vals p s) ->
  (s,g) -r[p | λ]-> (s',g') ->
  gwf_vals g' (free_vals p s').
Proof.
  Hint Resolve eval_r_term_preserves_gwf_vals_trans.
  Hint Resolve gwf_val_nat gwf_vals_nil eval_e_term_preserves_gwf_vals_trans.
  Hint Resolve gwf_val_ghincl_f.
  Hint Resolve gwf_vals_ghincl_f.
  Hint Resolve eval_e_term_preserves_gwf_vals_trans_final.
  Hint Resolve eval_e_preserves_gwf_vals_trans_final.

  Hint Resolve gwf_vals_free_vals_subst_b.
  Hint Resolve complexity_s_0.
  Hint Resolve eval_r_term_preserves_gwf_vals.
  Hint Resolve eval_r_preserves_gwf_val.
  Hint Resolve eval_r_preserves_gwf_vals.
  Hint Resolve gwf_val_update gwf_obj_field_update.
  Hint Resolve eval_r_term_preserves_gwf_vals_trans.
  Hint Resolve eval_r_preserves_gwf_vals_trans.
  Hint Resolve eval_e_preserves_gwf_vals_final.
  Hint Resolve eval_e_ghincl.
  Hint Resolve gwf_val_to_none gwf_vals_to_none.

  assert (ccs:{x : nat | complexity_s s <= x}) by eauto.
  destruct ccs as [c cs].
  revert p λ s g s' g' cs.
  induction c; intros; [assert False by eauto; intuition|].
  t2 s H1 IHc.
 - eapply IHc; try eapply H11; eauto.
    rewrite complexity_s_subst; omega.
 - split. 
   + eapply IHc; try eapply H10; dts omega.
   + eapply eval_r_preserves_gwf_vals; try eapply H1; eauto 2;
     simpl; simpwf; dt idtac; auto.
 - eapply IHc; try eapply H5; dts omega.
 - split.
   + eapply eval_r_preserves_gwf_vals; try eapply H1; eauto 2;
     simpl; simpwf; dt idtac; auto.
   + eapply IHc; try eapply H10; dts omega.
 - intuition.
   eapply gwf_vals_free_vals_on_subst_f; eauto 2.
   + eapply copy_gwf_val; eauto.
   + eapply gwf_vals_ghincl_f; eauto 2.
     eapply hincl_update_ghincl; eauto 2.
 - split.
   + rewrite map_app; simpwf. split; eauto 2.
     change (gwf_vals g' (ptrans_vals p λ0)).
     eauto.
   + eapply IHc; try eapply H5; dts omega.
 - split; eauto 2.
   eapply IHc; try eapply H10; dts omega.
 - split; eauto 2.
   eapply IHc; try eapply H10; dts omega.
 -  eapply IHc; try eapply H10; dts omega.
 - eapply gwf_vals_ghincl_f.
   + eapply hincl_update_ghincl; eauto 2.
     eapply transCopy_hincl_eqs; eauto.
   + eapply IHc; try eapply H9; dts omega.
 - eapply IHc; try eapply H10; dts omega.
 - eapply IHc; try eapply H11; dts omega.
 - eapply IHc; try eapply H5; dts omega.
Qed.

Lemma lookup_none_ncontains {g:global_heap} {p} :
  g[@p]=None ->
  ~ contains g p.
Proof.
  unfold contains; intros; destruct 1; congruence.
Qed.

Hint Resolve lookup_none_ncontains.

Lemma some_ncont_false {g1:global_heap} {p h} :
  Some h = g1[@p] -> (contains g1 p -> False) -> False.
Proof.
  unfold contains; eauto.
Qed.

Lemma eval_r_at_pfail {vs p s1 g1 sg'} :
  ~ contains g1 p -> 
  (s1, g1) -r[ p | ⊗ vs ]->? sg' -> 
  vs = (singleton DeadPlaceException).
Proof.
  Hint Resolve eval_r_preserves_places_b.
  Hint Resolve some_ncont_false.
  assert (ccs:{x : nat | complexity_s s1 <= x}) by eauto.
  destruct ccs as [c cs].
  revert vs p s1 g1 sg' cs.
  induction c; intros; [assert False by eauto; intuition|].
  t2 s1 H0 IHc; unfold place in *;
  try match goal with
      [H0:Some _ = ?g[@ ?p], H1:contains g1 p -> False |- _] => elim (some_ncont_false H0 H1)
  end.
  - eapply IHc; try eapply H7; dts omega.
  - eapply IHc; try eapply H8; dts omega.
  - eapply IHc; try eapply H8; dts omega.
  - destruct (trans_vals λ ++ l); simpl in *; try discriminate.
    inversion H1; auto.
  - elim H. eapply eval_r_preserves_places_b; eauto.
  - elim H. eapply eval_r_preserves_places_term; eauto.
  - destruct λ; simpl in *; try discriminate.
    inversion H1. auto.
  - destruct λ; simpl in *; try discriminate.
    inversion H1. auto.
  - destruct λ; simpl in *; try discriminate.
  - destruct λ; simpl in *; try discriminate.
Qed.

(* The resilient calculus is total even if the global heap is partial *)
Theorem eval_r_total p s1 g1 : 
  wfStmt s1 = true -> 
  gwf_vals g1 (free_vals p s1) ->
  { λ:trans_type & {s2g2 | (s1,g1) -r[p | λ]->? s2g2}}.
Proof.
  Hint Resolve complexity_s_0.
  assert (ccs:{x : nat | complexity_s s1 <= x}) by eauto.
  destruct ccs as [c cs].
  revert p g1 s1 cs.
  induction c; intros; [assert False by eauto; intuition|].

Hint Resolve eval_e_total some_lookup_contains.
Hint Resolve gwf_vals_free_vals_on_subst_f.
Hint Resolve gwf_val_wf.

Hint Constructors eval_r.
Hint Resolve ERSkip ERThrowCtxt ERThrowCtxtTerm ERBindCtxt ERBindCtxtTerm ERUpdateCtxt1 ERUpdateCtxt1Term ERUpdateCtxt2 ERUpdateCtxt2Term ERAtCtxt ERAtCtxtTerm EAt EDAt EDAtTerm ERDAsync ERDAsyncTerm ERSkipPFail ERThrowPFail ERBindPFail ERUpdatePFail ERAsyncPFail ERFinishTermPFail ESeq1TermPFailSync ESeq1TermPFailASync EAtPFailThere EAtPFailHere EDAtTermPFailHere EDAtTermPFailThere ECatchFailPFail ECatchFailTermPFail.

Ltac discval e :=
  case_eq (isVal e); intros;
  try match goal with
    | [H: isVal ?f = true |- _ ] => apply isVal_true in H; destruct H; subst
  end.
Ltac simplwf := 
  unfold wfStmt, isClosed, isTopClosed in *; simpl in *; dt idtac; unfold equiv in *;
  repeat match goal with
           |  [H:gwf_vals _ (_::_) |- _] => rewrite gwf_vals_cons_eq in H; destruct H
           | [H:gwf_vals _ (_ ++_) |- _] => rewrite gwf_vals_app_eq in H; destruct H
           | [H:gwf_vals _ (singleton _) |- _] => rewrite gwf_vals_singleton in H
           | [|- gwf_vals _ (_::_) ] => rewrite gwf_vals_cons_eq
           | [|- gwf_vals _ (_ ++_)] => rewrite gwf_vals_app_eq
           | [H: _ ++ _ = nil |- _ ] => apply app_eq_nil in H; destruct H
       end.
  destruct s1; simpl in *; simplwf; case_eq(g1[@p]); eauto.
  (* Seq *)
  - destruct (IHc p g1 s1_1) as [λ [sg' ev']]; dts omega.
    case_eq (isSyncTrans λ); eauto.
    + destruct λ; simpl; intuition; eauto.
      destruct sg' as [[s' g']|g']; eauto.
      case_eq (isSync s1_1); eauto.
      intros isa.
      rewrite isSync_not_isAsync in isa.
      rewrite ->  negb_false_iff in isa.
      eauto.
    + destruct sg' as [[s' g']|g']; eauto.
      case_eq (isSync s1_1); eauto.
      intros isa.
      rewrite isSync_not_isAsync in isa.
      rewrite ->  negb_false_iff in isa.
      eauto.
 (* Finish *)
  - destruct (IHc p g1 s1) as [λ [[[s' g']|g'] ev']]; dts omega.
  (* Catch *)
  - destruct (IHc p g1 s1_1) as [λ [sg' ev']]; dt ltac:(intuition; eauto 2; try omega).
    assert (ncont:~ contains g1 p) by eauto.
    + case_eq (isSyncTrans λ); [|destruct sg' as [[s' g']|g']; eauto;
    destruct λ; simpl; intuition; eauto].
      destruct λ; simpl; intuition.
      poses (eval_r_at_pfail ncont ev'); subst.
      destruct sg' as [[s' g']|g']; eauto.
  - destruct (IHc p0 g1 s1) as [λ [[[s' g']|g'] ev']]; dts omega.
  - destruct (IHc p g1 s1) as [λ [[[s' g']|g'] ev']]; dts omega.
Qed.

Require Import WfUtil.
Require Import Coq.Arith.Wf_nat.

Lemma eval_r_wf_pair_pb {p λ s g s' g'} : 
  (s,g) -r[p | λ]-> (s', g') ->
  wf_pair_pb lt lt valid_places complexity_s (g',s') (g,s).
Proof.
  intros ev.
  poses (eval_r_decreases_complexity ev).
  poses (eval_r_valid_notincreasing ev).
  repeat red; simpl.
  intuition omega.
Qed.

Lemma wfStmt_is_place_closes {s} :
  wfStmt s = true ->
  isPlaceClosed s = true.
Proof.
  unfold wfStmt, isClosed; dt idtac.
Qed.

Lemma eval_r_star_total_pair p g1s1 : 
  wfStmt (snd g1s1) = true -> 
  gwf_vals (fst g1s1) (free_vals p (snd g1s1)) ->
    {g2 | (swap g1s1) -r[p | ε]->*! g2}
  + { vs:list val & {s2g2 | (swap g1s1) -r[p | ⊗ vs]->*? s2g2}}
  + { vs:list val & {s2g2 | (swap g1s1) -r[p | × vs]->*? s2g2}}.
Proof.
  Hint Resolve eval_r_eval_r_star eval_r_star_trans eval_r_star_refl.
  Hint Resolve complexity_s_0.
  Hint Resolve wfStmt_is_place_closes.
  Hint Resolve eval_r_preserves_gwf_vals_final.

  revert p.
  pattern g1s1.
  apply (@well_founded_induction_type _ _
  (@wf_pair_pb_wf nat nat lt lt global_heap stmt valid_places complexity_s lt_wf lt_wf)); trivial.
  clear g1s1.
  intros.
  destruct x as [g s]; simpl in *.
  unfold swap in *; simpl in *.
  destruct (eval_r_total p s g) as [λ [s2g2 ev]]; eauto 2.
  destruct λ; intuition eauto.
  destruct s2g2 as [[s2 g2]|g2]; eauto.
  poses (eval_r_wf_pair_pb ev).
  Hint Resolve eval_r_preserves_wfStmt.
  destruct (X _ P p) as [[[g3 ev']|[vs [s3g3 ev']]]|[vs [s3g3 ev']]]; simpl in *;
    intuition eauto.
Qed.

(* Any well formed statement and global heap can be evaluated until it either terminates
  in a final heap with no exceptions, or generates an (uncaught) exception *)
Theorem eval_r_star_total p s1 g1 : 
  wfStmt s1 = true -> 
  gwf_vals g1 (free_vals p s1) ->
    {g2 | (s1,g1) -r[p | ε]->*! g2}
  + { vs:list val & {s2g2 | (s1,g1) -r[p | ⊗ vs]->*? s2g2}}
  + { vs:list val & {s2g2 | (s1,g1) -r[p | × vs]->*? s2g2}}.
Proof.
  intros wf gwf.
  poses (eval_r_star_total_pair p (g1,s1)).
  simpl in P.
  auto.
Qed.

Lemma eval_r_finish_nasync_trans {p μ vs s g s2g2} :
        (Finish μ s,g) -r[p|× vs]->? s2g2 -> False.
Proof.
  Hint Resolve asSyncTrans_nasync.
  inversion 1; eauto.
Qed.
  
Lemma eval_r_star_finish_to_finish {p μ s g s' g'} :
  (Finish μ s, g) -r[ p | ε ]->* (s', g') ->
  exists s'' l, s' = Finish l s''.
Proof.
  intros ev. 
  apply eval_r_star_eval_r_star_left in ev.
  dependent induction ev; eauto.
  inversion H; subst; eauto.
Qed.

Lemma eval_r_star_finish_nasync_trans {p μ vs s g s2g2} :
        (Finish μ s,g) -r[p|× vs]->*? s2g2 -> False.
Proof.
  intros ev.
  dependent induction ev.
  destruct sg'.
  destruct (eval_r_star_finish_to_finish ev) as [s' [l' ev']]; subst.
  eapply eval_r_finish_nasync_trans; eauto.
Qed.

Lemma eval_r_star_total_finish p s1 g1 : 
  wfStmt s1 = true -> 
  gwf_vals g1 (free_vals p s1) ->
    {g2 | (Finish List.nil s1,g1) -r[p | ε]->*! g2}
  + { vs:list val & {s2g2 | (Finish List.nil s1,g1) -r[p | ⊗ vs]->*? s2g2}}.
Proof.
  Hint Resolve eval_r_finish_nasync_trans.
  intros.
  destruct (eval_r_star_total p (Finish List.nil s1) g1); eauto 2.
  destruct s as [?[? ev]].
  assert False; intuition.
  eapply eval_r_star_finish_nasync_trans; eauto.
Qed.

End res_semantics_props.
