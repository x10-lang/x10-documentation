(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Properties of the statement semantics for TX10, including many properties from Section 2 of the paper *)
Require Export Semantics.
Require Import Program.
Require Import Eqdep_dec.
Require Export StmtProps.
Require Import EvalExprProps.
Require Import HeapIsoReachExt.
Require Import Lt.
Require Import Auxiliary2.
Require Import ECtxt.
Require Import HeapEvolve.

Section eval_stmt_props.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Ltac eval_stmt_tac := 
  idtac; match goal with
(*
    | [H: _ || _ = true |- _] =>   apply orb_true_iff in H
    | [|- _ || _ = true ] =>   apply orb_true_iff
*)
    | [H: toAsyncTrans _ = ⊗ _ |- _] => destruct (toAsyncTrans_sync H)
    | [H: _ -e[ ?p | ?λ ]-> _ |- _ ] => poses (eval_e_ε H); try subst; try discriminate
    | [H: _ -e[ _ | × _ ]->? _ |- _ ] => elim (eval_e_not_async H)
  end.

Proposition eval_stmt_sync_fail_sync {p s g k ve} : (s,g) -[p|⊗ ve]->? k -> isSync s = true.
Proof.
  intros ev.
  dependent induction ev; dts eval_stmt_tac;
  destruct (transCopy_sync H1); eauto.
Qed.

Proposition eval_stmt_sync_fail_async {p s g s' g' ve} : (s,g) -[p|⊗ ve]-> (s',g') -> isAsync s' = true.
Proof.
  intros ev.
  dependent induction ev; dts eval_stmt_tac.
  destruct (transCopy_sync H1); eauto.  
Qed.

Proposition eval_stmt_async_to_async {p λ s g s' g'} : 
  (s,g) -[p|λ]-> (s',g') ->
  isAsync s = true ->
  isAsync s' = true.
Proof.
  intros ev.
  dependent induction ev; dts eval_stmt_tac.
  - poses (eval_stmt_sync_fail_sync ev).
    rewrite isSync_not_isAsync in P; rewrite H0 in P.
    simpl in *; intuition.
  - poses (eval_stmt_sync_fail_sync ev).
    rewrite isSync_not_isAsync in P; rewrite H0 in P.
    simpl in *; intuition.
Qed.

Proposition eval_stmt_sync_from_sync {p λ s g s' g'} : 
  (s,g) -[p|λ]-> (s',g') ->
  isSync s' = true ->
  isSync s = true.
Proof.
  intros ev iss.
  case_eq (isSync s); trivial; intros isa.
  rewrite isSync_not_isAsync in isa.
  rewrite negb_false_iff in isa.
  poses (eval_stmt_async_to_async ev isa).
  rewrite isSync_not_isAsync in iss.
  rewrite P in iss; simpl in iss.
  discriminate.
Qed.

(* Note that we cannot guarantee it is the same exception list, since 
   it might actually be a copy of that exceptions *)
Proposition eval_stmt_async_fail_async_ctxt {p ve s g k} :
  properStmt s = true ->
  (s,g) -[p|× ve]->? k ->
  exists EC s' k' ve' r,    s = eplug EC s'
                /\ isAsync s' = true
                /\ (s',g) -[r|× ve']->? k'.
Proof.
  Hint Constructors eval.
  intros ps ev.
  dependent induction ev; dt eval_stmt_tac.
  (* The case for Bind cannot happen, because of the properStmt restriction *)
  - rewrite <- (staticOnly_subst _ x v) in ps.
    edestruct (IHev _ (s0[v//x]) _ (staticOnly_properStmt ps) (eq_refl _) (eq_refl _)); dt idtac.
    rewrite H0 in ps.
    apply staticOnly_eplug in ps.
    apply staticOnly_isSync in ps.
    rewrite isSync_not_isAsync in ps.
    rewrite H1 in ps; simpl in ps.
    discriminate.
  - rewrite <- (staticOnly_subst _ x v) in ps.
    edestruct (IHev _ (s0[v//x]) _ (staticOnly_properStmt ps) (eq_refl _) (eq_refl _)); dt idtac.
    rewrite H0 in ps.
    apply staticOnly_eplug in ps.
    apply staticOnly_isSync in ps.
    rewrite isSync_not_isAsync in ps.
    rewrite H1 in ps; simpl in ps.
    discriminate.
  - exists ECHole; simpl. do 2 eexists; intuition. exists ve.
    rewrite <- x. eauto.
  - exists ECHole; simpl. do 2 eexists; intuition. exists ve.
    rewrite <- x. eauto.
  - destruct (trans_vals λ ++ μ); simpl in *; discriminate.
  - edestruct IHev; eauto; dt idtac.
    exists ((ECSeq1 x t)); do 3 eexists; simpl; eauto.
  - edestruct IHev; eauto; dt idtac.
    exists ((ECSeq1 x t)); do 3 eexists; simpl; eauto.
  - rewrite isSync_not_isAsync,H in H1; simpl in H1.
    edestruct IHev; eauto; dt idtac.
    exists ((ECSeq2 s0 H x)); do 3 eexists; simpl; eauto.
  - rewrite isSync_not_isAsync,H in H1; simpl in H1.
    edestruct IHev; eauto; dt idtac.
    exists ((ECSeq2 s0 H x)); do 3 eexists; simpl; eauto.
  - destruct (transCopy_async H1); subst.
    edestruct IHev; eauto; dt idtac.
    exists ((ECDAt p x0)); exists x1; do 2 eexists; simpl; eauto.
  - destruct (transCopy_async H1); subst.
    edestruct IHev; eauto; dt idtac.
    exists ((ECDAt p x0)); exists x1; do 2 eexists; simpl; eauto.
  - edestruct IHev; eauto; dt idtac.
    exists ((ECCatch x t)); do 3 eexists; simpl; eauto.
  - edestruct IHev; eauto; dt idtac.
    exists ((ECCatch x t)); do 3 eexists; simpl; eauto.
Qed.

Hint Rewrite free_vars_subst  : rewrites.
Lemma eval_stmt_reduces_fvars {p λ s g s' g'} : 
     (s,g) -[p|λ]-> (s',g') 
  -> incl (free_vars s') (free_vars s).
Proof.
  unfold incl.
  intros ev; dependent induction ev; dt eval_stmt_tac;
  try match goal with 
      [H: (_, _) -e[_|_]-> (_,_) |- _ ] => rewrite (eval_e_preserves_free_vars H) in *
  end; trivial; try congruence; try rewrite in_app_iff in *; intuition.
  
  erewrite <- free_vars_subst; trivial; eauto.
Qed.

Lemma eval_stmt_preserves_topClosed {p λ s g s' g'} : 
     (s,g) -[p|λ]-> (s',g') 
  -> isTopClosed s = true -> isTopClosed s' = true.
Proof.
  intros ev. unfold isTopClosed.
  dt idtac; unfold equiv in *; simpl in *.
  poses (eval_stmt_reduces_fvars ev).
  rewrite H in P; red in P; simpl in P.
  destruct (free_vars s'); simpl in P; trivial.
  elim (P v); intuition.
Qed.

Hint Rewrite topClosed_seq : rewrites.

Lemma eval_stmt_preserves_placeClosed {p λ s g s' g'} : 
     (s,g) -[p|λ]-> (s',g') 
  -> isPlaceClosed s = true -> isPlaceClosed s' = true.
Proof.
  Hint Resolve eval_stmt_preserves_topClosed placeClosed_subst topAlmostClosed_subst_eq.
  intros ev; dependent induction ev; dt eval_stmt_tac; eauto;
    intuition; dt idtac.
Qed.

Lemma eval_stmt_preserves_closed {p λ s g s' g'} : 
     (s,g) -[p|λ]-> (s',g') 
  -> isClosed s = true -> isClosed s' = true.
Proof.
  Hint Resolve eval_stmt_preserves_topClosed eval_stmt_preserves_placeClosed.
  unfold isClosed; dts idtac.
Qed.

Lemma eval_stmt_to_isSync{p λ s g s' g'} : 
     (s,g) -[p|λ]-> (s',g') 
  -> isSync s' = true -> isSync s = true.
Proof.
  Hint Resolve eval_stmt_sync_fail_sync.
  intros ev; dependent induction ev; simpl; dt idtac; intuition; eauto 2.
Qed.

Hint Rewrite properStmt_subst: rewrites.

Lemma eval_stmt_preserves_properStmt {p λ s g s' g'} : 
     (s,g) -[p|λ]-> (s',g') 
  -> properStmt s = true -> properStmt s' = true.
Proof.
  Hint Resolve staticOnly_properStmt.
  Hint Rewrite isAsync_not_isSync : rewrites.
  Ltac t_sync := idtac; repeat match goal with 
     | [H:context [if isSync ?s then _ else _] |- _] => case_eq (isSync s); let HH:=(fresh "iss") in intros HH; try rewrite HH in *
     | [|- context [if isSync ?s then _ else _]] => case_eq (isSync s); let HH:=(fresh "iss") in intros HH; try rewrite HH in *
     | [Hev: (?s, _) -[ _ | _ ]-> (?s', _), Hsync: isSync ?s' = true |- _] => extend (eval_stmt_to_isSync Hev Hsync)
  end.

  intros ev; dependent induction ev; dt t_sync; intuition; try congruence.
  
  poses (IHev s0[v//x] g s' g'); simpl in *.
  rewrite properStmt_subst in P.
  eauto.
Qed.

Lemma eval_stmt_preserves_wfStmt {p λ s g s' g'} : 
     (s,g) -[p|λ]-> (s',g') 
  -> wfStmt s = true -> wfStmt s' = true.
Proof.
  Hint Resolve eval_stmt_preserves_closed eval_stmt_preserves_properStmt.
  unfold wfStmt; dts idtac.
Qed.

Lemma eval_preserves_places_term p s g g' λ: (s, g) -[p|λ]->! g' -> 
                                          forall q,
                                          contains g q <-> contains g' q.
Proof.
  Hint Resolve some_lookup_contains contains_update contains_update_back.
  intros ev.
  dependent induction ev; intuition eauto;
    unfold place in *; try solve[apply -> IHev; eauto | apply <- IHev; eauto].
  - apply contains_update, IHev; trivial.
  - apply <- IHev. eapply contains_update_back; [|eassumption]. eauto.
Qed.             

Lemma eval_preserves_places p s g s' g' λ: (s, g) -[p|λ]-> (s', g') -> 
                                          forall q,
                                          contains g q <-> contains g' q.
Proof.
  Hint Resolve some_lookup_contains contains_update contains_update_back.
  Hint Resolve eval_preserves_places_term.
  intros ev.
  dependent induction ev; intuition;
    try solve[apply -> IHev; eauto 
           | apply <- IHev; eauto
           | apply -> eval_preserves_places_term; eauto
           | apply <- eval_preserves_places_term; eauto
           | eauto].
  - eapply contains_update_back; try eassumption; eauto.
  - apply contains_update; apply -> IHev; eauto.
  - apply IHev. eapply contains_update_back; try eassumption; eauto.
Qed.

Theorem eval_decreases_complexity {p λ s g s' g'} : 
  (s,g) -[p | λ]-> (s', g') -> complexity_s s' < complexity_s s.
Proof.
  Hint Resolve eval_e_decreases_complexity.
  intros ev.
  dependent induction ev; try solve[simpl; dt idtac; eauto;
  try match goal with
      [H: _ -e[ p | λ ]-> _ |- _ ] => extend (eval_e_decreases_complexity H)
  end; try omega].
  
  simpl; apply lt_S. poses (IHev s0[v//x] g s' g'). dt idtac; eauto.
Qed.

Hint Resolve eval_decreases_complexity.

Require Import GloballyReachable.


Ltac hyp_app hyp :=
  match goal with
      [H: (?s, _) -[ ?p | ?λ ]->? _ |- _] => solve[eapply (hyp p _ λ s); eauto 3; dt omega]
  end.

Ltac t s inv hyp := 
  destruct s; simpl in *; inversion inv; subst; simpl in *; 
  simpwf;
  dt idtac; 
  try solve[intuition; eauto 3| hyp_app hyp].


Lemma eval_term_preserves_gwf_val {g λ p q s g' v} :
  isPlaceClosed s = true ->
  (s,g) -[p | λ]->! g' ->
  gwf_vals g (free_vals p s) ->
  gwf_val g q v ->
  gwf_val g' q v.
Proof.
  Hint Resolve complexity_s_0.

  Hint Resolve  gwf_vals_free_vals_on_subst_f.
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

Lemma eval_preserves_gwf_val {g λ p q s g' s' v} :
  isPlaceClosed s = true ->
  (s,g) -[p | λ]-> (s',g') ->
  gwf_vals g (free_vals p s) ->
  gwf_val g q v ->
  gwf_val g' q v.
Proof.
  Hint Resolve complexity_s_0.

  Hint Resolve eval_term_preserves_gwf_val.
  Hint Resolve  gwf_vals_free_vals_on_subst_f.
  Hint Resolve gwf_val_step_obj.
  Hint Resolve gwf_vals_incl_f.
  Hint Resolve eval_e_preserves_gwf_val.


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

Lemma eval_term_preserves_gwf_vals {g λ p s g' l} :
  isPlaceClosed s = true ->
  (s,g) -[p | λ]->! g' ->
  gwf_vals g (free_vals p s) ->
  gwf_vals g l ->
  gwf_vals g' l.
Proof.
  intros; red; intros.
  eapply eval_term_preserves_gwf_val; eauto.
Qed.

Lemma eval_preserves_gwf_vals {g λ p s g' s' l} :
  isPlaceClosed s = true ->
  (s,g) -[p | λ]-> (s',g') ->
  gwf_vals g (free_vals p s) ->
  gwf_vals g l ->
  gwf_vals g' l.
Proof.
  intros; red; intros.
  eapply eval_preserves_gwf_val; eauto.
Qed.

Ltac hyp_apps hyp :=
  match goal with
      [H: (?s, _) -[ ?p | ?λ ]->? _ |- _] => solve[eapply (hyp p _ λ s); eauto 3; dts omega]
  end.

Ltac t2 s inv hyp := 
  destruct s; simpl in *; inversion inv; subst; simpl in *; 
  unfold FieldNotFoundException, BadPlaceException, BadTypeException;
  unfold ptrans_vals in *; simpl in *;
  simpwf;
  dt idtac; 
  try solve[intuition; eauto 3| hyp_apps hyp].

Lemma eval_term_preserves_gwf_vals_trans {p λ s g g'} :
  isPlaceClosed s = true ->
  gwf_vals g (free_vals p s) ->
  (s,g) -[p | λ]->! g' ->
  gwf_vals g' (ptrans_vals p λ).
Proof.
  Hint Resolve gwf_val_nat gwf_vals_nil eval_e_term_preserves_gwf_vals_trans.
  Hint Resolve gwf_val_ghincl_f.
  Hint Resolve eval_e_term_preserves_gwf_vals_trans_final.

  Hint Resolve gwf_vals_free_vals_subst_b.
  Hint Resolve complexity_s_0.
  Hint Resolve eval_term_preserves_gwf_vals.
  Hint Resolve eval_preserves_gwf_val.
  Hint Resolve eval_preserves_gwf_vals.
  Hint Resolve gwf_val_update gwf_obj_field_update.
  assert (ccs:{x : nat | complexity_s s <= x}) by eauto.
  destruct ccs as [c cs].
  revert p λ s g g' cs.
  induction c; intros; [assert False by eauto; intuition|].
  t2 s H1 IHc.
 - eapply IHc; try eapply H10; eauto.
    rewrite complexity_s_subst; omega.
 - replace ve with (trans_vals (⊗ ve)) by reflexivity.
   eapply IHc; try eapply H8; dts omega.
 - simpwf; split; eauto 2.
   eapply IHc; try eapply H5; dts omega.
 - eapply IHc; try eapply H10; dts omega.
 - assert (gwf_vals g'0 (placed_vals p0 (trans_vals λ0)))
   by (eapply IHc; try eapply H8; dts omega).
   eapply  transCopy_gwf_vals; eauto.
 - eapply IHc; try eapply H5; dts omega.
Qed.

Lemma eval_preserves_gwf_vals_trans {p λ s g s' g'} :
  isPlaceClosed s = true ->
  gwf_vals g (free_vals p s) ->
  (s,g) -[p | λ]-> (s',g') ->
  gwf_vals g' (ptrans_vals p λ).
Proof.
  Hint Resolve eval_term_preserves_gwf_vals_trans.
  Hint Resolve gwf_val_nat gwf_vals_nil eval_e_term_preserves_gwf_vals_trans.
  Hint Resolve gwf_val_ghincl_f.
  Hint Resolve eval_e_term_preserves_gwf_vals_trans_final.
  Hint Resolve eval_e_preserves_gwf_vals_trans_final.

  Hint Resolve gwf_vals_free_vals_subst_b.
  Hint Resolve complexity_s_0.
  Hint Resolve eval_term_preserves_gwf_vals.
  Hint Resolve eval_preserves_gwf_val.
  Hint Resolve eval_preserves_gwf_vals.
  Hint Resolve gwf_val_update gwf_obj_field_update.
  assert (ccs:{x : nat | complexity_s s <= x}) by eauto.
  destruct ccs as [c cs].
  revert p λ s g s' g' cs.
  induction c; intros; [assert False by eauto; intuition|].
  t2 s H1 IHc.
 - eapply IHc; try eapply H11; eauto.
    rewrite complexity_s_subst; omega.
 - eapply IHc; try eapply H10; dts omega.
 - replace ve with (trans_vals (⊗ ve)) by reflexivity.
   eapply IHc; try eapply H8; dts omega.
 - eapply IHc; try eapply H10; dts omega.
 - eapply IHc; try eapply H11; dts omega.
 - assert (gwf_vals g'0 (placed_vals p0 (trans_vals λ0)))
   by (eapply IHc; try eapply H9; dts omega).
   eapply  transCopy_gwf_vals; eauto.
 - eapply IHc; try eapply H5; dts omega.
Qed.

Lemma eval_preserves_gwf_vals_final {p λ s g s' g'} :
  isPlaceClosed s = true ->
  gwf_vals g (free_vals p s) ->
  (s,g) -[p | λ]-> (s',g') ->
  gwf_vals g' (free_vals p s').
Proof.
  Hint Resolve eval_term_preserves_gwf_vals_trans.
  Hint Resolve gwf_val_nat gwf_vals_nil eval_e_term_preserves_gwf_vals_trans.
  Hint Resolve gwf_val_ghincl_f.
  Hint Resolve gwf_vals_ghincl_f.
  Hint Resolve eval_e_term_preserves_gwf_vals_trans_final.
  Hint Resolve eval_e_preserves_gwf_vals_trans_final.

  Hint Resolve gwf_vals_free_vals_subst_b.
  Hint Resolve complexity_s_0.
  Hint Resolve eval_term_preserves_gwf_vals.
  Hint Resolve eval_preserves_gwf_val.
  Hint Resolve eval_preserves_gwf_vals.
  Hint Resolve gwf_val_update gwf_obj_field_update.
  Hint Resolve eval_term_preserves_gwf_vals_trans.
  Hint Resolve eval_preserves_gwf_vals_trans.
  Hint Resolve eval_e_preserves_gwf_vals_final.
  Hint Resolve eval_e_ghincl.

  assert (ccs:{x : nat | complexity_s s <= x}) by eauto.
  destruct ccs as [c cs].
  revert p λ s g s' g' cs.
  induction c; intros; [assert False by eauto; intuition|].
  t2 s H1 IHc.
 - eapply IHc; try eapply H11; eauto.
    rewrite complexity_s_subst; omega.
 - split. 
   + eapply IHc; try eapply H10; dts omega.
   + eapply eval_preserves_gwf_vals; try eapply H1; eauto 2;
     simpl; simpwf; dt idtac; auto.     
 - eapply IHc; try eapply H8; dts omega.
 - split.
   + eapply eval_preserves_gwf_vals; try eapply H1; eauto 2;
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
   eapply IHc; try eapply H11; dts omega.
 - split; eauto 2.
   eapply IHc; try eapply H10; dts omega.
 - eapply gwf_vals_ghincl_f.
   + eapply hincl_update_ghincl; eauto 2.
     eapply transCopy_hincl_eqs; eauto.
   + eapply IHc; try eapply H9; dts omega.
 - eapply IHc; try eapply H5; dts omega.
Qed.

(* The non-resilient calculus is only total if the global heap is totally defined *)
Theorem eval_total p s1 g1 : 
  wfStmt s1 = true -> 
  gwf_vals g1 (free_vals p s1) ->
  (forall q, contains g1 q) ->
  { λ:trans_type & {s2g2 | (s1,g1) -[p | λ]->? s2g2}}.
Proof.
  Hint Resolve complexity_s_0.
  assert (ccs:{x : nat | complexity_s s1 <= x}) by eauto.
  destruct ccs as [c cs].
  revert p g1 s1 cs.
  induction c; intros; [assert False by eauto; intuition|].

Hint Resolve eval_e_total some_lookup_contains.
Hint Resolve gwf_vals_free_vals_on_subst_f.
Hint Resolve gwf_val_wf.

Hint Constructors eval.

Hint Resolve EThrowCtxt EThrowCtxtTerm EBindCtxt EBindCtxtTerm EUpdateCtxt1 EUpdateCtxt1Term EUpdateCtxt2 EUpdateCtxt2Term EAtCtxt EAtCtxtTerm EAt EDAt EDAtTerm EDAsync EDAsyncTerm.

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
  poses (contains_all_strengthen H1).
  destruct (P p) as [h gph].
  destruct s1; simpl in *; simplwf.
  (* Skip *)
  - eauto.
  (* Throw *)
  - discval e; eauto.
    destruct (eval_e_total p e h) as [λ [[[e' h']|h'] ehe]]; eauto.
  (* Bind *)
  - discval e.
    + destruct (IHc p g1 s1[x//v]) as [λ [s2g2 ev']]; simplwf; intuition; [dts idtac|].
      destruct s2g2 as [[s2 g2]|g2]; eauto.
    + destruct (eval_e_total p e h) as [λ [[[e' h']|h'] ehe]]; intuition; eauto.
  (* Assign *)
  - discval e.
    + discval e0.
      * destruct x; eauto. case_eq (h[@o]); intros; subst.
        case_eq (o0[@f]); intros.
          repeat eexists; eapply EUpdate;
            eauto; eapply some_lookup_contains; eauto.
          repeat eexists; eapply EUpdateBad; eauto.
          rewrite H4; eauto.
        repeat eexists; eapply EUpdateBad; eauto.
        rewrite H4; eauto.
      * destruct (eval_e_total p e0 h) as [λ [[[e' h']|h'] ehe]]; intuition; eauto.
    + destruct (eval_e_total p e h) as [λ [[[e' h']|h'] ehe]]; intuition; eauto.
  (* Seq *)
  - destruct (IHc p g1 s1_1) as [λ [sg' ev']]; dts omega.
    case_eq (isSyncTrans λ); eauto.
    + destruct λ; simpl; intuition; eauto.
    + destruct sg' as [[s' g']|g']; eauto.
  (* At *)
  - discval e.
    + case_eq (g1[@p0]); intros.
      * case_eq (copy h x h0); [intros [??]|]; intros; eauto.
        simpl in *; simplwf.
        assert False; intuition.
        eapply gwf_val_wf in H0; eauto.
        edestruct (wf_can_copy _ H0 h0) as [?[??]]; eauto.
        congruence.
      * assert False; intuition.
        destruct (H1 p0); unfold place in *; congruence.
    + destruct (eval_e_total p e h) as [λ [[[e' h']|h'] ehe]]; intuition; eauto.
  (* Async *) 
  - eauto.
  (* Finish *)
  - destruct (IHc p g1 s1) as [λ [[[s' g']|g'] ev']]; dts omega.
  (* Catch *)
  - destruct (IHc p g1 s1_1) as [λ [sg' ev']]; dt ltac:(intuition; eauto 2; try omega).
    case_eq (isSyncTrans λ); destruct sg' as [[s' g']|g']; eauto;
    destruct λ; simpl; intuition; eauto.
  (* DAt *)
  - destruct (IHc p0 g1 s1) as [λ [[[s' g']|g'] ev']]; dts omega.
    + poses (H1 p).
      poses (H1 p0).
      apply (eval_preserves_places _ _ _ _ _ _ ev') in P0.
      apply (eval_preserves_places _ _ _ _ _ _ ev') in P1.
      apply contains_strengthen in P0; apply contains_strengthen in P1.
      destruct P0; destruct P1.
      assert (wft:wf_vals x0 (trans_vals λ)).
      * eapply gwf_vals_wf; eauto 1.
        replace (placed_vals p0 (trans_vals λ)) with (ptrans_vals p0 λ) by trivial.
        eapply eval_preserves_gwf_vals_trans; eauto.
      * destruct (wf_can_transCopy (p0 ==b p) x wft) as [?[??]]; eauto.
    + poses (H1 p).
      poses (H1 p0).
      apply (eval_preserves_places_term _ _ _ _ _ ev') in P0.
      apply (eval_preserves_places_term _ _ _ _ _ ev') in P1.
      apply contains_strengthen in P0; apply contains_strengthen in P1.
      destruct P0; destruct P1.
      assert (wft:wf_vals x0 (trans_vals λ)).      
      * eapply gwf_vals_wf; eauto 1.
        replace (placed_vals p0 (trans_vals λ)) with (ptrans_vals p0 λ) by trivial.
        destruct (P p0) as [g1ph g1ps]. 
        eapply eval_term_preserves_gwf_vals_trans; eauto.
      * destruct (wf_can_transCopy (p0 ==b p) x wft) as [?[??]]; eauto.
  (* DAsync *) 
  - destruct (IHc p g1 s1) as [λ [[[s' g']|g'] ev']]; dts omega.
Grab Existential Variables.
red; eauto.
Defined.

(* Any well formed statement and global heap can be evaluated until it either terminates
  in a final heap with no exceptions, or generates an (uncaught) exception *)
Theorem eval_star_total p s1 g1 : 
  wfStmt s1 = true -> 
  gwf_vals g1 (free_vals p s1) ->
  (forall q, contains g1 q) ->
    {g2 | (s1,g1) -[p | ε]->*! g2}
  + { vs:list val & {s2g2 | (s1,g1) -[p | ⊗ vs]->*? s2g2}}
  + { vs:list val & {s2g2 | (s1,g1) -[p | × vs]->*? s2g2}}.
Proof.
  Hint Resolve eval_eval_star eval_star_trans eval_star_refl.
  Hint Resolve complexity_s_0.

  assert (ccs:{x : nat | complexity_s s1 <= x}) by eauto.
  destruct ccs as [c cs].
  revert p g1 s1 cs.
  induction c; intros; [assert False by eauto; intuition|].
  destruct (eval_total p s1 g1) as [λ [s2g2 ev]]; eauto 2.
  destruct λ; intuition eauto.
  destruct s2g2 as [[s2 g2]|g2]; eauto.
  poses (eval_decreases_complexity ev).
  Hint Resolve eval_stmt_preserves_wfStmt.
  Hint Resolve eval_preserves_gwf_vals.
  destruct (IHc p g2 s2) as [[[g3 ev']|[vs [s3g3 ev']]]|[vs [s3g3 ev']]] ;
    eauto 2; try omega; [| |intuition eauto..].
  - eapply eval_preserves_gwf_vals_final; eauto 2.
    unfold wfStmt, isClosed in *; dt idtac.
  - intros; apply -> eval_preserves_places; eauto. 
Defined.

Lemma eval_finish_nasync_trans {p μ vs s g s2g2} :
        (Finish μ s,g) -[p|× vs]->? s2g2 -> False.
Proof.
  Hint Resolve asSyncTrans_nasync.
  inversion 1; eauto.
Qed.
  
Lemma eval_star_finish_to_finish {p μ s g s' g'} :
  (Finish μ s, g) -[ p | ε ]->* (s', g') ->
  exists s'' l, s' = Finish l s''.
Proof.
  intros ev. 
  apply eval_star_eval_star_left in ev.
  dependent induction ev; eauto.
  inversion H; subst.
  eauto.
Qed.

Lemma eval_star_finish_nasync_trans {p μ vs s g s2g2} :
        (Finish μ s,g) -[p|× vs]->*? s2g2 -> False.
Proof.
  intros ev.
  dependent induction ev.
  destruct sg'.
  destruct (eval_star_finish_to_finish ev) as [s' [l' ev']]; subst.
  eapply eval_finish_nasync_trans; eauto.
Qed.

Lemma eval_star_total_finish p s1 g1 : 
  wfStmt s1 = true -> 
  gwf_vals g1 (free_vals p s1) ->
  (forall q, contains g1 q) ->
    {g2 | (Finish nil s1,g1) -[p | ε]->*! g2}
  + { vs:list val & {s2g2 | (Finish nil s1,g1) -[p | ⊗ vs]->*? s2g2}}.
Proof.
  Hint Resolve eval_finish_nasync_trans.
  intros.
  destruct (eval_star_total p (Finish nil s1) g1); eauto 2.
  destruct s as [?[? ev]].
  assert False; intuition.
  eapply eval_star_finish_nasync_trans; eauto.
Qed.

Section evolve.

Lemma eval_term_gevolve {λ p s g g'} :
  (s,g) -[p | λ]->! g' ->
  gevolve g g'.
Proof.
  Hint Resolve complexity_s_0.

  Hint Resolve eval_e_term_ghincl ghincl_gevolves.
  Hint Resolve hevolve_update gevolve_update.
  Hint Resolve transCopy_hevolve_eqs.

  assert (ccs:{x : nat | complexity_s s <= x}) by eauto.
  destruct ccs as [c cs].
  revert λ p s g g' cs.
  induction c; intros; [assert False by eauto 3; intuition|].
  destruct s; simpl in *; inversion H; clear H; subst; simpl in *; 
  simpwf;
  dt idtac; 
  try solve[intuition; eauto 3
           | match goal with 
                 [H:_ -[_ | _]->! _ |- _ ] => eapply IHc; try eapply H; dts omega
             end].
  transitivity g'0; eauto.
  match goal with 
      [H:_ -[_ | _]->! _ |- _ ] => eapply IHc; try eapply H; dts omega
  end.
Qed.

Lemma eval_gevolve {λ p s g s' g'} :
  (s,g) -[p | λ]-> (s',g') ->
  gevolve g g'.
Proof.
  Hint Resolve complexity_s_0.

  Hint Resolve eval_e_ghincl eval_term_gevolve ghincl_gevolves.
  Hint Resolve hevolve_update gevolve_update.
  Hint Resolve transCopy_hevolve_eqs copy_hevolve.

  assert (ccs:{x : nat | complexity_s s <= x}) by eauto.
  destruct ccs as [c cs].
  revert λ p s g s' g' cs.
  induction c; intros; [assert False by eauto 3; intuition|].
  destruct s; simpl in *; inversion H; clear H; subst; simpl in *; 
  simpwf;
  dt idtac; 
  try solve[intuition; eauto 3
           | match goal with 
                 [H:_ -[_ | _]-> _ |- _ ] => solve[eapply IHc; try eapply H; dts omega]
             end].
  transitivity g'0; eauto.
  match goal with 
      [H:_ -[_ | _]-> _ |- _ ] => eapply IHc; try eapply H; dts omega
  end.
Qed.

End evolve.

Lemma eval_term_subst {p λ s g g'} v x :
(s, g) -[ p | λ ]->! g' ->
(s[v//x], g) -[ p | λ ]->! g'.
Proof.
  unfold subst.
  Hint Resolve complexity_s_0.
  Hint Resolve eval_e_term_subst'.
  Hint Resolve eval_e_term_subst.
  assert (ccs:{x : nat | complexity_s s <= x}) by eauto.
  destruct ccs as [c cs].
  revert p λ s g g' x v cs.
  induction c; intros; [assert False by eauto 3; intuition|].
  destruct s; simpl in *; inversion H; subst; unfold subst; simpl in *; dt idtac;
  try solve[eauto 3 | econstructor; eauto 3 | dts omega].
  - destruct (@equiv_dec var (@eq var) (@eq_equivalence var)
                         oid_eqdec x v0); eauto.
    econstructor; trivial.
    unfold complement, equiv in *.
    unfold subst.    
    poses @substs_commute. unfold subst in P. rewrite P; auto.
    apply IHc; auto. fold subst.
    poses complexity_s_subst. unfold subst in P0.  rewrite P0.
    omega.
  - rewrite <- vals_plus_trans_vals. econstructor.
    dts omega.
  - econstructor; eauto.
    dts omega.
Qed.

End eval_stmt_props.