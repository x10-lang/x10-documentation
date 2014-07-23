(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Properties of the expression semantics for TX10 (and Resilient X10) *)
Require Import Program.
Require Import Eqdep_dec.
Require Import Assoc2.
Require Export ExprSemantics.
Require Export ExprProps.
Require Import Auxiliary2.
Require Import GloballyReachable.

Section eval_expr_props.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

(* expression evaluation is deterministic *)
Theorem eval_e_det {p λ λ' e1 h1 e2h2 e2'h2'} : (e1,h1) -e[p | λ ]->? e2h2
                     -> (e1,h1) -e[p|λ']->? e2'h2'
                     -> λ=λ'
                     /\ e2h2 = e2'h2'.
Proof.
  Local Ltac te :=  
    repeat match goal with
      | [H: inl _ = inr _ |- _] => discriminate
      | [H: isVal ?f = true |- _ ] => apply isVal_true in H; destruct H; subst
      | [H:evale _ _ (Val _, _) _ |- _] => inversion H
      | [H: inl _ = inl _ |- _] => inversion H; clear H; try subst
    end.
  revert λ λ' e2h2 e2'h2'.
  dependent induction e1 using expr_indF; intros e2 h2 e2' h2' IH1 IH2; try solve[inversion IH1].
  (* Select *)
  - inversion IH1; subst; inversion IH2; subst; try te;
    try solve[match goal with 
          [H1: evale _ _ ?x _, H2: evale _ _ ?x _ |- _] => destruct (IHe1 _ _ _ _ _ H1 H2); te; intuition discriminate
      end | split; congruence].
    + rewrite H5 in *. congruence.
    + rewrite H6 in *. congruence.
  (* New *) 
  - rewrite Forall_forall in *. inversion IH1; subst.
    + inversion IH2; subst.
      * unfold allVals in *. rewrite forallb_forall, <- Forall_forall in *.
        rewrite domain_mswap_codomain in H8, H6.
        destruct (equal_part_upto _ H0 H8) as [?[??]]; auto.
        inversion H5; simpl; congruence.
        inversion H4; simpl; congruence.
        inversion H2; subst. 
        rewrite Forall_forall in H.
        assert (InH:In (f,e) (l1 ++ (f, e) :: l2)) 
          by (apply in_app_iff; simpl; intuition).
        destruct (H (f,e) InH _ _ _ _ _ H4 H5); te; intuition.
      * unfold allVals in *. rewrite forallb_forall, <- Forall_forall in *.
        rewrite domain_mswap_codomain in H8, H6.
        destruct (equal_part_upto _ H0 H8) as [?[??]]; auto.
          inversion H5; simpl; congruence.
          inversion H4; simpl; congruence.
        inversion H2; subst.
        rewrite Forall_forall in H.
        assert (InH:In (f,e) (l1 ++ (f, e) :: l2)) 
          by (apply in_app_iff; simpl; intuition).
        destruct (H (f,e) InH _ _ _ _ _ H4 H5); te; intuition.
      * unfold allVals in *.  poses pf0. 
        rewrite mswap_app, domain_app, forallb_app in P.
        dt idtac.
        te.
    + inversion IH2; subst.
       * unfold allVals in *. rewrite forallb_forall, <- Forall_forall in *.
         rewrite domain_mswap_codomain in H8, H6.
         destruct (equal_part_upto _ H0 H8) as [?[??]]; auto.
         inversion H5; simpl; congruence.
         inversion H4; simpl; congruence.
         inversion H2; subst.
        rewrite Forall_forall in H.
        assert (InH:In (f,e) (l1 ++ (f, e) :: l2)) 
          by (apply in_app_iff; simpl; intuition).
        destruct (H (f,e) InH _ _ _ _ _ H4 H5); te; intuition discriminate.
      * unfold allVals in *. rewrite forallb_forall, <- Forall_forall in *.
         rewrite domain_mswap_codomain in H8, H6.
         destruct (equal_part_upto _ H0 H8) as [?[??]]; auto.
         inversion H5; simpl; congruence.
         inversion H4; simpl; congruence.
         inversion H2; subst.
         rewrite Forall_forall in H.
        assert (InH:In (f,e) (l1 ++ (f, e) :: l2)) 
          by (apply in_app_iff; simpl; intuition).
        destruct (H (f,e) InH _ _ _ _ _ H4 H5); te; intuition discriminate.
       * unfold allVals in *.  poses pf0. 
         rewrite mswap_app, domain_app, forallb_app in P. dt idtac.
         te.
    + revert oh IH1. inversion IH2; subst; intros.
       * unfold allVals in *.  poses pf0. 
         rewrite mswap_app, domain_app, forallb_app in P. dt idtac.
         te.
       * unfold allVals in *.  poses pf0. 
         rewrite mswap_app, domain_app, forallb_app in P. dt idtac.
         te.
       * unfold oh, oh0 in *.
         rewrite (toCompactVals_pf_irrel l pf0 pf1).
         intuition.
  (* GetGlobal *)
  - inversion IH1; subst; inversion IH2; subst; te;
      solve[destruct (IHe1 _ _ _ _ _ H4 H5); subst; te; intuition discriminate | intuition].
  (* MkGlobal *)
  -  inversion IH1; subst; inversion IH2; subst; te;
      solve[destruct (IHe1 _ _ _ _ _ H4 H5); subst; te; intuition discriminate | intuition].
Qed.

Lemma new_cons1 {l h1 p λ f e0} : (({e2h2 | (New l, h1) -e[ p | λ]->? e2h2}) ->
        {e2h2 : expr * heap + heap | (New ((f, Val e0) :: l), h1) -e[ p | λ]->? e2h2}).
Proof.
  Hint Resolve ENewCtxt ENewCtxtTerm.
  intros. case_eq (allVals ((f, Val e0)::l)); intros pf.
  - destruct X as [[[e2 h]|h] H].
    + exists (@inl _ heap (Val (Object (snd (new h1 (toCompactVals ((f, Val e0)::l) pf)))), (fst (new h1 (toCompactVals ((f, Val e0)::l) pf))))).
    inversion H; subst; simpl in *.
      * poses pf. unfold allVals in *; simpl in P; rewrite mswap_app, domain_app, forallb_app in P. dt te.
      * apply ENewObj.
    + assert False; intuition. inversion H; subst.
      unfold allVals in *.
      simpl in pf; rewrite mswap_app, domain_app, forallb_app in pf; simpl in *.
      dt idtac. destruct (isVal_true H1); subst. inversion H5.
  - destruct X; destruct x as [[e1 h]|h].
    + destruct e1; try solve[assert False; intuition; inversion e; unfold allVals in *; simpl in *; congruence].
      exists (@inl _ heap ((New ((f, Val e0)::l0)), h)).
        inversion e; subst.
        * replace ((f, Val e0) :: l1 ++ (f0, e1) :: l2) with (((f, Val e0) :: l1) ++ (f0, e1) :: l2) by apply app_comm_cons.
          replace ((f, Val e0) :: l1 ++ (f0, e') :: l2) with (((f, Val e0) :: l1) ++ (f0, e') :: l2) by apply app_comm_cons.
          eauto.
    + exists (@inr (expr*heap) _ h).
      inversion e; subst.
      replace ((f, Val e0) :: l1 ++ (f0, e1) :: l2) with (((f, Val e0) :: l1) ++ (f0, e1) :: l2) by apply app_comm_cons.
      eauto.
Qed.

Lemma new_cons2 {l h1 p f e0} : 
  {e2h2 : expr * heap | (New ((f, Val e0) :: l), h1) -e[ p | ε]-> e2h2} 
  -> {e2h2 | (New l, h1) -e[ p | ε]-> e2h2}.
Proof.
  Hint Resolve ENewCtxt ENewCtxtTerm.
  intros. case_eq (allVals ((f, Val e0)::l)); intros pf.
  - destruct X as [[e2 h] H].
      exists ((Val (Object (snd (new h1 (toCompactVals l pf))))), (fst (new h1 (toCompactVals l pf)))).
      unfold allVals in *; simpl in pf.
      eapply ENewObj.
  - simpl in pf. destruct X; destruct x. 
    destruct e1; try solve[assert False; intuition; inversion e; simpl in *; unfold allVals in *; simpl in *; congruence].
      destruct l0.
       1: assert False; intuition; inversion e; subst; try congruence;
         eapply app_cons_not_nil; eauto.
       exists ((New l0),h).
       destruct p0.
       inversion e; subst.
       + destruct l1; simpl in *; inversion H; subst; te.
         inversion H3; subst.
         eauto.
Qed.

(* expression evaluation it total and computable *)
Theorem eval_e_total p e1 h1 : free_vars_e e1 = nil -> isVal e1 = false ->
  { λ:trans_type & {e2h2 | (e1,h1) -e[p | λ]->? e2h2}}.
Proof.
  Local Ltac te' := repeat match goal with
        | [H: sig _ |- _ ] => destruct H
        | [H: (Val _, _) -e[ _ | _]-> _ |- _ ] => inversion H
        | [|- ~ (Val _, _) -e[ _ | _]-> _ ] => inversion 1
        | [H: (Var _, _) -e[ _ | _]-> _ |- _ ] => inversion H
        | [|- ~ (Var _, _) -e[ _ | _]-> _ ] => inversion 1
        | [H: prod _ _ |- _ ] => destruct H
        | [H: isVal ?f = true |- _ ] => apply isVal_true in H; destruct H; subst
      end.
  Local Ltac de := try solve[right; inversion 1; subst; te'; intuition solve[congruence|eauto]].
  dependent induction e1 using expr_rectF; simpl; intros fv nval; try discriminate.
  Hint Resolve ESelect ESelectBad ESelectCtxt ESelectCtxtTerm EMkGlobalCtxt EMkGlobalCtxtTerm EMkGlobal EMkGlobalBad EGetGlobalCtxt EGetGlobalCtxtTerm EGetGlobal EGetGlobalBad ENewCtxt ENewCtxtTerm new_cons1.
  (* Select *)
  - case_eq (isVal e1); intros isv.
    + unfold isVal in isv; destruct e1; try discriminate.
      destruct v; eauto.
      case_eq (h1[@o]); de.
      * intros. case_eq (o0[@ff]); intros; eauto.
        eexists; eexists; eapply ESelectBad; rewrite H; auto.
      * eexists; eexists; eapply ESelectBad; rewrite H; auto.
    + destruct (IHe1 h1) as [?[??]]; trivial. destruct x0 as [[??]|?]; eauto.
  (* New *)
  - clear nval. induction l; [eexists; eexists; apply (@ENewObj _ _ _ nil _ (eq_refl true))|].
    inversion X; subst.
    simpl in fv; apply app_eq_nil in fv; destruct fv as [fv1 fvs].
    specialize (IHl X1 fvs).
    destruct IHl as [? [??]].
    destruct a as [f a].
    case_eq (isVal a); intros isv; te'; simpl in *; eauto.
    replace ((f, a) :: l) with (nil ++ ((f, a) :: l)) by auto.
    destruct (X0 h1) as [λ [eh ev]]; auto.
    destruct eh as [[e' h]|h]; eauto.
  (* GetGlobal *)
  - case_eq (isVal e1); intros; te.
    + destruct x; eauto.
      destruct (p==p0); unfold equiv, complement in *; subst; eauto.
    + destruct (IHe1 h1) as [λ [[[e h]|h] ev]]; auto; eauto.
  (* MkGlobal *)
    - case_eq (isVal e1); intros; te.
    + destruct x; eauto. 
    + destruct (IHe1 h1) as [λ [[[e h]|h] ev]]; auto; eauto.
Qed.

(* Whenever we signal an exception, we yield a final heap.  So if we yield a new 
 (expression, heap) pair then we must not signal anything *)
Theorem eval_e_ε {p λ e1h1 e2h2} : e1h1 -e[p | λ]-> e2h2 -> λ = ε.
Proof.
  intros H.
  dependent induction H; eauto.
Qed.

Theorem eval_e_preserves_free_vars {p λ e h e' h'} : 
  (e,h) -e[p | λ]-> (e', h') -> free_vars_e e' = free_vars_e e.
Proof.
  dependent induction e using expr_indF; inversion 1; subst; simpl; eauto.
  - repeat rewrite fold_right_app.
    f_equal; simpl; f_equal.
    rewrite Forall_forall in *.
    eapply (H (f,e)); eauto. 
  - rewrite allVals_closed; auto.
Qed.

Require Import Lt.

Theorem eval_e_decreases_complexity {p λ e h e' h'} : 
  (e,h) -e[p | λ]-> (e', h') -> complexity_e e' < complexity_e e.
Proof.
  Hint Resolve lt_n_S.
  dependent induction e using expr_indF; inversion 1; subst; simpl; eauto.
  - rewrite Forall_forall in *.
    assert (complexity_e e'0 < complexity_e e)
      by (eapply (H (f,e)); eauto; apply in_app_iff; intuition).
    repeat rewrite compl_fr_app; simpl.
    omega.
  - omega.
Qed.

Definition terminal_config_e (config:(expr * heap) + heap) : bool
  := match config with
         | inl (e,_)=> isVal e
         | inr _ => true
     end.

Inductive eval_e_config : place -> trans_type -> 
                 (expr * heap) + heap -> (expr*heap) + heap -> Prop := 
| EConfig_e : forall p λ eh eh',
   eh -e[p|λ]->? eh' -> eval_e_config p λ (inl eh) eh'. 

(* Given a closed expression, we can compute a terminal configuration and a (finite) series of expression evaluation steps that will get us there *)
Theorem eval_e_star_total p e1 h1 : free_vars_e e1 = nil -> 
  { λ:trans_type & {e2h2 | (e1,h1) -e[p | λ]->*? e2h2 & terminal_config_e e2h2 = true}}.
Proof.
  Hint Constructors eval_e_star.
  assert (cce:{x : nat | complexity_e e1 <= x}) by eauto.
  destruct cce as [c ce].
  revert h1 e1 ce.
  induction c.
  - intros.
    assert False; intuition. induction e1; simpl in ce; omega.
  - intros. case_eq (isVal e1); eauto; intros.
    destruct (eval_e_total p e1 h1) as [λ [[[e h]|h] ev]]; eauto.
    poses (eval_e_ε ev); subst.
    destruct (IHc h e)  as [λ [eh' ev']].
    + poses (eval_e_decreases_complexity ev); omega.
    + erewrite eval_e_preserves_free_vars; eauto.
    + exists λ. exists eh'; auto.
      eapply eval_e_star_trans; [|eassumption].
      eauto.
Qed.

(* evaluation preserves local (and global) well formedness *)
Section wf.
Require Import Reachable.
Lemma eval_e_term_preserves_wf_val {p v λ e h h'} :
  wf_val h v ->
  (e,h) -e[p | λ]->! h' ->
  wf_val h' v.
Proof.
  revert p v λ h h'.
  dependent induction e using expr_indF; intros p v' λ h h' wf; inversion 1; subst; simpl in *; eauto; (try solve [rewrite update_same_eq; auto]).
  - rewrite Forall_forall in *. eapply (H (f,e)); eauto.
    
Qed.

Lemma eval_e_preserves_wf_val {p v λ e h e' h'} :
  wf_val h v ->
  (e,h) -e[p | λ]-> (e', h') ->
  wf_val h' v.
Proof.
  Hint Resolve eval_e_term_preserves_wf_val.
  revert p v λ h e' h'.
  dependent induction e using expr_indF; intros p v' λ h e' h' wf; inversion 1; subst; simpl in *; eauto; (try solve [rewrite update_same_eq; auto]).
  - rewrite Forall_forall in *. eapply (H (f,e)); eauto.
  - destruct v'; try solve[red; inversion 1].
    eapply wf_val_hincl; eauto.
    + eapply hincl_new.
    + apply wf; reflexivity.
Qed.

End wf.

Lemma eval_e_term_preserves_gwf_val {p q v λ e g h h'} :
  gwf_val g q v ->
  g[@p] = Some h ->
  (e,h) -e[p | λ]->! h' ->
  gwf_val g[p~~>Some h'] q v.
Proof.
  revert p q v λ g h h'.
  dependent induction e using expr_indF; intros p q v' λ g h h' wf heq; inversion 1; subst; simpl in *; eauto; (try solve [unfold place in *; rewrite update_same_eq; auto]).

  rewrite Forall_forall in *. eapply (H (f,e)); eauto.
Qed.


Lemma eval_e_preserves_gwf_val {p q v λ e g h e' h'} :
  gwf_val g q v ->
  g[@p] = Some h ->
  (e,h) -e[p | λ]-> (e', h') ->
  gwf_val g[p~~>Some h'] q v.
Proof.
  Hint Resolve eval_e_term_preserves_gwf_val.
  revert p q v λ g h e' h'.
  dependent induction e using expr_indF; intros p q v' λ g h e' h' wf heq; inversion 1; subst; simpl in *; eauto; (try solve [unfold place; rewrite update_same_eq; auto]).
  - rewrite Forall_forall in *. eapply (H (f,e)); eauto.
  - eapply gwf_val_ghincl_f; eauto.
    eapply hincl_update_ghincl; eauto.
    apply hincl_new.
Qed.

Lemma eval_e_term_hincl {p λ e h h'} :
      (e,h) -e[p | λ]->! h' ->
      hincl h h'.
Proof.
  revert p λ h h'.
  dependent induction e using expr_indF; intros p λ h h'; inversion 1; subst; simpl in *; eauto; intuition. 
  rewrite Forall_forall in *. eapply (H (f,e)); eauto.
Qed.

Lemma eval_e_hincl {p λ e h e' h'} :
      (e,h) -e[p | λ]-> (e', h') ->
      hincl h h'.
Proof.
  Hint Resolve eval_e_term_hincl.
  revert p λ h e' h'.
  dependent induction e using expr_indF; intros p λ h e' h'; inversion 1; subst; simpl in *; eauto; intuition. 
  - rewrite Forall_forall in *. eapply (H (f,e)); eauto.
  - apply hincl_new.
Qed.

Lemma eval_e_term_ghincl {g p λ e h h'} :
      g[@p] = Some h ->
      (e,h) -e[p | λ]->! h' ->
      ghincl g g[p~~>Some h'].
Proof.
  Hint Resolve eval_e_term_hincl.
  intros; eapply hincl_update_ghincl; eauto.
Qed.

Lemma eval_e_ghincl {g p λ e h e' h'} :
      g[@p] = Some h ->
      (e,h) -e[p | λ]-> (e',h') ->
      ghincl g g[p~~>Some h'].
Proof.
  Hint Resolve eval_e_hincl.
  intros; eapply hincl_update_ghincl; eauto.
Qed.

Lemma eval_e_term_preserves_gwf_vals {l p λ e g h h'} :
  gwf_vals g l ->
  gwf_vals g (free_vals_e p e) ->
  g[@p] = Some h ->
  (e,h) -e[p | λ]->! h' ->
  gwf_vals g[p~~>Some h'] l.
Proof.
  Hint Resolve gwf_vals_ghincl_f eval_e_term_ghincl.
  eauto.
Qed.

Lemma eval_e_preserves_gwf_vals {l p λ e g h e' h'} :
  gwf_vals g l ->
  gwf_vals g (free_vals_e p e) ->
  g[@p] = Some h ->
  (e,h) -e[p | λ]-> (e',h') ->
  gwf_vals g[p~~>Some h'] l.
Proof.
  Hint Resolve gwf_vals_ghincl_f eval_e_ghincl.
  eauto.
Qed.


Lemma eval_e_preserves_gwf_vals_final {p λ e g h e' h'} :
  gwf_vals g (free_vals_e p e) ->
  g[@p] = Some h ->
  (e,h) -e[p | λ]-> (e',h') ->
  gwf_vals g[p~~>Some h'] (free_vals_e p e').
Proof.
  Hint Resolve gwf_val_wrap.
  Hint Resolve eval_e_ghincl.
  Hint Resolve gwf_obj_step gwf_val_step_obj gwf_val_step_gobject.


  revert p λ g h e' h'.
  dependent induction e using expr_indF; intros p λ g h e' h' wfre heq;
  inversion 1; subst; unfold singleton in *; simpl in *; eauto.
  - unfold gwf_vals, singleton in *; simpl in *.
    intuition; eauto. inversion H1; subst.
    eapply eval_e_preserves_gwf_val; eauto.
  - rewrite <- fold_right_flat_map in wfre |- *.
    intros p' v' inp'.
    apply in_flat_map in inp'.
    destruct inp' as [[f' e'] [infel infef]].
    rewrite Forall_forall in *.
    eapply Permutation_in in infel; [|symmetry; eapply Permutation_middle].
    simpl in infel. destruct infel.
    + inversion H1; subst; simpl in *.
      eapply (H (f', e)); eauto; simpl.
      unfold gwf_vals in *. intros. apply (wfre p0 v).
      apply in_flat_map.
      eexists; rewrite in_app_iff; intuition.
    + assert (In (f',e') (l1 ++ (f, e) :: l2)) by
      (eapply Permutation_in; [eapply Permutation_middle| simpl; intuition]).
      assert (gwf_val g p' v') by
          (apply wfre; apply in_flat_map; eauto).
      apply gwf_vals_singleton.
      eapply (@eval_e_preserves_gwf_vals (singleton (p',v'))); try apply H6; eauto.
      * apply gwf_vals_singleton; trivial.
      * red; intros.
        eapply wfre. apply in_flat_map.
        exists (f,e); intuition.
  - unfold gwf_vals, singleton in *; simpl in *; intuition.
    inversion H2; subst; clear H2.
    eapply gwf_val_step_o. 
    + unfold place; rewrite lookup_update_eq; eauto.
    + eapply lookup_new.
    + rewrite <- fold_right_flat_map in wfre. rewrite Forall_forall in *.
      intros f v veq.
      eapply gwf_val_ghincl_f; [eapply hincl_update_ghincl; eauto|].
      poses (obj_compact_toVals_lookup veq).
      apply lookup_in in P.
      apply obj_compact_in_in in P.
      apply wfre.
      apply in_flat_map. exists (f, Val v); simpl; intuition.
  - unfold place; rewrite update_same_eq; eauto.
    unfold gwf_vals, singleton in *; simpl in *; intuition.
    inversion H1; subst. assert (gwf_val g p0 (GlobalObject p0 oid)); eauto.
  - unfold place; rewrite update_same_eq; eauto.
    unfold gwf_vals, singleton in *; simpl in *; intuition.
    inversion H1; subst. assert (gwf_val g p0 (GlobalObject p0 oid)); eauto.
Qed.

Lemma eval_e_term_not_ε {p e1h1 g} : e1h1 -e[p | ε]->! g -> False.
Proof.
  intros H.
  dependent induction H; eauto.
Qed.

Lemma eval_e_term_sync_same_heap {p l e h h'} :
  (e, h) -e[ p | ⊗ l ]->! h' ->
  h = h'.
Proof.
  revert p l h h'.
  dependent induction e using expr_indF; intros p l' h h' ev; inversion ev; subst; simpl in *; eauto.
  - rewrite Forall_forall in H. eapply (H (f,e)); eauto.
Qed.

Lemma eval_e_term_async_same_heap {p l e h h'} :
  (e, h) -e[ p | × l ]->! h' ->
  h = h'.
Proof.
  revert p l h h'.
  dependent induction e using expr_indF; intros p l' h h' ev; inversion ev; subst; simpl in *; eauto.
  - rewrite Forall_forall in H. eapply (H (f,e)); eauto.
Qed.

Lemma eval_e_term_preserves_gwf_vals_trans {g p λ e h h'} :
  gwf_vals g (free_vals_e p e) ->
  g[@p] = Some h ->
  (e,h) -e[p | λ]->! h' ->
  gwf_vals g (ptrans_vals p λ).
Proof.
  Hint Resolve gwf_val_nat gwf_vals_nil.
  revert g p λ h h'.
  dependent induction e using expr_indF; intros g p λ h h' wf heq; inversion 1; subst; 
  simpl in *; unfold FieldNotFoundException, BadPlaceException, BadTypeException;
  unfold ptrans_vals in *; simpl in *;
  simpwf; eauto 3; (try solve [rewrite update_same_eq; auto]).
  rewrite Forall_forall in *. eapply (H (f,e)); eauto 2.
  - rewrite <- fold_right_flat_map in wf.
    red; intros.
    apply (wf p0).
    apply in_flat_map.
    eexists; intuition.
Qed.

Lemma eval_e_preserves_gwf_vals_trans {g p λ e h e' h'} :
  gwf_vals g (free_vals_e p e) ->
  g[@p] = Some h ->
  (e,h) -e[p | λ]-> (e',h') ->
  gwf_vals g (ptrans_vals p λ).
Proof.
  Hint Resolve gwf_val_nat gwf_vals_nil eval_e_term_preserves_gwf_vals_trans.
  revert g p λ h e' h'.
  dependent induction e using expr_indF; intros g p λ h e' h' wf heq; inversion 1; subst; 
  simpl in *; unfold FieldNotFoundException, BadPlaceException, BadTypeException;
  unfold ptrans_vals in *; simpl in *;
  simpwf; eauto 3; (try solve [rewrite update_same_eq; auto]).
  rewrite Forall_forall in *. eapply (H (f,e)); eauto 2.
  - rewrite <- fold_right_flat_map in wf.
    red; intros.
    apply (wf p0).
    apply in_flat_map.
    eexists; intuition.
Qed.


Lemma eval_e_term_preserves_gwf_vals_trans_final {g p λ e h h'} :
  gwf_vals g (free_vals_e p e) ->
  g[@p] = Some h ->
  (e,h) -e[p | λ]->! h' ->
  gwf_vals g[p~~>Some h'] (ptrans_vals p λ).
Proof.
  intros.
  eapply eval_e_term_preserves_gwf_vals; eauto.
Qed.

Lemma eval_e_preserves_gwf_vals_trans_final {g p λ e h e' h'} :
  gwf_vals g (free_vals_e p e) ->
  g[@p] = Some h ->
  (e,h) -e[p | λ]-> (e',h') ->
  gwf_vals g[p~~>Some h'] (ptrans_vals p λ).
Proof.
  intros.
  eapply eval_e_preserves_gwf_vals; eauto 2.
  eapply eval_e_preserves_gwf_vals_trans; eauto 2.
Qed.

Lemma eval_e_not_async {p l e h k} :
  (e, h) -e[ p | × l ]->? k -> False.
Proof.
  revert p l h k.
  dependent induction e using expr_indF; intros p l' h h' ev; inversion ev; subst; simpl in *; eauto.
  - rewrite Forall_forall in H. eapply (H (f,e)); eauto.
  - rewrite Forall_forall in H. eapply (H (f,e)); eauto.
Qed.

Lemma eval_e_term_subst {p λ e h h'} v x :
(e, h) -e[ p | λ ]->! h' ->
(e[v//x], h) -e[ p | λ ]->! h'.
Proof.
  Hint Constructors evale.
  unfold subst.
  revert p λ h h' v x.
  dependent induction e using expr_indF; intros p λ h h' v0 x0; inversion 1; subst; simpl in *;
  try solve[econstructor; eauto | eauto].
  - rewrite map_app; simpl. rewrite Forall_forall in *. 
    econstructor.
    + eapply (H (f,e)); eauto.
    + rewrite allVals_subst; trivial.
Qed. 

Lemma eval_e_term_subst' {p λ e h h'} v x :
(e, h) -e[ p | λ ]->! h' ->
(subst_expr e x v, h) -e[ p | λ ]->! h'.
Proof.
  poses @eval_e_term_subst.
  unfold subst in P.
  eauto.
Qed.

End eval_expr_props.
