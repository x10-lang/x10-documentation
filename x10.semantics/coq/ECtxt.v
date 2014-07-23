(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Defines Evaluation Contexts, and their associated properties *)
Require Export Syntax.
Require Import Program.
Require Import Eqdep_dec.
Require Import Omega.

Section ectxt.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

(* Evaluation contexts with a hole for a statement *)
Inductive ectxt :=
  | ECHole : ectxt
  | ECSeq1 : ectxt -> stmt -> ectxt
  | ECSeq2 : forall (s:stmt), isAsync s = true -> ectxt -> ectxt
  | ECFinish : list val -> ectxt-> ectxt
  | ECCatch : ectxt -> stmt -> ectxt
  | ECDAt : place -> ectxt -> ectxt
  | ECDAsync : ectxt -> ectxt.

(* we can also plug a statement into a context to get a closed context *)
Fixpoint eplug (c:ectxt) (s:stmt) : stmt
  := match c with
       | ECHole => s
       | ECSeq1 c s2 => Seq (eplug c s) s2
       | ECSeq2 s1 pf c => Seq s1 (eplug c s)
       | ECFinish μ c => Finish μ (eplug c s)
       | ECCatch c t  => Catch (eplug c s) t
       | ECDAt p c => DAt p (eplug c s)
       | ECDAsync c => DAsync (eplug c s)
     end.

Lemma isAsync_subst_imp {s x v b} :
  isAsync s = b ->
  isAsync s[v//x] = b.
Proof.
  destruct (@isAsync_subst _ s x v); trivial.
Qed.

Global Instance subst_ectxt : Subst ectxt var val :=
{ subst := fix substc (c:ectxt) (x:var) (v:val) : ectxt :=
  match c with
       | ECHole => ECHole
       | ECSeq1 c s2 => ECSeq1 (substc c x v) (s2[v//x])
       | ECSeq2 s1 pf c => ECSeq2 (s1[v//x]) (isAsync_subst_imp pf) (substc c x v)
       | ECFinish μ c => ECFinish μ (substc c x v)
       | ECCatch c s2  => ECCatch (substc c x v) (s2[v//x])
       | ECDAt p c => ECDAt p (substc c x v)
       | ECDAsync c => ECDAsync (substc c x v)
  end
}.

Ltac tac 
  := idtac; match goal with
       | [H:context [(@equiv_dec ?A ?B ?C ?D ?X ?Y)] |- _] => destruct (@equiv_dec A B C D X Y); unfold equiv, complement in *; try subst; try congruence
       | [|- context [(@equiv_dec ?A ?B ?C ?D ?X ?Y)]] => destruct (@equiv_dec A B C D X Y); unfold equiv, complement in *; try subst; try congruence
     end.

Lemma subst_commute_nfree C s v x : 
  ~ In x (free_vars s) ->
  (eplug C s)[v//x] = eplug C[v//x] s.
Proof.
  Hint Rewrite topClosed_subst' subst_nfree' using solve[auto] : rewrites.
  revert s v x.
  unfold subst.
  induction C; simpl in *; unfold subst; dt tac; f_equal; dts tac.
Qed.

Lemma subst_commute_tclosed C s v x : 
     isTopClosed s = true 
  -> (eplug C s)[v//x] = eplug C[v//x] s.
  Hint Resolve subst_commute_nfree topClosed_nfree.
  auto.
Qed.

(* we can also plug a context with another context *)
Fixpoint eplug_c (c:ectxt) (c2:ectxt) : ectxt
  := match c with
       | ECHole => c2
       | ECSeq1 c s2 => ECSeq1 (eplug_c c c2) s2
       | ECSeq2 s1 pf c => ECSeq2 s1 pf (eplug_c c c2)
       | ECFinish μ c => ECFinish μ (eplug_c c c2)
       | ECCatch c s2  => ECCatch (eplug_c c c2) s2
       | ECDAt p c => ECDAt p (eplug_c c c2)
       | ECDAsync c => ECDAsync (eplug_c c c2)
     end.

Lemma eplug_c_ass c1 c2 c3 : eplug_c (eplug_c c1 c2) c3 = eplug_c c1 (eplug_c c2 c3).
Proof.
  induction c1; simpl; congruence.
Qed.

Lemma eplug_c_eplug c1 c2 s : eplug (eplug_c c1 c2) s = eplug c1 (eplug c2 s).
Proof.
  induction c1; simpl; congruence.
Qed.

Definition sub_eval_stmt (s1 s2:stmt) := exists C:ectxt, eplug C s1 = s2.
Definition sub_eval_ectxt (c1 c2:ectxt) := exists C:ectxt, eplug_c C c1 = c2.

Global Instance sub_eval_stmt_pre : PreOrder sub_eval_stmt.
Proof.
constructor; unfold sub_eval_stmt; red.
(* reflexive *)
- intros; exists ECHole; auto.
(* transitive *)
- intros x y z [C1 pC1] [C2 pC2].
  exists (eplug_c C2 C1).
  rewrite eplug_c_eplug. congruence.
Qed.

Global Instance sub_eval_ectxt_pre : PreOrder sub_eval_ectxt.
Proof.
constructor; unfold sub_eval_stmt; red.
(* reflexive *)
- intros; exists ECHole; auto.
(* transitive *)
- intros x y z [C1 pC1] [C2 pC2].
  exists (eplug_c C2 C1).
  rewrite eplug_c_ass. congruence.
Qed.

Lemma eplug_c_ECHole_l c : eplug_c ECHole c = c.
Proof. reflexivity. Qed.

Lemma eplug_c_ECHole_r c : eplug_c c ECHole = c.
Proof.
  induction c; simpl; congruence.
Qed.

Lemma sub_eval_ectxt_ECHole c : sub_eval_ectxt ECHole c.
Proof.
  exists c; simpl; apply eplug_c_ECHole_r.
Qed.

Fixpoint size_ec (c:ectxt) : nat 
 := match c with
       | ECHole => 0
       | ECSeq1 c s2 => S (size_ec c + size_s s2)
       | ECSeq2 s1 pf c => S (size_s s1 + size_ec c)
       | ECFinish μ c => S (size_ec c)
       | ECCatch c s2  => S (size_ec c + size_s s2)
       | ECDAt p c => S (size_ec c)
       | ECDAsync c => S (size_ec c)
     end.

Lemma size_ec_eplug_dist c1 c2 : size_ec (eplug_c c1 c2) = size_ec c1 + size_ec c2.
Proof.
  induction c1; simpl; omega.
Qed.

Lemma size_eplug_dist c s : size_s (eplug c s) = size_ec c + size_s s.
Proof.
  induction c; simpl; omega.
Qed.

Lemma size_ec_0 c : size_ec c = 0 -> c = ECHole.
Proof.
  destruct c; simpl; trivial; omega.
Qed.

Lemma eplug_self c s : eplug c s = s -> c = ECHole.
Proof.
  intros peq.
  poses (f_equal size_s peq).
  rewrite size_eplug_dist in P.
  apply size_ec_0.
  omega.
Qed.

Lemma eplug_c_self c c2 : eplug_c c c2 = c2 -> c = ECHole.
Proof.
  intros peq.
  poses (f_equal size_ec peq).
  rewrite size_ec_eplug_dist in P.
  apply size_ec_0.
  omega.
Qed.

Lemma eplug_Fail {C s e} : eplug C s = Throw e -> C = ECHole /\ s = Throw e.
Proof.
  destruct C; simpl; inversion 1; intuition.
Qed.

Lemma eplug_Skip {C s} : eplug C s = Skip -> C = ECHole /\ s = Skip.
Proof.
  destruct C; simpl; inversion 1; intuition.
Qed.

Lemma eplug_c_CHole {c1 c2} : eplug_c c1 c2 = ECHole -> c1 = ECHole /\ c2 = ECHole.
Proof.
  destruct c1; simpl; inversion 1; tauto.
Qed.

Lemma sub_ectxt_of_CHole c : sub_eval_ectxt c ECHole -> c = ECHole.
Proof.
  intros [C ceq].
  destruct (eplug_c_CHole ceq); trivial.
Qed.

Global Instance sub_eval_stmt_asym : Antisymmetric stmt eq sub_eval_stmt.
Proof.
red; unfold sub_eval_stmt.
induction x; simpl; intros y [c1 ?] [c2 eq2]; subst; simpl in *;
rewrite <- eplug_c_eplug in eq2; apply eplug_self in eq2;
apply eplug_c_CHole in eq2; destruct eq2; subst; simpl; trivial.
Qed.

Global Instance sub_eval_ectxt_asym : Antisymmetric ectxt eq sub_eval_ectxt.
Proof.
red; unfold sub_eval_ectxt.
induction x; simpl; intros y [c1 ?] [c2 eq2]; subst; simpl in *;
rewrite <- eplug_c_ass in eq2; apply eplug_c_self in eq2;
apply eplug_c_CHole in eq2; destruct eq2; subst; simpl; trivial.
Qed.

Lemma eplug_sub_eval_stmt c s : sub_eval_stmt s (eplug c s).
Proof.
  unfold sub_eval_stmt; eauto.
Qed.

Lemma eplug_c_sub_eval_ectxt c1 c2 : sub_eval_ectxt c2 (eplug_c c1 c2).
Proof.
  unfold sub_eval_ectxt; eauto.
Qed.

Lemma staticOnly_eplug {s c} : staticOnly (eplug c s) = true -> staticOnly s = true.
Proof.
  induction c; simpl; dt idtac; intuition.
  destruct l; intuition.
Qed.

Lemma staticOnly_sub_eval_stmt {s1 s2} : sub_eval_stmt s1 s2 -> staticOnly s2 = true -> staticOnly s1 = true.
Proof.
  Hint Resolve staticOnly_eplug.
  destruct 1 as [c ceq]; subst; eauto.
Qed.

Ltac tacd 
  := idtac; match goal with
       | [H:context [(isSync ?s)] |- _] =>  case_eq (isSync s); intros iss; rewrite iss in *
     end.

Lemma properStmt_eplug {s c} : properStmt (eplug c s) = true -> properStmt s = true.
Proof.
  Hint Resolve staticOnly_eplug staticOnly_properStmt.
  induction c; simpl; dt tacd; intuition.
Qed.

Lemma properStmt_sub_stmt {s1 s2} : sub_eval_stmt s1 s2 -> properStmt s2 = true -> properStmt s1 = true.
Proof.
  Hint Resolve properStmt_eplug.
  destruct 1 as [c ceq]; subst; eauto.
Qed.

Lemma sub_eval_stmt_catch_inv {t s1 s2} : 
  sub_eval_stmt t (Catch s1 s2) ->
     t = Catch s1 s2
  \/ sub_eval_stmt t s1.
Proof.
  Hint Resolve eplug_sub_eval_stmt.
  destruct 1.
  induction x; simpl in *; try discriminate.
  - intuition.
  - inversion H; subst; eauto.
Qed.

Lemma sub_eval_stmt_seq_inv {t s1 s2} : 
  sub_eval_stmt t (Seq s1 s2) ->
     t = Seq s1 s2
  \/ sub_eval_stmt t s1
  \/ (sub_eval_stmt t s2 /\ isAsync s1 = true).
Proof.
  Hint Resolve eplug_sub_eval_stmt.
  destruct 1.
  induction x; simpl in *; try discriminate.
  - intuition.
  - inversion H; subst; eauto.
  - inversion H; subst; eauto.
Qed.  

Lemma staticOnly_isDynamic_sub_eval_stmt_iff {s} : staticOnly s = true -> (forall t, sub_eval_stmt t s -> isDynamic t = false).
Proof.
  Hint Resolve staticOnly_not_dynamic staticOnly_sub_eval_stmt. 
  induction s; simpl; try congruence; intros H; dt idtac; eauto 3;
  try solve [apply IHs; intros; apply H; etransitivity; eauto|
         split; [apply IHs1|apply IHs2]; intros; apply H; etransitivity; eauto].

  - apply sub_eval_stmt_seq_inv in H0; intuition. subst; trivial.
  - apply sub_eval_stmt_catch_inv in H0; intuition. subst; trivial.
Qed.

End ectxt.