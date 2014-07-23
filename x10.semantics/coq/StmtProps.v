(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Definition and lemmas about statements *)
Require Export Auxiliary.
Require Import Coq.Vectors.Fin.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.Peano_dec.
Require Import Eqdep_dec.
Require Import Program.
Require Import GloballyReachable.

Require List.
Require Import ExprProps.
Require Export Stmt.

Section props.
Context `{sc:StaticConfig}.

Lemma subst_to_skip : forall {s x v}, s [v // x] = Skip -> s = Skip.
Proof.
  unfold subst; destruct s; simpl; intros; congruence.
Qed.

Section sync.

Lemma isAsync_not_isSync (s:stmt) : isAsync s = negb (isSync s).
Proof.
  induction s; simpl; intuition.
  rewrite negb_orb; congruence.
Qed.

Lemma isSync_not_isAsync (s:stmt) : isSync s = negb (isAsync s).
Proof.
  Hint Resolve isAsync_not_isSync negb_sym.
  auto. 
Qed.

Proposition isSync_xor_isAsync (s:stmt) : xorb (isSync s) (isAsync s) = true.
Proof.
  rewrite isAsync_not_isSync.
  destruct (isSync s); simpl; trivial.
Qed.


Lemma isSync_subst' {s x v} : isSync (subst_stmt s x v) = isSync s.
Proof.
  induction s; simpl; congruence.
Qed.

Lemma isSync_subst {s x v} : isSync s[v//x] = isSync s.
Proof.
  apply isSync_subst'.
Qed.

Lemma isAsync_subst' {s x v} : isAsync (subst_stmt s x v) = isAsync s.
Proof.
  induction s; simpl; congruence.
Qed.

Lemma isAsync_subst {s x v} :  isAsync s[v//x] = isAsync s.
Proof.
  apply isAsync_subst'.
Qed.

End sync.

(* instead of separating dynamic statements, as in the paper,
 we put all statements together into one type and define here a predicate
 classifying the dynamic statements *)
Definition isDynamic (s:stmt) :=
  match s with
      | DAt _ _ => true
      | DAsync _ => true
      | Finish (_::_) _ => true
      | _ => false
  end.

(* the free variables of a statement *)
Fixpoint free_vars (s:stmt) : list var :=
  match s with
    | Skip => nil
    | Throw e => free_vars_e e
    | Bind x' e s => (free_vars_e e) ++ (remove var_eqdec x' (free_vars s))
    | Assign e1 f e3 => (free_vars_e e1) ++ (free_vars_e e3)
    | Seq s1 s2 => (free_vars s1) ++ (free_vars s2)
    | At p x' e s => (free_vars_e e) ++ (remove var_eqdec x' (free_vars s)) 
    | Async s => (free_vars s)
    | Finish _ s => (free_vars s)
    | Catch s t => (free_vars s) ++ (free_vars t)
    | DAt p s => (free_vars s)
    | DAsync s => free_vars s
  end.

(* Closed (no free variables) at the top level of the statement *)
Definition isTopClosed (s:stmt) : bool := free_vars s ==b nil.

(* rewrite rules for topClosed *)
Lemma topClosed_skip : isTopClosed Skip = true.
Proof.
  unfold isTopClosed; simpl; trivial.
Qed.

Lemma topClosed_throw e : isTopClosed (Throw e) = (free_vars_e e ==b nil).
Proof.
  unfold isTopClosed; simpl; trivial.
Qed.

Lemma topClosed_seq a b : isTopClosed (Seq a b) = isTopClosed a && isTopClosed b.
Proof.
  unfold isTopClosed; simpl.
  destruct (free_vars a); simpl; trivial.
Qed.

Lemma topClosed_async s: isTopClosed (Async s) = isTopClosed s.
Proof.
  unfold isTopClosed; simpl; trivial.
Qed.

Lemma topClosed_finish μ s: isTopClosed (Finish μ s) = isTopClosed s.
Proof.
  unfold isTopClosed; simpl; trivial.
Qed.

Lemma topClosed_catch a b : isTopClosed (Catch a b) = isTopClosed a && isTopClosed b.
Proof.
  unfold isTopClosed; simpl.
  destruct (free_vars a); simpl; trivial.
Qed.

Lemma topClosed_dat p s: isTopClosed (DAt p s) = isTopClosed s.
Proof.
  unfold isTopClosed; simpl; trivial.
Qed.

Lemma topClosed_dasync s: isTopClosed (DAsync s) = isTopClosed s.
Proof.
  unfold isTopClosed; simpl; trivial.
Qed.

(* Only x may be free at the top level *)
Definition isTopAlmostClosed (x:var) (s:stmt)
  := match free_vars s with
       | nil => true
       | y::nil => x ==b y
       | _ :: _ :: _ => false
     end.

(* The sub-statement of any nested at statements must only have
   the appropriate (bound) variable free.  
   This ensures that we don't accidentally capture unintended variables
   across place transitions. *)
Fixpoint isPlaceClosed (s:stmt) : bool :=
  match s with
    | Skip => true
    | Throw e => true
    | Bind x' e s => (isPlaceClosed s)
    | Assign e1 f e3 => true
    | Seq s1 s2 => isPlaceClosed s1 && isPlaceClosed s2
    | At p x' e s => isTopAlmostClosed x' s && isPlaceClosed s
    | Async s => isPlaceClosed s
    | Finish μ s => isPlaceClosed s
    | Catch s t => isPlaceClosed s && isPlaceClosed t
    | DAt p s => isTopClosed s && isPlaceClosed s
    | DAsync s => isPlaceClosed s
  end.

(* A statements is closed if it is both closed at the top level
   and at every nested at statement *)
Definition isClosed (s:stmt) := isTopClosed s && isPlaceClosed s.


Ltac t_var 
  := idtac; repeat match goal with
       | [ H: context [ var_eqdec ?x ?y ] |- _ ] => destruct (var_eqdec x y); unfold equiv, complement in *; subst
       | [|- context [ var_eqdec ?x ?y ]] => destruct (var_eqdec x y); unfold equiv, complement in *; subst
       | [ H: context [ (@equiv_dec ?A ?B ?C ?D ?x ?y) ] |- _ ] => destruct (@equiv_dec A B C D x y); unfold equiv, complement in *
       | [|- context [ (@equiv_dec ?A ?B ?C ?D ?x ?y) ]] => destruct (@equiv_dec A B C D x y); unfold equiv, complement in *
     end.


Lemma free_vars_subst (s:stmt) x v : free_vars (s[v//x]) = (remove var_eqdec x (free_vars s)).
Proof.
  Hint Rewrite free_vars_subst_e : rewrites.
  revert x v. unfold subst.
  induction s; simpl; dt t_var; try congruence;
    rewrite remove_comm; congruence.
Qed.

Lemma free_vars_subst' (s:stmt) x v : free_vars (subst_stmt s x v) = (remove var_eqdec x (free_vars s)).
Proof.
  erewrite <- free_vars_subst; unfold subst; eauto.
Qed.

Lemma subst_nfree (s:stmt) x v : ~ In x (free_vars s) -> s[v//x] = s.
Proof.
  Hint Rewrite subst_nfree_e in_app_iff: rewrites.
  revert x v. unfold subst.
  induction s; simpl; dts t_var; try rewrite IHs; try rewrite IHs1, IHs2; try congruence;
    rewrite remove_in_iff in H1; auto.
Qed.

Lemma subst_nfree' (s:stmt) x v : ~ In x (free_vars s) -> subst_stmt s x v = s.
Proof. apply subst_nfree. Qed.

Lemma substs_idem (s:stmt) x v v' : s[v//x][v'//x] = s[v//x].
Proof.
  apply subst_nfree. rewrite  free_vars_subst. apply remove_nin.
Qed.


Lemma topClosed_nfree (s:stmt) : isTopClosed s = true -> forall x, ~ In x (free_vars s).
Proof.
unfold isTopClosed.
destruct (free_vars s); compute in *; intuition.
Qed.

Lemma topClosed_subst (s:stmt) : isTopClosed s = true -> forall x v, s[v//x] = s.
Proof.
  Hint Resolve subst_nfree topClosed_nfree.
  auto.
Qed.

Lemma topClosed_subst' (s:stmt) : isTopClosed s = true -> forall x v, subst_stmt s x v = s.
Proof. apply topClosed_subst. Qed.

Lemma closed_subst (s:stmt) : isClosed s = true -> forall x v, s[v//x] = s.
Proof.
  Hint Resolve topClosed_subst.
  unfold isClosed.
  dt auto.
Qed.

Lemma closed_subst' (s:stmt) : isClosed s = true -> forall x v, subst_stmt s x v = s.
Proof. apply closed_subst. Qed.

Lemma topAlmostClosed_subst' {s:stmt} z x v :
     isTopAlmostClosed z s = true 
  -> isTopAlmostClosed z (subst_stmt s x v) = true.
Proof.
  unfold isTopAlmostClosed.
  rewrite free_vars_subst'.
  destruct (free_vars s); simpl; trivial.
  destruct l; try discriminate.
  simpl. destruct (var_eqdec x v0); trivial.
Qed.

Lemma topAlmostClosed_subst {s:stmt} z x v :
     isTopAlmostClosed z s = true 
  -> isTopAlmostClosed z (s[v//x]) = true.
Proof. apply topAlmostClosed_subst'. Qed.

Lemma topAlmostClosed_subst_eq' {s:stmt} x v :
   isTopAlmostClosed x s = true 
-> isTopClosed (subst_stmt s x v) = true.
Proof.
  unfold isTopAlmostClosed, isTopClosed.
  rewrite free_vars_subst'; simpl.
  destruct (free_vars s); simpl; trivial.
  destruct l; try discriminate.
  simpl. destruct (var_eqdec x v0); trivial.
  dt idtac; congruence.
Qed.

Lemma topAlmostClosed_subst_eq {s:stmt} x v :
   isTopAlmostClosed x s = true 
-> isTopClosed (s[v//x]) = true.
Proof. apply topAlmostClosed_subst_eq'. Qed.
  
Lemma placeClosed_subst' {s:stmt} x v :
     isPlaceClosed s = true 
  -> isPlaceClosed (subst_stmt s x v) = true.
Proof. 
  Hint Resolve topAlmostClosed_subst'. 
  induction s; simpl; dt t_var; auto.
  rewrite topClosed_subst'; auto.
Qed.

Lemma placeClosed_subst {s:stmt} x v :
     isPlaceClosed s = true 
  -> isPlaceClosed (s[v//x]) = true.
Proof. apply placeClosed_subst'. Qed.

(* Does not have any dynamic statements in it *)
Fixpoint staticOnly (s:stmt) : bool
  := match s with
       | Skip => true
       | Throw e => true
       | Bind x' e s => staticOnly s
       | Assign e1 f e3 => true
       | Seq s1 s2 => staticOnly s1 && staticOnly s2
       | At p x' e s => staticOnly s
       | Async s => staticOnly s
       | Finish nil s => staticOnly s
       | Finish (_::_) s => false
       | Catch s t => staticOnly s && staticOnly t
       | DAt p s => false
       | DAsync s => false
     end.

Lemma staticOnly_not_dynamic {s} : staticOnly s = true -> isDynamic s = false.
Proof.
  destruct s; simpl; try congruence.
  destruct l; congruence.
Qed.

(* does not have any dynamic statements improperly nested inside statements 
   that are expected to be static only.  
   As we will see later, this property is preserved by our evaluation semantics *)
Fixpoint properStmt (s:stmt) : bool
  := match s with
    | Skip => true
    | Throw e => true
    | Bind x' e s => staticOnly s
    | Assign e1 f e3 => true
    | Seq s1 s2 => properStmt s1 && (if isSync s1 then staticOnly s2 else properStmt s2)
    | At p x' e s => staticOnly s
    | Async s => staticOnly s
    | Finish μ s => properStmt s
    | Catch s t => properStmt s && staticOnly t
    | DAt p s => properStmt s
    | DAsync s => properStmt s
  end.

Ltac t_var_sync := idtac; try match goal with 
    | [|- context [isSync ?s]] => destruct (isSync s)
  end; t_var.

(* staticOnly is stronger than properStmt *)
Lemma staticOnly_properStmt {s} : staticOnly s = true -> properStmt s = true.
Proof.
  induction s; simpl; dt t_var_sync; auto.
  destruct l; intuition.
Qed.

Lemma staticOnly_subst' s x v : staticOnly (subst_stmt s x v) = staticOnly s.
Proof.
  induction s; simpl; dt t_var; try congruence.
  destruct l; congruence.
Qed.

Lemma staticOnly_subst s x v : staticOnly s[v//x] = staticOnly s.
Proof. apply staticOnly_subst'. Qed.

Lemma properStmt_subst' s x v : properStmt (subst_stmt s x v) = properStmt s.
Proof.
  Hint Resolve staticOnly_subst' isSync_subst'.
  induction s; simpl; dt t_var; try congruence.
  rewrite <- IHs1, IHs2, isSync_subst'.
  dt t_var_sync. f_equal; auto.
  rewrite IHs1, staticOnly_subst'; auto.
Qed.

Lemma properStmt_subst s x v : properStmt s[v//x] = properStmt s.
Proof. apply properStmt_subst'. Qed.

(* A well formed statement is both proper and closed. *)
Definition wfStmt (s:stmt) := properStmt s && isClosed s.

Lemma staticOnly_isSync t : 
  staticOnly t = true ->
  isSync t = true.
Proof.
  induction t; simpl; dts idtac.
Qed.

Proposition proper_seq_sync_sync {s t} : 
  properStmt (Seq s t) = true ->
  isSync s = true ->
  isSync t = true.
Proof.
  Hint Resolve staticOnly_isSync.
  simpl; intros prop iss.
  rewrite iss in prop.
  dts idtac.
Qed.

Section complexity.

(* A complexity measure for statements.  This is useful for induction.  
   In particular, it allows for induction to coexist with substitution.
   The result of a substitution is not structurally related to the original statement,
   however it has the same complexity, allowing for use of the induction hypothesis. *)
Fixpoint complexity_s (s:stmt) 
  := match s with
        | Skip => 1
        | Throw e => complexity_e e
        | Bind x e s => complexity_e e + complexity_s s
        | Assign e1 f e2 => complexity_e e1 + complexity_e e2
        | Seq s1 s2 => 1 + complexity_s s1 + complexity_s s2
        | At p x e s => 3 + complexity_e e + complexity_s s
        | Async s => 2 + complexity_s s
        | Finish ve s => 1 + complexity_s s
        | Catch s t => 1 + complexity_s s + complexity_s t
        | DAt p s => 1 + complexity_s s
        | DAsync s => 1 + complexity_s s
     end.

Require Import Lt.
Require Import List.

(* critical property of the complexity measure: it is preserved by substitution *)
Lemma complexity_s_subst s x v : complexity_s s[v//x] = complexity_s s.
Proof.
  Hint Rewrite complexity_e_subst : rewrites.
  induction s; simpl; dt idtac; auto;
    destruct (@equiv_dec var (@eq var) (@eq_equivalence var) oid_eqdec x v0); simpl; auto.
Qed.

Hint Rewrite complexity_s_subst : rewrites.

(* The base case for induction over the complexity of a statement is trivial *)
Lemma complexity_s_0 {s} : complexity_s s <= 0 -> False.
Proof.
  Hint Resolve complexity_e_0.
  intro cs; induction s; simpl in cs; eauto; try omega.
  apply IHs. omega.
  assert (complexity_e e <= 0) by omega.
  eauto.
Qed.

End complexity.

(* the "free" (embedded) values of a statement *)
Fixpoint free_vals (p:place) (s:stmt)  
    := match s with
        | Skip => nil
        | Throw e => free_vals_e p e
        | Bind x e s => free_vals_e p e ++ free_vals p s
        | Assign e1 f e2 => free_vals_e p e1 ++ free_vals_e p e2
        | Seq s1 s2 => free_vals p s1 ++ free_vals p s2
        | At q x e s => free_vals_e p e ++ free_vals q s
        | Async s => free_vals p s
        | Finish ve s => ((map (fun x => (p, x)) ve)) ++ free_vals p s
        | Catch s t => free_vals p s ++ free_vals p t
        | DAt q s => free_vals q s
        | DAsync s =>  free_vals p s
     end.

Lemma free_vals_subst_in {p:place} {s:stmt} v x {a}:
  isPlaceClosed s = true ->
  In a (free_vals p s) -> 
  In a (free_vals p s[v//x]).
Proof.
  Hint Resolve free_vals_e_subst_in.
  dependent induction s; simpl in *; try repeat rewrite in_app_iff in * |- *; try solve [dts t_var]; intuition; t_var; subst; eauto.
  - right. unfold isTopAlmostClosed in *.
    case_eq (free_vars s); [intros eqs| intros vv l eqs]; rewrite eqs in H.
    + rewrite subst_nfree'; auto; rewrite eqs; intuition.
    + destruct l; dt idtac.
      unfold equiv in *; subst.
      rewrite subst_nfree'; auto; rewrite eqs; simpl in *; intuition.
  - rewrite topClosed_subst'; dt idtac.
Qed.

Lemma free_vals_in_subst {p:place} {s:stmt} {v x a}:
  isPlaceClosed s = true ->
  In a (free_vals p s[v//x]) ->
  In a ((p,v)::(free_vals p s)).
Proof.
  Hint Resolve free_vals_e_in_subst'.
  dependent induction s; simpl in *; auto 3;   try repeat rewrite in_app_iff in * |- *;
  intuition; 
repeat match goal with
      [H:In _ (free_vals_e _ _[_//_]) |- _] => apply free_vals_e_in_subst in H
  end;
 dt t_var; intuition;
 try match goal with 
         [H:isPlaceClosed _ = true, H1:In _ _ |- _] => 
         first[destruct (IHs _ _ _ H H1)
              | destruct (IHs1 _ _ _ H H1) 
              | destruct (IHs2 _ _ _ H H1)]; intuition
     end.
  - unfold isTopAlmostClosed in H. 
    case_eq (free_vars s); [intros eqs| intros vv l eqs]; rewrite eqs in H.
    + rewrite subst_nfree' in H1; auto; rewrite eqs; intuition.
    + destruct l; dt idtac.
      unfold equiv in *; subst.
      rewrite subst_nfree' in H1; auto; rewrite eqs; simpl in *; intuition.
  - rewrite topClosed_subst' in H0; auto.
Qed.

Section gwf.
Context {Heap:@HEAP oid oid_eqdec obj}.

Lemma gwf_vals_free_vals_e_on_subst_b {g p e x v} :
  gwf_vals g (free_vals_e p e[v//x]) ->
  gwf_vals g (free_vals_e p e).
Proof.
  Hint Resolve free_vals_e_subst_in.
  intros.
  eapply gwf_vals_incl_f; eauto.
  red; eauto.
Qed.

Lemma gwf_vals_free_vals_e_on_subst_f {g p e x v} :
  gwf_val g p v ->
  gwf_vals g (free_vals_e p e) ->
  gwf_vals g (free_vals_e p e[v//x]).
Proof.
  intros.
  poses (gwf_vals_cons H H0).
  eapply (gwf_vals_incl_f P).
  red; intros.
  poses (free_vals_e_in_subst H1); simpl in *; intuition.
Qed.

Lemma gwf_vals_free_vals_subst_b {g p s x v} :
  isPlaceClosed s = true ->
  gwf_vals g (free_vals p s[v//x]) ->
  gwf_vals g (free_vals p s).
Proof.
  Hint Resolve free_vals_subst_in.
  intros.
  eapply gwf_vals_incl_f; eauto.
  red; eauto.
Qed.

Lemma gwf_vals_free_vals_on_subst_f {g p s x v} :
  isPlaceClosed s = true ->
  gwf_val g p v ->
  gwf_vals g (free_vals p s) ->
  gwf_vals g (free_vals p s[v//x]).
Proof.
  intros.
  poses (gwf_vals_cons H0 H1).
  eapply (gwf_vals_incl_f P).
  red; intros.
  poses (free_vals_in_subst H H2); simpl in *; intuition.
Qed.

End gwf.

Lemma wfStmt_catch_skip s:
  wfStmt (Catch s Skip) = wfStmt s.
Proof.
  unfold wfStmt, isClosed, isTopClosed; simpl.
  rewrite app_nil_r.
  repeat rewrite andb_true_r; trivial.
Qed.

Lemma wfStmt_finish_nil s : 
  wfStmt (Finish nil s) = wfStmt s.
Proof.
  reflexivity.
Qed.

Fixpoint size_s (s:stmt) : nat :=
  match s with
   | Skip => 1
   | Throw _ => 1
   | Bind _ _ s => S (size_s s)
   | Assign _ _ _ => 1
   | Seq s1 s2 => S (size_s s1 + size_s s2)
   (* At-Statement-with-Binding *)
   | At _ _ _ s =>  S (size_s s)
   | Async s => S (size_s s)
   | Finish μ s => S (size_s s)
   | Catch s t => S (size_s s + size_s t)
   | DAt _ s => S (size_s s)
   | DAsync s => S (size_s s)
  end.

Lemma size_s_n0 s : size_s s > 0.
Proof.
  destruct s; simpl; omega.
Qed.

Lemma substs_commute {s:stmt} {x1 v1 x2 v2} : 
  x1 <> x2 ->
  s[v1//x1][v2//x2] = s[v2//x2][v1//x1].
Proof.
  Hint Resolve subste_commute'.
  induction s; unfold subst; simpl; unfold subst in *; simpl; trivial; intros;
  repeat try rewrite subste_commute' by assumption; try solve[auto | f_equal; auto].
  - dt t_var; try congruence.
    rewrite IHs; auto.
  - f_equal; auto.
    dt t_var; auto.
Qed.

End props.

Hint Rewrite @topClosed_skip @topClosed_throw @topClosed_seq @topClosed_async @topClosed_finish @topClosed_catch @topClosed_dat @topClosed_dasync : rewrites.
Hint Rewrite @complexity_s_subst : rewrites.
Hint Resolve size_s_n0.