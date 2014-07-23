(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Definition and lemmas about expressions *)
Require Export Auxiliary.
Require Import Coq.Vectors.Fin.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Arith.Peano_dec.
Require Import Eqdep_dec.
Require Import Program.
Require Import Assoc2.
Require List.
Require Export Expr.

Section props.
Context `{sc:StaticConfig}.

(* The free variables in expr *)
Fixpoint free_vars_e (e:expr) : list var :=
 match e with
     | Val v => nil
     | Var x' => x'::nil
     | Select e f => (free_vars_e e)
     | GetGlobal e => free_vars_e e
     | MkGlobal e => free_vars_e e
     | New lee => List.fold_right (fun b a => ((free_vars_e (snd b)) ++ a)) nil lee
   end.

Ltac t_var 
  := idtac; repeat match goal with
       | [ H: context [ var_eqdec ?x ?y ] |- _ ] => destruct (var_eqdec x y); unfold equiv, complement in *; subst
       | [|- context [ var_eqdec ?x ?y ]] => destruct (var_eqdec x y); unfold equiv, complement in *; subst
       | [ H: context [ (@equiv_dec ?A ?B ?C ?D ?x ?y) ] |- _ ] => destruct (@equiv_dec A B C D x y); unfold equiv, complement in *
       | [|- context [ (@equiv_dec ?A ?B ?C ?D ?x ?y) ]] => destruct (@equiv_dec A B C D x y); unfold equiv, complement in *
     end.

Lemma free_vars_subst_e (e:expr) x v : free_vars_e (e[v//x]) = (remove var_eqdec x (free_vars_e e)).
Proof.
  revert x v. unfold subst.
  induction e using expr_indF; simpl; dt t_var; try congruence.
  revert H; induction l; simpl in *; inversion 1; dts congruence.
Qed.

Lemma subst_nfree_e (e:expr) x v : ~ In x ( free_vars_e e) -> e[v//x] = e.
Proof.
  intros; unfold subst.
  induction e using expr_indF; simpl; dt t_var; intuition; try congruence.
  induction l; simpl in *; trivial.
  match goal with
      [|- New (?a::?l) = New (?a'::?l')] => cut (a = a' /\ New l = New l');
                                           [destruct 1 as [? GGG]; inversion GGG; congruence|]
  end.
  inversion H0; subst.
  destruct a; simpl in *.
  repeat rewrite in_app_iff in H.
  rewrite H3, IHl; auto.
Qed.

Lemma subste_idem (e:expr) x v v' : e[v//x][v'//x] = e[v//x].
Proof.
  apply subst_nfree_e. rewrite  free_vars_subst_e. apply remove_nin.
Qed.

(* values are not variables *)
Lemma isVal_closed {e} : isVal e = true -> free_vars_e e = nil.
Proof.
  destruct e; simpl in *; intuition.
Qed.

Lemma allVals_closed {l} : allVals l = true -> 
   fold_right
     (fun (b : fname * expr) (a : list var) => free_vars_e (snd b) ++ a)
     nil l = nil.
Proof.
Proof.
  unfold allVals; rewrite forallb_forall, <- Forall_forall.
  induction l; simpl in *; trivial; intros.
  inversion H; subst.
  rewrite IHl; auto.
  rewrite isVal_closed; auto.
Qed.

Section complexity.

(* a complexity metric on expressions, useful for some inductions *)
Fixpoint complexity_e (e:expr) 
  :=  match e with
     | Val v => 1
     | Var x' => 1
     | Select e f => 1 + (complexity_e e)
     | GetGlobal e => 1 + (complexity_e e)
     | MkGlobal e =>  1 + (complexity_e e)
     | New lee => 2 + (fold_right (fun fe r => 1 + (complexity_e (snd fe) + r)) 0 lee)
   end.

Require Import Plus.

Lemma compl_fr_app {A} {l1 l2:list (A*expr)} : (fold_right (fun fe r => 1 + (complexity_e (snd fe) + r)) 0 (l1 ++ l2)) =
                      (fold_right (fun fe r => 1 + (complexity_e (snd fe) + r)) 0 l1) + 
                      (fold_right (fun fe r => 1 + (complexity_e (snd fe) + r)) 0 l2).
Proof.
  induction l1; simpl; trivial.
  rewrite <- plus_assoc; auto.
Qed.

Require Import Lt.

Lemma complexity_e_subst e x v : complexity_e e[v//x] = complexity_e e.
Proof.
  dependent induction e using expr_indF; unfold subst in *; simpl; auto.
  - destruct (@equiv_dec var (@eq var) (@eq_equivalence var) oid_eqdec x v); simpl; auto.
  - erewrite fold_right_map. do 2 f_equal. apply fold_right_equiv.
    rewrite Forall_forall in H; eauto.
Qed.

Hint Rewrite complexity_e_subst : rewrites.

Lemma complexity_e_0 {e} : complexity_e e <= 0 -> False.
Proof.
  intro ce; induction e; simpl in ce; omega.
Qed.

End complexity.

(* The "free" (embedded) values in expr *)
Fixpoint free_vals_e (p:place) (e:expr) := 
  match e with
    | Val v => singleton (p,v)
    | Var x' => nil
    | Select e f => free_vals_e p e
    | GetGlobal e => free_vals_e p e
    | MkGlobal e =>  free_vals_e p e
    | New lee => List.fold_right (fun a b => free_vals_e p (snd a) ++ b) nil lee
  end.


Lemma free_vals_e_subst_in {p:place} {e:expr} v x {a}:
  In a (free_vals_e p e) -> 
  In a (free_vals_e p e[v//x]).
Proof.
  revert x v. unfold subst, incl.
  induction e using expr_indF; simpl; dt t_var; intuition; try congruence.
  rewrite fold_right_map.
  rewrite <- fold_right_flat_map in H0 |- *.
  apply in_flat_map in H0.
  apply in_flat_map.
  rewrite Forall_forall in *.
  dts idtac.
Qed.

Lemma free_vals_e_in_subst {p:place} {e:expr} {v x a}:
  In a (free_vals_e p e[v//x]) -> 
  In a ((p,v)::(free_vals_e p e)).
Proof.
  revert x v. unfold subst, incl.
  induction e using expr_indF; simpl; dt t_var; intuition; eauto; try congruence.
  rewrite fold_right_map in H0.
  rewrite <- fold_right_flat_map in H0 |- *.
  apply in_flat_map in H0.
  rewrite Forall_forall in *.
  dt idtac.
  destruct ((p,v)==(p0,v0)); intuition; unfold equiv, complement.
  right.
  apply in_flat_map.
  destruct (H _ H0 _ _ H1); intuition; eauto.
Qed.

Lemma free_vals_e_in_subst' {p:place} {e:expr} {v x a}:
  In a (free_vals_e p (subst_expr e x v)) -> 
  In a ((p,v)::(free_vals_e p e)).
Proof.
  poses @free_vals_e_in_subst.
  unfold subst in P.
  eauto.
Qed.


Ltac isval_tac
  := match goal with
       | [H: isVal ?f = true |- _ ] => apply isVal_true in H; destruct H; subst
     end.

Program Definition asVal e (pfv:isVal e = true) : val
  := match e with
       | Val y => y
       | _ => _
     end.
Solve Obligations using (program_simpl; intros; isval_tac; intuition).


Lemma toVals'_split f e l pf : 
  exists pf1 pf2,
    (toVals' ((f, e) :: l) pf) = (f, asVal e pf1)::toVals' l pf2.
Proof.
  poses pf.
  unfold allVals in P; simpl in P;
  rewrite andb_true_iff in P; destruct P.
  exists H. simpl.
  poses H. isval_tac.
  eauto.
Qed.

Lemma toVals_lookup_none {l f pf}:
  lookup_assoc (toVals' l pf) f = None ->
  lookup_assoc l f = None.
Proof.
  induction l; [intuition|].
  destruct a.
  destruct (toVals'_split f0 e l pf) as [pf1 [pf2 pfeq]].
  rewrite pfeq. simpl.
  destruct (@equiv_dec fname (@eq fname) (@eq_equivalence fname) oid_eqdec f f0); eauto.
  discriminate. 
Qed.

Lemma toVals_lookup_some {l f pf v}:
  lookup_assoc (toVals' l pf) f = Some v ->
  lookup_assoc l f = Some (Val v).
Proof.
  induction l; [discriminate|].
  destruct a.
  destruct (toVals'_split f0 e l pf) as [pf1 [pf2 pfeq]].
  rewrite pfeq. simpl.
  destruct (@equiv_dec fname (@eq fname) (@eq_equivalence fname) oid_eqdec f f0); eauto.
  poses pf1; isval_tac; simpl.
  congruence.
Qed.

Lemma obj_compact_toVals_lookup {l pf f v} :
  (toCompactVals l pf)[@f] = Some v ->
  (obj_compact l)[@f] = Some (Val v).
Proof.
  revert f v.
  induction l; simpl in *; try discriminate.
  intros f v eqf.
  destruct a; simpl in *.

  unfold toCompactVals in *.
  unfold lookup, obj_lookup in *.
  unfold build_obj, proj1_sig in *.
  destruct (toVals'_split f0 e l pf) as [pf1 [pf2 eqsplit]].
  rewrite eqsplit in eqf.
  poses pf1; isval_tac.
  simpl in eqf.
  unfold lookup, obj_lookup in *.
  case_eq (lookup_assoc (toVals' l pf2) f0); [intros v' H|intros H]; rewrite H in *;
  [rewrite (toVals_lookup_some H) | rewrite (toVals_lookup_none H)]; eauto.
  clear eqsplit.
  simpl in *.
  destruct (@equiv_dec fname (@eq fname) (@eq_equivalence fname) oid_eqdec f f0); eauto; congruence.
Qed.

Lemma allVals_subst {l} x v : 
  allVals l = true -> 
  (map (fun ee : fname * expr => (fst ee, subst_expr (snd ee) x v)) l) = l.
Proof.
  unfold allVals; rewrite forallb_forall, <- Forall_forall; intros.
  induction l; simpl; trivial.
  inversion H; subst.
  rewrite IHl; trivial.
  poses subst_nfree_e. unfold subst in P.
  destruct a.
  rewrite P; auto.
  rewrite isVal_closed; intuition.
Qed.

Lemma subste_commute {e:expr} {x1 v1 x2 v2} : 
  x1 <> x2 ->
  e[v1//x1][v2//x2] = e[v2//x2][v1//x1].
Proof.
  intros; unfold subst.
  induction e using expr_indF; unfold subst; simpl; dt t_var; intuition; try congruence.
  repeat rewrite map_map; simpl.
  f_equal.
  apply map_eq.
  rewrite Forall_forall in H0 |- *; intros.
  f_equal; auto.
Qed.

Lemma subste_commute' {e:expr} {x1 v1 x2 v2} : 
  x1 <> x2 ->
  subst_expr (subst_expr e x1 v1) x2 v2 = subst_expr (subst_expr e x2 v2) x1 v1.
Proof.
  apply subste_commute.
Qed.

(* equality for expressions is decidable (computable) *)
Global Instance expr_eqdec : EqDec expr eq.
Proof.
intros e1.
induction e1 using expr_rectF; unfold subst in *; simpl; auto; intros e2;
destruct e2; unfold equiv, complement; try solve[right; inversion 1].
- poses (val_eqdec v v0); unfold equiv, complement in *; intuition congruence.
- poses (var_eqdec v v0); unfold equiv, complement in *; intuition congruence.
- poses (fname_eqdec f ff); poses (IHe1 e2); unfold equiv, complement in *; intuition congruence.
- revert l0; induction l; destruct l0; inversion H.
  + intuition.
  + right; inversion 1. 
  + right; inversion 1. 
  + subst. destruct a; destruct p.
    poses (fname_eqdec f f0).  specialize (H2 e0). simpl in *.
    specialize (IHl H3 l0). unfold equiv, complement in *. intuition congruence.
- poses (IHe1 e2); unfold equiv, complement in *; intuition congruence.
- poses (IHe1 e2); unfold equiv, complement in *; intuition congruence.
Qed.

Lemma fname_expr_eqdec : forall x0 y : fname*expr, {x0 = y} + {x0 <> y}.
Proof.
  decide equality.
  apply expr_eqdec.
  apply fname_eqdec.
Qed.

End props.

Hint Rewrite @complexity_e_subst : rewrites.
