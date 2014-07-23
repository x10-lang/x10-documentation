(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Defines the syntax of expressions for TX10 and Resilient X10 *)
Require Export Auxiliary.
Require Import Eqdep_dec.

Require List.

Section expr.

Context `{sc:StaticConfig}.

Inductive expr : Set :=
  | Val : val -> expr
  | Var : var -> expr
  | Select : expr -> fname -> expr
  | New :  list (fname*expr) -> expr
  | GetGlobal : expr -> expr
  | MkGlobal : expr -> expr.

Global Instance subst_expr : Subst expr var val :=
 { subst := fix subste (e:expr) (x:var) (v:val) : expr :=
   match e with
     | Val v => Val v
     | Var x' => if x == x' then Val v else Var x'
     | Select e f => Select (subste e x v) f
     | GetGlobal e => GetGlobal (subste e x v)
     | MkGlobal e => MkGlobal (subste e x v)
     | New lee => New (List.map (fun ee => ((fst ee), subste (snd ee) x v)) lee)
   end}.

Definition isVal (e:expr) :=
  match e with
    | Val _ => true
    | _ => false
  end.


Lemma isVal_true {f} : isVal f = true -> {v |f = Val v}.
Proof.
  destruct f; simpl; intros; try discriminate. 
  eauto.
Qed.

Definition allVals (a:list (fname*expr)) := forallb isVal (domain (mswap a)).

Program Fixpoint toVals' (e:list (fname*expr)) (pfv:allVals e = true) : list (fname*val)
  := match e with
       | nil => nil
       | (fn, y')::ls => (fn,match y' with
                     | Val y => y
                     | _ => _
                   end)::(toVals' ls _)
     end.
Next Obligation.
simpl in *; unfold isVal in *.
unfold allVals, isVal in pfv; simpl in pfv.
repeat rewrite andb_true_iff in *.
destruct pfv.
destruct y'; intuition.
Defined.
Next Obligation.
unfold allVals, isVal in pfv; simpl in pfv.
repeat rewrite andb_true_iff in *.
intuition.
Defined.

Lemma toVals'_dom e pfv : domain (toVals' e pfv) = domain e.
Proof.
  induction e; [intuition|].
  destruct a; destruct e0; simpl; congruence.
Qed.

Hint Rewrite toVals'_dom : rewrites.

Lemma toVals'_nodup e pfv : NoDup (domain e) -> NoDup (domain (toVals' e pfv)).
Proof.
  dt idtac.
Qed.  

Lemma obj_compact_none {A B:Type} {dec:EqDec A equiv} (l:list(A*B)) a :
  l[@a] = None -> (obj_compact l)[@a] = None.
Proof.
  revert a.
  induction l; simpl; auto; intros.
  destruct a. destruct (a == a0); unfold equiv, complement in *; subst.
  - rewrite lookup_cons_eq in H; discriminate.
  - rewrite lookup_cons_neq in H; auto.
    destruct (l[@a]); auto.
    rewrite lookup_cons_neq; auto.
Qed.
    
Lemma obj_compact_nd {A B:Type}  {dec:EqDec A equiv} (l:list(A*B)):
  NoDup (domain (obj_compact l)).
Proof.
Hint Constructors NoDup.
induction l; simpl; auto.
destruct a.
case_eq (l[@a]); auto.
simpl; constructor; auto.
apply lookup_none_nin.
apply obj_compact_none; auto.
Qed.

Definition toCompactVals (e:list (fname*expr)) (pfv:allVals e = true) : obj
  :=  build_obj (obj_compact (toVals' e pfv)) (obj_compact_nd _).

Lemma toCompactVals_cons_some {l pf0 f v} e0 pf1 :
          (toCompactVals l pf0)[@f] = Some v ->
          toCompactVals ((f, Val e0) :: l) pf1 = toCompactVals l pf0.
Proof.
  unfold toCompactVals; intros.
  rewrite obj_lookup_simpl in H; simpl in H.
  apply lookup_in in H.
  apply build_obj_inj.
  replace (toVals' ((f, Val e0) :: l) pf1) with 
  ((f, e0)::toVals' l pf0).
  eapply obj_compact_in; eauto.
  simpl. f_equal. f_equal. apply UIP_dec; apply bool_dec.
Qed.

Lemma toCompactVals_pf_irrel e pfv1 pfv2 : toCompactVals e pfv1 = toCompactVals e pfv2.
Proof.
  f_equal. eapply UIP_dec. apply bool_dec.
Qed.

(* The induction principle automatically generated for expr is not sufficiently strong,
   since it loses the induction hypothesis for the list used by New.
   Here, we (manually) define a stronger induction principle *)
Definition expr_indF (P : expr -> Prop) (f : forall v : val, P (Val v))
  (f0 : forall v : var, P (Var v))
  (f1 : forall e : expr, P e -> forall ff, P (Select e ff))
  (f2 : forall l : list (fname * expr), Forall (fun ab => P (snd ab)) l -> P (New l))
  (f3 : forall e : expr, P e -> P (GetGlobal e))
  (f4 : forall e : expr, P e -> P (MkGlobal e)) :=
fix F (e : expr) : P e :=
  match e as e0 return (P e0) with
  | Val v => f v
  | Var v => f0 v
  | Select e0 ff => f1 e0 (F e0) ff
  | New l => f2 l ((
                  fix FN (l:list (fname * expr))
                  : Forall (fun ab => P (snd ab)) l
                  := match l with 
                       | nil => Forall_nil _
                       | x::xs => @Forall_cons _ (fun ab => P (snd ab)) x xs (F (snd x)) (FN xs)
                     end) l)
                     
  | GetGlobal e0 => f3 e0 (F e0)
  | MkGlobal e0 => f4 e0 (F e0)
  end.

(* The same as Forall (from the standard library), but for P with sort Type instead of sort Prop *)
Inductive Forallt {A : Type} (P : A -> Type) : list A -> Type :=
    Forallt_nil : Forallt P nil
  | Forallt_cons : forall (x : A) (l : list A),
                  P x -> Forallt P l -> Forallt P (x :: l).


(* A recursive principle for expressions, stronger then the one that is automatically derived.
   The main difference from the above induction principle is that this work on P at sort Type (not just Prop) *)
Definition expr_rectF (P : expr -> Type) (f : forall v : val, P (Val v))
  (f0 : forall v : var, P (Var v))
  (f1 : forall e : expr, P e -> forall ff : fname, P (Select e ff))
  (f2 : forall l : list (fname * expr), Forallt (fun ab => (P (snd ab))) l -> P (New l))
  (f3 : forall e : expr, P e -> P (GetGlobal e))
  (f4 : forall e : expr, P e -> P (MkGlobal e)) :=
fix F (e : expr) : P e :=
  match e as e0 return (P e0) with
  | Val v => f v
  | Var v => f0 v
  | Select e0 ff => f1 e0 (F e0) ff
  | New l => f2 l ((
                  fix FN (l:list (fname * expr))
                  : Forallt (fun ab => (P (snd ab))) l
                  := match l with 
                       | nil => Forallt_nil _
                       | x::xs => @Forallt_cons _ (fun ab => (P (snd ab))) x _ ((F (snd x))) (FN xs)
                     end) l)
                     
  | GetGlobal e0 => f3 e0 (F e0)
  | MkGlobal e0 => f4 e0 (F e0)
  end.

End expr.

Hint Rewrite @toVals'_dom : rewrites.
