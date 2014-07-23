(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Encodes the semantics of expressions in TX10 (and Resilient X10) *)
Require Export Assoc2.
Require Export Auxiliary.
Require Export Stmt.
Require Export CopyVal.
Require Export TransitionLabels.

Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.EquivDec.
Require Import Program.

Section semantics.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

(* predefined values for exceptions.  Rather than introduce a new value type, we simply use natural numbers *)
Definition FieldNotFoundException : val := Nat 0.
Definition BadPlaceException : val := Nat 1.
Definition BadTypeException : val := Nat 2.
Definition DeadPlaceException : val := Nat 3.

(* expression evaluation relation *)

(* A=(e,h) evaluates to B=(e',h') at place p, with transition label t *)
Reserved Notation "A '-e[' p | t ']->' B" (at level 70).
(* A=(e,h) evaluates to configuration B at place p, with transition label t.  
   B may be an expression,heap pair or it may be a terminal heap *)
Reserved Notation "A '-e[' p | t ']->?' B" (at level 70).
(* A=(e,h) evaluates to the terminal heap B=h' at place p, with transition label t *)
Reserved Notation "A '-e[' p | t ']->!' B" (at level 70).

Inductive evale : place -> trans_type -> expr * heap -> (expr * heap) + heap -> Prop :=
  | ENewCtxt :
      forall p λ e h e' h',
        (e,h) -e[p | λ]-> (e',h') ->
        forall l1 f l2, 
          allVals l1 = true -> 
          (New (l1 ++ (f,e) :: l2),h) -e[p | λ]-> (New (l1 ++ (f,e') :: l2), h')
  | ENewCtxtTerm :
      forall p λ e h h',
        (e,h) -e[p | λ]->! h' ->
        forall l1 f l2
        , allVals l1 = true -> 
          (New (l1 ++ (f,e) :: l2),h) -e[p | λ]->! h'
  | ENewObj : 
      forall p l h (pf:allVals l = true),
        let oh := new h (toCompactVals l pf) in
        (New l,h) -e[p | ε]-> (Val (Object (snd oh)), (fst oh))

  | ESelectCtxt : 
      forall p λ e1 h e1' h',
        (e1,h) -e[p | λ]-> (e1',h') ->
        forall f,
          (Select e1 f,h) -e[p | λ]-> (Select e1' f, h')
  | ESelectCtxtTerm : 
      forall p λ e1 h h',
        (e1,h) -e[p | λ]->! h' ->
        forall f,
          (Select e1 f,h) -e[p | λ]->! h'
  | ESelect : 
      forall p oid f h obj res,
        h[@oid] = Some obj ->
        obj [@ f] = Some res ->
        (Select (Val (Object oid)) f, h) -e[p | ε]-> (Val res, h)
  | ESelectBad : 
      forall p v f h,
        match v with
          | GlobalObject _ _ => True
          | Nat _ => True
          | Object oid => match h[@oid] with
                            | None => True
                            | Some obj => obj[@ f] = None
                          end 
        end ->
        (Select (Val v) f, h) -e[p | ⊗ (singleton FieldNotFoundException) ]->! h

  | EMkGlobalCtxt :
      forall p λ e h e' h',
        (e,h) -e[p | λ]-> (e',h') ->
        (MkGlobal e,h) -e[p | λ]-> (MkGlobal e', h')
  | EMkGlobalCtxtTerm :
      forall p λ e h h',
        (e,h) -e[p | λ]->! h' ->
        (MkGlobal e,h) -e[p | λ]->! h'
  | EMkGlobal : 
      forall p oid h,
        (MkGlobal (Val (Object oid)),h) -e[p | ε]-> (Val (GlobalObject p oid), h)
  | EMkGlobalBad : 
      forall p v h,
        match v with
          | Nat _ => True
          | Object oid => False
          | GlobalObject p' oid => True
        end -> 
        (MkGlobal (Val v),h) -e[p | ⊗ (singleton BadTypeException)]->! h

  | EGetGlobalCtxt :
      forall p λ e h e' h',
        (e,h) -e[p | λ]-> (e',h') ->
        (GetGlobal e,h) -e[p | λ]-> (GetGlobal e', h')
  | EGetGlobalCtxtTerm :
      forall p λ e h h',
        (e,h) -e[p | λ]->! h' ->
        (GetGlobal e,h) -e[p | λ]->! h'
  | EGetGlobal : 
      forall p oid h,
        (GetGlobal (Val (GlobalObject p oid)),h) -e[p | ε]-> (Val (Object oid), h)
  | EGetGlobalBad : 
      forall p v h,
        match v with
          | Nat _ => True
          | Object oid => True
          | GlobalObject p' oid => p <> p'
        end -> 
        (GetGlobal (Val v),h) -e[p | ⊗ (singleton BadPlaceException)]->! h
                                       
where "A '-e[' p | t ']->?' B" := (evale p t A B)
  and "A '-e[' p | t ']->!' B" := (evale p t A (inr B))
  and "A '-e[' p | t ']->' B" := (evale p t A (inl B)).

Notation "A '-e[' p | t ']->?' B" := (evale p t A B).
Notation "A '-e[' p | t ']->!' B" := (evale p t A (inr B)).
Notation "A '-e[' p | t ']->' B" := (evale p t A (inl B)).

(* we can also define the transitive closure of the evaluation relation,
  where all steps except for the last one must have an ε transition label *)

Reserved Notation "A '-e[' p | t ']->*' B" (at level 70).
Reserved Notation "A '-e[' p | t ']->*?' B" (at level 70).
Reserved Notation "A '-e[' p | t ']->*!' B" (at level 70).

Inductive eval_e_star : place -> trans_type -> 
                 expr * heap -> (expr*heap) + heap -> Prop :=
  | eval_e_star_refl : forall p eh, 
                       eh -e[ p | ε]->* eh
  | eval_e_star_step : forall {p eh λ eh' eh''}, 
                         eh -e[ p | ε]->* eh'
                      -> eh' -e[ p | λ]->? eh''
                      -> eh -e[ p | λ]->*? eh''
  where "A '-e[' p | t ']->*?' B" := (eval_e_star p t A B)
 and "A '-e[' p | t ']->*!' B" := (eval_e_star p t A (inr B))
 and "A '-e[' p | t ']->*' B" := (eval_e_star p t A (inl B)).

Notation "A '-e[' p | t ']->*?' B" := (eval_e_star p t A B).
Notation "A '-e[' p | t ']->*!' B" := (eval_e_star p t A (inr B)).
Notation "A '-e[' p | t ']->*' B" := (eval_e_star p t A (inl B)).

Lemma eval_e_star_trans {p λ eh} eh' {eh''}:
    eh -e[ p | ε]->* eh'
 -> eh' -e[ p | λ]->*? eh''
 -> eh -e[ p | λ]->*? eh''.
Proof.
  Hint Constructors eval_e_star.
  intros ev1 ev2; revert ev1.
  induction ev2; eauto.
Qed.

Lemma eval_e_eval_e_star {p λ eh eh'} :
    eh -e[ p | λ]->? eh'
 -> eh -e[ p | λ]->*? eh'.
Proof.
  eauto.
Qed.

End semantics.

Notation "A '-e[' p | t ']->?' B" := (evale p t A B)  (at level 70) : eval_relations.
Notation "A '-e[' p | t ']->!' B" := (evale p t A (inr B))  (at level 70) : eval_relations.
Notation "A '-e[' p | t ']->' B" := (evale p t A (inl B))  (at level 70) : eval_relations.

Notation "A '-e[' p | t ']->*?' B" := (eval_e_star p t A B) (at level 70): eval_relations.
Notation "A '-e[' p | t ']->*!' B" := (eval_e_star p t A (inr B)) (at level 70) : eval_relations.
Notation "A '-e[' p | t ']->*' B" := (eval_e_star p t A (inl B)) (at level 70): eval_relations.

Open Scope eval_relations.

