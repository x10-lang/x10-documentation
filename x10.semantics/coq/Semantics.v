(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Encodes the semantics of statements in TX10 *)
Require Export Assoc2.
Require Export Auxiliary.
Require Export Stmt.
Require Export CopyVal.
Require Export TransitionLabels.

Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.EquivDec.
Require Import Program.
Require Export ExprSemantics.

Section semantics.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Reserved Notation "A '-[' p | t ']->' B" (at level 70).
Reserved Notation "A '-[' p | t ']->?' B" (at level 70).
Reserved Notation "A '-[' p | t ']->!' B" (at level 70).

Inductive eval : place -> trans_type -> 
                 stmt * global_heap -> (stmt*global_heap) + global_heap -> Prop :=
  (* SKIP *)
  | ESkip :
      forall p g, 
        contains g p -> 
        (Skip, g) -[p | ε]->! g

  (* EXCEPTION *)
  | EThrowCtxt : 
      forall p g λ e h e' h',
        Some h = g [@ p] -> 
        (e,h) -e[p | λ]-> (e',h') ->
        (Throw e, g) -[p | λ]-> (Throw e',  g[p~~>Some h'])
  | EThrowCtxtTerm : 
      forall p g λ e h h',
        Some h = g [@ p] -> 
        (e,h) -e[p | λ]->! h' ->
        (Throw e, g) -[p | λ]->! g[p~~>Some h']
  | EThrow :
      forall p g v,
        contains g p ->
        (Throw (Val v), g) -[p | ⊗ (singleton v)]->! g

  (* DECLARE VAL *)
  | EBindCtxt : 
      forall p g λ e h e' h', 
        Some h = g[@ p] ->
        (e, h) -e[p | λ]-> (e',h') -> 
        forall x s,
          (Bind x e s, g) -[p|λ]-> (Bind x e' s, g[p~~>Some h'])
  | EBindCtxtTerm :
      forall p g λ e h h',
        Some h = g[@ p] ->
        (e, h) -e[p | λ]->! h' -> 
        forall x s,
          (Bind x e s, g) -[p|λ]->! g[p~~>Some h']
  | EBind :
      forall p g λ s v x s' g', 
        contains g p ->
        (s[v//x], g) -[p|λ]-> (s',g') -> 
        (Bind x (Val v) s, g) -[p|λ]-> (s',g')
  | EBindTerm : 
      forall p g λ s v x g', 
        contains g p ->
        (s[v//x], g) -[p|λ]->! g' -> 
        (Bind x (Val v) s, g) -[p|λ]->! g'

  (* FIELD UPDATE *)
  | EUpdateCtxt1 :
      forall p g λ e1 f e2 h e1' h', 
        Some h = g [@ p] -> 
        (e1,h) -e[p | λ]-> (e1',h') ->
        (Assign e1 f e2, g) -[p|λ]-> (Assign e1' f e2, g[p~~>Some h'])
  | EUpdateCtxt1Term :
      forall p g λ e1 f e2 h h', 
        Some h = g [@ p] -> 
        (e1,h) -e[p | λ]->! h' ->
        (Assign e1 f e2, g) -[p|λ]->! g[p~~>Some h']
  | EUpdateCtxt2 :
      forall p g λ o f e2 h e2' h', 
        Some h = g [@ p] -> 
        (e2,h) -e[p | λ]-> (e2',h') ->
        (Assign (Val o) f e2, g) -[p|λ]-> (Assign (Val o) f e2', g[p~~>Some h'])
  | EUpdateCtxt2Term :
      forall p g λ o f e2 h h', 
        Some h = g [@ p] -> 
        (e2,h) -e[p | λ]->! h' ->
        (Assign (Val o) f e2, g) -[p|λ]->! g[p~~>Some h']
  | EUpdate :
      forall p g oid f v h pf o, 
        Some h = g [@ p] ->
        h[@oid] = Some o ->
        contains o f ->
        (Assign (Val (Object oid)) f (Val v), g) -[p|ε]->! g[p~~>Some (update h oid pf (o[f~~>v]))]
  | EUpdateBad :
      forall p g v1 f v h,
        Some h = g [@ p] ->
        match v1 with
          | GlobalObject _ _ => True
          | Nat _ => True
          | Object oid => match h[@oid] with
                            | None => True
                            | Some obj => obj[@ f] = None
                          end 
        end ->
        (Assign (Val v1) f (Val v), g) -[p|⊗ (singleton FieldNotFoundException)]->! g

  (* SPAWN *)
  | EAsync :
      forall p g s, 
      contains g p ->         
     (Async s, g) -[p|ε]-> (DAsync s, g)

  (* ASYNC *)
  | EDAsync : 
      forall p g λ s s' g', 
        (s,g) -[p|λ]-> (s',g') ->
        (DAsync s, g) -[p|(toAsyncTrans λ)]-> (DAsync s', g')
  | EDAsyncTerm :
      forall p g λ s g', 
     (s,g) -[p|λ]->! g' ->
     (DAsync s, g) -[p|(toAsyncTrans λ)]->! g'

  (* FINISH *)
  | EFinish : forall p μ λ s g s' g', 
      (s,g) -[p|λ]-> (s',g') ->
    (Finish μ s,g) -[p|ε]-> (Finish (vals_plus_trans_type μ λ) s',g')

  (* END OF FINISH *)
  | EFinishTerm : forall p μ λ s g g',
      (s,g) -[p|λ]->! g' ->
    (Finish μ s,g) -[p|(asSyncTrans (vals_plus_trans_type μ λ))]->! g'

  (* SEQ *)
  | ESeq1 :
      forall p λ s g s' g',
        isSyncTrans λ = false -> 
        (s,g) -[p|λ]-> (s',g') ->
        forall t,
          (Seq s t,g) -[p|λ]-> (Seq s' t,g')
  | ESeq1Term : 
      forall p λ s g g',
        isSyncTrans λ = false -> 
        (s,g) -[p|λ]->! g' ->
        forall t,
          (Seq s t,g) -[p|λ]-> (t,g')
  | ESeq1Fail : 
      forall p s g ve sg',
        (s,g) -[p|⊗ ve]->? sg' ->
        forall t,
          (Seq s t,g) -[p|⊗ ve]->? sg'
  (* OUR OF ORDER SEQ *)
  | ESeq2 : 
      forall p λ s t g t' g', 
        isAsync s = true ->
        (t,g) -[p|λ]-> (t',g') ->
        (Seq s t,g) -[p|λ]-> (Seq s t',g')
  | ESeq2Term :
      forall p λ s t g g',
        isAsync s = true ->
        (t,g) -[p|λ]->! g' ->
        (Seq s t,g) -[p|λ]-> (s,g')

  (* AT CONTEXT *)
  | EAtCtxt :
      forall p g λ q x e s h e' h', 
        Some h = g [@ p] -> 
        (e,h) -e[p | λ]-> (e',h') ->
        (At q x e s, g) -[p|λ]-> (At q x e' s, g[p~~>Some h'])
  | EAtCtxtTerm :
      forall p g λ q x e s h h', 
        Some h = g [@ p] -> 
        (e,h) -e[p | λ]->! h' ->
        (At q x e s, g) -[p|λ]->! g[p~~>Some h']

  (* PLACE SHIFT *)
  | EAt : 
      forall q p x o s g qh ph o' ph',
     Some ph = g [@ p] ->
     Some qh = g [@ q] -> 
     Some (o', ph') = copy qh o ph ->
     (At p x (Val o) s,g) -[q|ε]-> (DAt p (Seq (s[o' // x]) Skip), g[p~~>Some ph'])
  
  (* At *)
  | EDAt : 
      forall p r λ s g rh ph s' g' λ' rh',
        (s,g) -[p|λ]-> (s',g') ->
        Some rh = g' [@ r] -> 
        Some ph = g' [@ p] ->
        (* copy any values in the label back to the parent's heap *)
        Some (λ',rh') = transCopy (p ==b r) ph λ rh ->
        (DAt p s,g) -[r|λ']-> (DAt p s',g'[r~~>Some rh'])
  | EDAtTerm : 
      forall p r λ s g rh ph g' λ' rh',
        (s,g) -[p|λ]->! g' ->
        Some rh = g' [@ r] -> 
        Some ph = g' [@ p] ->
        (* copy any values in the label back to the parent's heap *)
        Some (λ',rh') = transCopy (p ==b r) ph λ rh ->
        (DAt p s,g) -[r|λ']->! g'[r~~>Some rh']

  (* TRY *)
  | ECatch : 
      forall p g λ s t s' g', 
        contains g p ->
        isSyncTrans λ = false ->
     (s,g) -[p|λ]-> (s',g') ->
     (Catch s t, g) -[p|λ]-> (Catch s' t,g')
  | ECatchTerm : 
      forall p g λ s t g', 
        contains g p ->
        isSyncTrans λ = false ->
     (s,g) -[p|λ]->! g' ->
     (Catch s t, g) -[p|λ]->! g'
  | ECatchFail : 
      forall p g ve s t s' g', 
        contains g p ->
     (s,g) -[p|⊗ ve]-> (s',g') ->
     (Catch s t, g) -[p|ε]-> (Seq s' t,g')
  | ECatchFailTerm : 
      forall p g ve s t g', 
        contains g p ->
     (s,g) -[p|⊗ ve]->! g' ->
     (Catch s t, g) -[p|ε]-> (t,g')
where "A '-[' p | t ']->?' B" := (eval p t A B)
 and "A '-[' p | t ']->!' B" := (eval p t A (inr B))
 and "A '-[' p | t ']->' B" := (eval p t A (inl B)).

Notation "A '-[' p | t ']->?' B" := (eval p t A B).
Notation "A '-[' p | t ']->!' B" := (eval p t A (inr B)).
Notation "A '-[' p | t ']->' B" := (eval p t A (inl B)).

Inductive eval_config : place -> trans_type -> 
                 (stmt * global_heap) + global_heap -> (stmt*global_heap) + global_heap -> Prop := 
| EConfig : forall p λ sg sg',
   sg -[p|λ]->? sg' -> eval_config p λ (inl sg) sg'. 

Reserved Notation "A '-[' p | t ']->*' B" (at level 70).
Reserved Notation "A '-[' p | t ']->*?' B" (at level 70).
Reserved Notation "A '-[' p | t ']->*!' B" (at level 70).

(* we can also define the transitive closure of the evaluation relation,
  where all steps except for the last one must have an ε transition label *)
(* in fact, we define transitive closure a number of different ways.  Each make some proofs
   simpler *)

Inductive eval_star : place -> trans_type -> 
                 stmt * global_heap -> (stmt*global_heap) + global_heap -> Prop :=
  | eval_star_refl : forall p sg, 
                       sg -[ p | ε]->* sg
  | eval_star_step : forall {p sg λ sg' sg''}, 
                         sg -[ p | ε]->* sg'
                      -> sg' -[ p | λ]->? sg''
                      -> sg -[ p | λ]->*? sg''
  where "A '-[' p | t ']->*?' B" := (eval_star p t A B)
 and "A '-[' p | t ']->*!' B" := (eval_star p t A (inr B))
 and "A '-[' p | t ']->*' B" := (eval_star p t A (inl B)).

Notation "A '-[' p | t ']->*?' B" := (eval_star p t A B).
Notation "A '-[' p | t ']->*!' B" := (eval_star p t A (inr B)).
Notation "A '-[' p | t ']->*' B" := (eval_star p t A (inl B)).

Lemma eval_star_trans {p λ sg} sg' {sg''}:
    sg -[ p | ε]->* sg'
 -> sg' -[ p | λ]->*? sg''
 -> sg -[ p | λ]->*? sg''.
Proof.
  Hint Constructors eval_star.
  intros ev1 ev2; revert ev1.
  induction ev2; eauto.
Qed.

Lemma eval_eval_star {p λ sg sg'} :
    sg -[ p | λ]->? sg'
 -> sg -[ p | λ]->*? sg'.
Proof.
  eauto.
Qed.

Section eval_star_alt.


Inductive eval_star_both : place ->
                 stmt * global_heap ->
                 (stmt*global_heap) -> Prop :=
  | eval_star_both_refl : forall p sg, 
                       eval_star_both p sg sg
  | eval_star_both_step : forall p sg sg', 
                       sg -[p|ε]-> sg' -> 
                       eval_star_both p sg sg'
  | eval_star_both_trans : forall {p sg sg' sg''}, 
                         eval_star_both p sg sg' ->
                         eval_star_both p sg' sg'' ->
                         eval_star_both p sg sg''.

Lemma eval_star_eval_star_both {p sg sg'} : eval_star p ε sg (inl sg') -> eval_star_both p sg sg'.
Proof.
  Hint Constructors eval_star_both.
  intros ev; dependent induction ev; eauto.
Qed.

Lemma eval_star_both_eval_star {p sg sg'} : eval_star_both p sg sg' -> eval_star p ε sg (inl sg').
Proof.
  Hint Resolve eval_star_trans.
  Hint Constructors eval_star.
  intros ev; dependent induction ev; eauto.
Qed.

Inductive eval_star_left : place ->
                            stmt * global_heap ->
                            (stmt*global_heap) + global_heap -> Prop :=
  | eval_star_left_refl : forall p sg, 
                       eval_star_left p sg (inl sg)
  | eval_star_left_step : forall {p sg sg' sg''}, 
                         sg -[ p | ε]-> sg'
                      -> eval_star_left p sg' sg''
                      -> eval_star_left p sg sg''.

Lemma eval_star_left_trans p s1g1 s2g2 s3g3 : 
  eval_star_left p s1g1 (inl s2g2) ->
  eval_star_left p s2g2 s3g3 ->         
  eval_star_left p s1g1 s3g3.
Proof.
  Hint Constructors eval_star_left.
  intros ev.
  dependent induction ev; eauto.
Qed.

Lemma eval_star_left_eval_star_both {p sg sg'} : eval_star_left p sg (inl sg') -> eval_star_both p sg sg'.
Proof.
  Hint Constructors eval_star_both.
  intros ev; dependent induction ev; eauto.
Qed.

Lemma eval_star_both_eval_star_left {p sg sg'} : eval_star_both p sg sg' -> eval_star_left p sg (inl sg').
Proof.
  Hint Constructors eval_star_left.
  Hint Resolve eval_star_left_trans.
  intros ev; dependent induction ev; eauto.
Qed.

Lemma eval_star_eval_star_left {p sg sg'} : eval_star p ε sg (inl sg') -> eval_star_left p sg (inl sg').
Proof.
  Hint Resolve eval_star_both_eval_star_left eval_star_eval_star_both.
  eauto.
Qed.

Lemma eval_star_left_eval_star {p sg sg'} : eval_star_left p sg (inl sg') -> eval_star p ε sg (inl sg').
Proof.
  Hint Resolve eval_star_left_eval_star_both eval_star_both_eval_star.
  eauto.
Qed.
End eval_star_alt.

End semantics.

Hint Resolve eval_eval_star.

Notation "A '-[' p | t ']->?' B" := (eval p t A B)   (at level 70) : eval_relations.
Notation "A '-[' p | t ']->!' B" := (eval p t A (inr B)) (at level 70) : eval_relations.
Notation "A '-[' p | t ']->' B" := (eval p t A (inl B))  (at level 70) : eval_relations.

Notation "A '-[' p | t ']->*?' B" := (eval_star p t A B) (at level 70) : eval_relations.
Notation "A '-[' p | t ']->*!' B" := (eval_star p t A (inr B)) (at level 70) : eval_relations.
Notation "A '-[' p | t ']->*' B" := (eval_star p t A (inl B)) (at level 70) : eval_relations.

Open Scope eval_relations.
