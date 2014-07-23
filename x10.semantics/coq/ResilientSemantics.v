(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Encodes the semantics of statements in Resilient X10 *)
Require Export ExprSemantics.

Require Import Coq.Vectors.Vector.
Require Import Coq.Classes.EquivDec.
Require Import Program.

Section res_semantics.
Context `{sc:StaticConfig}.
Context {Heap:@HEAP oid oid_eqdec obj}.

Reserved Notation "A '-r[' p | t ']->' B" (at level 70).
Reserved Notation "A '-r[' p | t ']->?' B" (at level 70).
Reserved Notation "A '-r[' p | t ']->!' B" (at level 70).

Definition MaskedException : val := Nat 4.

Definition toDP (vs:list val):list val :=
  match vs with 
      | List.nil => List.nil
      | _::_ => (singleton DeadPlaceException)
  end.

Definition mask_trans (v:val) (λ:trans_type) : trans_type
  := match λ with
    | ε => ε
    | SyncFail _ => SyncFail (singleton v)
    | AsyncFail _ => AsyncFail (singleton v)
  end.


Inductive eval_r : place -> trans_type -> 
                 stmt * global_heap -> (stmt*global_heap) + global_heap -> Prop :=

  (* SKIP *)
  | ERSkip :
      forall p g, 
        contains g p -> 
        (Skip, g) -r[p | ε]->! g

  | ERSkipPFail :
      forall p g,
        ~ contains g p ->
     (Skip, g) -r[p|⊗ (singleton DeadPlaceException)]->! g


  (* EXCEPTION *)
  | ERThrowCtxt : 
      forall p g λ e h e' h',
        Some h = g [@ p] -> 
        (e,h) -e[p | λ]-> (e',h') ->
        (Throw e, g) -r[p | λ]-> (Throw e',  g[p~~>Some h'])
  | ERThrowCtxtTerm : 
      forall p g λ e h h',
        Some h = g [@ p] -> 
        (e,h) -e[p | λ]->! h' ->
        (Throw e, g) -r[p | λ]->! g[p~~>Some h']
  | ERThrow :
      forall p g v,
        contains g p ->
        (Throw (Val v), g) -r[p | ⊗ (singleton v)]->! g

  | ERThrowPFail :
      forall p g v,
        ~ contains g p ->
     (Throw v, g) -r[p|⊗ (singleton DeadPlaceException)]->! g

  (* DECLARE VAL *)
  | ERBindCtxt : 
      forall p g λ e h e' h', 
        Some h = g[@ p] ->
        (e, h) -e[p | λ]-> (e',h') -> 
        forall x s,
          (Bind x e s, g) -r[p|λ]-> (Bind x e' s, g[p~~>Some h'])
  | ERBindCtxtTerm :
      forall p g λ e h h',
        Some h = g[@ p] ->
        (e, h) -e[p | λ]->! h' -> 
        forall x s,
          (Bind x e s, g) -r[p|λ]->! g[p~~>Some h']
  | ERBind :
      forall p g λ s v x s' g', 
        contains g p ->
        (s[v//x], g) -r[p|λ]-> (s',g') -> 
        (Bind x (Val v) s, g) -r[p|λ]-> (s',g')
  | ERBindTerm : 
      forall p g λ s v x g', 
        contains g p ->
        (s[v//x], g) -r[p|λ]->! g' -> 
        (Bind x (Val v) s, g) -r[p|λ]->! g'

  | ERBindPFail :
      forall p g x e s,
        ~ contains g p ->
     (Bind x e s, g) -r[p|⊗ (singleton DeadPlaceException)]->! g

  (* FIELD UPDATE *)
  | ERUpdateCtxt1 :
      forall p g λ e1 f e2 h e1' h', 
        Some h = g [@ p] -> 
        (e1,h) -e[p | λ]-> (e1',h') ->
        (Assign e1 f e2, g) -r[p|λ]-> (Assign e1' f e2, g[p~~>Some h'])
  | ERUpdateCtxt1Term :
      forall p g λ e1 f e2 h h', 
        Some h = g [@ p] -> 
        (e1,h) -e[p | λ]->! h' ->
        (Assign e1 f e2, g) -r[p|λ]->! g[p~~>Some h']
  | ERUpdateCtxt2 :
      forall p g λ o f e2 h e2' h', 
        Some h = g [@ p] -> 
        (e2,h) -e[p | λ]-> (e2',h') ->
        (Assign (Val o) f e2, g) -r[p|λ]-> (Assign (Val o) f e2', g[p~~>Some h'])
  | ERUpdateCtxt2Term :
      forall p g λ o f e2 h h', 
        Some h = g [@ p] -> 
        (e2,h) -e[p | λ]->! h' ->
        (Assign (Val o) f e2, g) -r[p|λ]->! g[p~~>Some h']
  | ERUpdate :
      forall p g oid f v h pf o, 
        Some h = g [@ p] ->
        h[@oid] = Some o ->
        contains o f ->
        (Assign (Val (Object oid)) f (Val v), g) -r[p|ε]->! g[p~~>Some (update h oid pf (o[f~~>v]))]
  | ERUpdateBad :
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
        (Assign (Val v1) f (Val v), g) -r[p|⊗ (singleton FieldNotFoundException)]->! g

  | ERUpdatePFail :
      forall p g e1 f e2,
        ~ contains g p ->
     (Assign e1 f e2, g) -r[p|⊗ (singleton DeadPlaceException)]->! g

  (* PLACE FAILURE *)
  | ERPlaceFailure :
      forall p g s,
        contains g p ->
        (s, g) -r[p|ε]-> (s,g[p~~>None])

  (* SPAWN *)
  | ERAsync :
      forall p g s, 
      contains g p ->         
     (Async s, g) -r[p|ε]-> (DAsync s, g)

  | ERAsyncPFail :
      forall p g s,
        ~ contains g p ->
     (Async s, g) -r[p|⊗ (singleton DeadPlaceException)]->! g
       
  (* ASYNC *)
  | ERDAsync : 
      forall p g λ s s' g', 
        (s,g) -r[p|λ]-> (s',g') ->
        (DAsync s, g) -r[p|(toAsyncTrans λ)]-> (DAsync s', g')
  | ERDAsyncTerm :
      forall p g λ s g', 
     (s,g) -r[p|λ]->! g' ->
     (DAsync s, g) -r[p|(toAsyncTrans λ)]->! g'

   (* FINISH *)
  | ERFinish : 
      forall p μ λ s g s' g', 
        (s,g) -r[p|λ]-> (s',g') ->
        (Finish μ s,g) -r[p|ε]-> (Finish (vals_plus_trans_type μ λ) s',g')

  (* END OF FINISH *)
  | ERFinishTerm : 
      forall p μ λ s g g',
        contains g p ->
        (s,g) -r[p|λ]->! g' ->
        (Finish μ s,g) -r[p|(asSyncTrans (vals_plus_trans_type μ λ))]->! g'

  | ERFinishTermPFail : 
      forall p μ λ s g g',
        ~ contains g p ->
        (s,g) -r[p|λ]->! g' ->
        (Finish μ s,g) -r[p|(asSyncTrans (toDP (vals_plus_trans_type μ λ)))]->! g'

  (* SEQ *)
  | ESeq1 :
      forall p λ s g s' g',
        isSyncTrans λ = false -> 
        (s,g) -r[p|λ]-> (s',g') ->
        forall t,
          (Seq s t,g) -r[p|λ]-> (Seq s' t,g')
  | ESeq1Fail : 
      forall p s g ve s' g',
        (s,g) -r[p|⊗ ve]-> (s', g') ->
        forall t,
          (Seq s t,g) -r[p|⊗ ve]-> (s',g')

  (* PAR *)
  | ESeq2 : 
      forall p λ s t g t' g', 
        isAsync s = true ->
        (t,g) -r[p|λ]-> (t',g') ->
        (Seq s t,g) -r[p|λ]-> (Seq s t',g')
  | ESeq2Term :
      forall p λ s t g g',
        isAsync s = true ->
        (t,g) -r[p|λ]->! g' ->
        (Seq s t,g) -r[p|λ]-> (s,g')

  (* SEQ TERM *)
  | ESeq1Term : 
      forall p λ s g g',
        contains  g p ->
        isSyncTrans λ = false -> 
        (s,g) -r[p|λ]->! g' ->
        forall t,
          (Seq s t,g) -r[p|λ]-> (t,g')

  | ESeq1TermFail : 
      forall p s g ve g',
        contains  g p ->
        (s,g) -r[p|⊗ ve]->! g' ->
        forall t,
          (Seq s t,g) -r[p|⊗ ve]->! g'

  (* SEQ FAILED TERM *)
  | ESeq1TermPFailSync : 
      forall p λ s g g',
        ~ contains g p ->
        isSync s = true ->
        (s,g) -r[p|λ]->! g' ->
        forall t,
          (Seq s t,g) -r[p|⊗ (singleton DeadPlaceException)]->! g'

  | ESeq1TermPFailASync : 
      forall p λ s g g',
        ~ contains g p ->
        isAsync s = true ->
        (s,g) -r[p|λ]->! g' ->
        forall t,
          (Seq s t,g) -r[p|× (singleton DeadPlaceException)]-> (t,g')

  (* AT CONTEXT *)
  | ERAtCtxt :
      forall p g λ q x e s h e' h', 
        Some h = g [@ p] -> 
        (e,h) -e[p | λ]-> (e',h') ->
        (At q x e s, g) -r[p|λ]-> (At q x e' s, g[p~~>Some h'])
  | ERAtCtxtTerm :
      forall p g λ q x e s h h', 
        Some h = g [@ p] -> 
        (e,h) -e[p | λ]->! h' ->
        (At q x e s, g) -r[p|λ]->! g[p~~>Some h']

  (* PLACE SHIFT *)
  | EAt : 
      forall q p x o s g qh ph o' ph',
     Some ph = g [@ p] ->
     Some qh = g [@ q] -> 
     Some (o', ph') = copy qh o ph ->
     (At p x (Val o) s,g) -r[q|ε]-> (DAt p (Seq (s[o' // x]) Skip), g[p~~>Some ph'])

  | EAtPFailThere : 
      forall q p x v s g,
        ~ contains g p ->
     (At p x (Val v) s,g) -r[q|⊗ (singleton DeadPlaceException)]->! g

  | EAtPFailHere : 
      forall q p x e s g,
        ~ contains g q ->
     (At p x e s,g) -r[q|⊗ (singleton DeadPlaceException)]->! g

 (* At *)
  | EDAt : 
      forall p r λ s g rh ph s' g' λ' rh',
        (s,g) -r[p|λ]-> (s',g') ->
        Some rh = g' [@ r] -> 
        Some ph = g' [@ p] ->
        (* copy any values in the label back to the parent's heap *)
        Some (λ',rh') = transCopy (p ==b r) ph λ rh ->
        (DAt p s,g) -r[r|λ']-> (DAt p s',g'[r~~>Some rh'])
  | EDAtTerm : 
      forall p r λ s g rh ph g' λ' rh',
        (s,g) -r[p|λ]->! g' ->
        Some rh = g' [@ r] -> 
        Some ph = g' [@ p] ->
        (* copy any values in the label back to the parent's heap *)
        Some (λ',rh') = transCopy (p ==b r) ph λ rh ->
        (DAt p s,g) -r[r|λ']->! g'[r~~>Some rh']

  | EDAtPFailHere : 
      forall p r λ s g s' g',
        ~ contains g r ->
        (s,g) -r[p|λ]-> (s',g') ->
        (DAt p s,g) -r[r|(mask_trans DeadPlaceException λ)]-> (DAt p s',g')
  | EDAtTermPFailHere : 
      forall p r λ s g g',
        ~ contains g r ->
        (s,g) -r[p|λ]->! g' ->
        (DAt p s,g) -r[r|(mask_trans DeadPlaceException λ)]->! g'

  | EDAtPFailThere : 
      forall p r λ s g s' g',
        contains g r ->
        ~ contains g p ->
        (s,g) -r[p|λ]-> (s',g') ->
        (DAt p s,g) -r[r|(mask_trans MaskedException λ)]-> (DAt p s',g')
  | EDAtTermPFailThere : 
      forall p r λ s g g',
        contains g r ->
        ~ contains g p ->
        (s,g) -r[p|λ]->! g' ->
        (DAt p s,g) -r[r|(mask_trans MaskedException λ)]->! g'

 (* TRY *)
  | ECatch : 
      forall p g λ s t s' g', 
        isSyncTrans λ = false ->
        (s,g) -r[p|λ]-> (s',g') ->
        (Catch s t, g) -r[p|λ]-> (Catch s' t,g')
  | ECatchTerm : 
      forall p g λ s t g', 
        isSyncTrans λ = false ->
        (s,g) -r[p|λ]->! g' ->
        (Catch s t, g) -r[p|λ]->! g'

  | ECatchFail : 
      forall p g ve s t s' g', 
        contains g p ->
        (s,g) -r[p|⊗ ve]-> (s',g') ->
        (Catch s t, g) -r[p|ε]-> (Seq s' t,g')
  | ECatchFailTerm : 
      forall p g ve s t g', 
        contains g p ->
        (s,g) -r[p|⊗ ve]->! g' ->
        (Catch s t, g) -r[p|ε]-> (t,g')

  | ECatchFailPFail : 
      forall p g s t s' g', 
        ~ contains g p ->
        (s,g) -r[p|⊗ (singleton DeadPlaceException)]-> (s',g') ->
        (Catch s t, g) -r[p|⊗ (singleton DeadPlaceException)]-> (s',g')
  | ECatchFailTermPFail : 
      forall p g s t g', 
        ~ contains g p ->
        (s,g) -r[p|⊗ (singleton DeadPlaceException)]->! g' ->
        (Catch s t, g) -r[p|⊗ (singleton DeadPlaceException)]->! g'


where "A '-r[' p | t ']->?' B" := (eval_r p t A B)
  and "A '-r[' p | t ']->!' B" := (eval_r p t A (inr B))
  and "A '-r[' p | t ']->' B" := (eval_r p t A (inl B)).



Reserved Notation "A '-r[' p | t ']->*' B" (at level 70).
Reserved Notation "A '-r[' p | t ']->*?' B" (at level 70).
Reserved Notation "A '-r[' p | t ']->*!' B" (at level 70).

(* we can also define the transitive closure of the evaluation relation,
  where all steps except for the last one must have an ε transition label *)
(* in fact, we define transitive closure a number of different ways.  Each make some proofs
   simpler *)

Inductive eval_r_star : place -> trans_type -> 
                 stmt * global_heap -> (stmt*global_heap) + global_heap -> Prop :=
  | eval_r_star_refl : forall p sg, 
                       sg -r[ p | ε]->* sg
  | eval_r_star_step : forall {p sg λ sg' sg''}, 
                         sg -r[ p | ε]->* sg'
                      -> sg' -r[ p | λ]->? sg''
                      -> sg -r[ p | λ]->*? sg''
  where "A '-r[' p | t ']->*?' B" := (eval_r_star p t A B)
 and "A '-r[' p | t ']->*!' B" := (eval_r_star p t A (inr B))
 and "A '-r[' p | t ']->*' B" := (eval_r_star p t A (inl B)).

Notation "A '-r[' p | t ']->*?' B" := (eval_r_star p t A B).
Notation "A '-r[' p | t ']->*!' B" := (eval_r_star p t A (inr B)).
Notation "A '-r[' p | t ']->*' B" := (eval_r_star p t A (inl B)).

Lemma eval_r_star_trans {p λ sg} sg' {sg''}:
    sg -r[ p | ε]->* sg'
 -> sg' -r[ p | λ]->*? sg''
 -> sg -r[ p | λ]->*? sg''.
Proof.
  Hint Constructors eval_r_star.
  intros ev1 ev2; revert ev1.
  induction ev2; eauto.
Qed.

Lemma eval_r_eval_r_star {p λ sg sg'} :
    sg -r[ p | λ]->? sg'
 -> sg -r[ p | λ]->*? sg'.
Proof.
  eauto.
Qed.

Section eval_r_star_alt.


Inductive eval_r_star_both : place ->
                 stmt * global_heap ->
                 (stmt*global_heap) -> Prop :=
  | eval_r_star_both_refl : forall p sg, 
                       eval_r_star_both p sg sg
  | eval_r_star_both_step : forall p sg sg', 
                       sg -r[p|ε]-> sg' -> 
                       eval_r_star_both p sg sg'
  | eval_r_star_both_trans : forall {p sg sg' sg''}, 
                         eval_r_star_both p sg sg' ->
                         eval_r_star_both p sg' sg'' ->
                         eval_r_star_both p sg sg''.

Lemma eval_r_star_eval_r_star_both {p sg sg'} : eval_r_star p ε sg (inl sg') -> eval_r_star_both p sg sg'.
Proof.
  Hint Constructors eval_r_star_both.
  intros ev; dependent induction ev; eauto.
Qed.

Lemma eval_r_star_both_eval_r_star {p sg sg'} : eval_r_star_both p sg sg' -> eval_r_star p ε sg (inl sg').
Proof.
  Hint Resolve eval_r_star_trans.
  Hint Constructors eval_r_star.
  intros ev; dependent induction ev; eauto.
Qed.

Inductive eval_r_star_left : place ->
                            stmt * global_heap ->
                            (stmt*global_heap) + global_heap -> Prop :=
  | eval_r_star_left_refl : forall p sg, 
                       eval_r_star_left p sg (inl sg)
  | eval_r_star_left_step : forall {p sg sg' sg''}, 
                         sg -r[ p | ε]-> sg'
                      -> eval_r_star_left p sg' sg''
                      -> eval_r_star_left p sg sg''.

Lemma eval_r_star_left_trans p s1g1 s2g2 s3g3 : 
  eval_r_star_left p s1g1 (inl s2g2) ->
  eval_r_star_left p s2g2 s3g3 ->         
  eval_r_star_left p s1g1 s3g3.
Proof.
  Hint Constructors eval_r_star_left.
  intros ev.
  dependent induction ev; eauto.
Qed.

Lemma eval_r_star_left_eval_r_star_both {p sg sg'} : eval_r_star_left p sg (inl sg') -> eval_r_star_both p sg sg'.
Proof.
  Hint Constructors eval_r_star_both.
  intros ev; dependent induction ev; eauto.
Qed.

Lemma eval_r_star_both_eval_r_star_left {p sg sg'} : eval_r_star_both p sg sg' -> eval_r_star_left p sg (inl sg').
Proof.
  Hint Constructors eval_r_star_left.
  Hint Resolve eval_r_star_left_trans.
  intros ev; dependent induction ev; eauto.
Qed.

Lemma eval_r_star_eval_r_star_left {p sg sg'} : eval_r_star p ε sg (inl sg') -> eval_r_star_left p sg (inl sg').
Proof.
  Hint Resolve eval_r_star_both_eval_r_star_left eval_r_star_eval_r_star_both.
  eauto.
Qed.

Lemma eval_r_star_left_eval_r_star {p sg sg'} : eval_r_star_left p sg (inl sg') -> eval_r_star p ε sg (inl sg').
Proof.
  Hint Resolve eval_r_star_left_eval_r_star_both eval_r_star_both_eval_r_star.
  eauto.
Qed.
End eval_r_star_alt.

End res_semantics.

Notation "A '-r[' p | t ']->?' B" := (eval_r p t A B)   (at level 70) : eval_relations.
Notation "A '-r[' p | t ']->!' B" := (eval_r p t A (inr B)) (at level 70) : eval_relations.
Notation "A '-r[' p | t ']->' B" := (eval_r p t A (inl B))  (at level 70) : eval_relations.

Notation "A '-r[' p | t ']->*?' B" := (eval_r_star p t A B)   (at level 70) : eval_relations.
Notation "A '-r[' p | t ']->*!' B" := (eval_r_star p t A (inr B)) (at level 70) : eval_relations.
Notation "A '-r[' p | t ']->*' B" := (eval_r_star p t A (inl B))  (at level 70) : eval_relations.

Hint Resolve eval_r_eval_r_star.

