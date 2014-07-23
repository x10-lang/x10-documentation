(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Properties of functional association lists needed by parts of the development. 
   An assocation list is a list of pairs, generally with decidable equality on the first part of the pair (the key) *)
Require Export ListUtil.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Sorting.Sorted.
Section Assoc.

Context {A B:Type}.
Let assoc := list (A*B).
Context {dec:EqDec A equiv}.

(* define lookup for assocation lists *)
Global Instance lookup_assoc : Lookup assoc A (option B) :=
  {lookup := fix lookupo o f
  := match o with 
       | nil => None
       | (f',v')::os => if f == f' then Some v' else lookupo os f
     end}.

(* define update/replace for assocation lists *)
Global Instance update_assoc : Update assoc A B :=
  {update := fix updateo o f v
    := match o with 
       | nil => nil
       | (f',v')::os => if f == f' then (f',v)::os else (f',v')::(updateo os f v)
     end}.

(* defines compaction for assocation lists.  This "compacts" the association list,
   removing entries that have the same key as another one *)
(* if there are repeated keys, this keeps the entry associated with the last one *)
Fixpoint obj_compact (l:assoc) : assoc :=
  match l with 
    | nil => nil
    | (f,v)::ls => match ls [@ f] with
                  | None => (f,v)::obj_compact ls
                  | Some _ => obj_compact ls
                end
    end.

(* the keys of an association list *)
Definition domain (l:assoc) := map fst l.

Definition swap (ab:A*B) := (snd ab, fst ab).

(* swap the domain and codomain of an association list *)
Definition mswap (l:assoc) := map swap l.

Ltac t := repeat progress (try (unfold lookup, update, domain in *; intros; try match goal with
    [ H: prod _ _ |- _ ] => destruct H
    | [H:context [(@equiv_dec ?A ?B ?C ?D ?X ?Y)] |- _] => destruct (@equiv_dec A B C D X Y); unfold equiv, complement in *; try subst
    | [|- context [(@equiv_dec ?A ?B ?C ?D ?X ?Y)]] => destruct (@equiv_dec A B C D X Y);  unfold equiv, complement in *; try subst
    | [|- _ :: _ = _ :: _] => f_equal
  end; intros; try simpl in *; try subst; trivial; try discriminate; try intuition)).

Lemma lookup_cons_eq : forall (l:assoc) a b, ((a,b)::l)[@a] = Some b.
Proof.
  t.
Qed.

Hint Resolve lookup_cons_eq.

Lemma lookup_cons_neq : forall (l:assoc) a b c, a <> c -> ((a,b)::l)[@c] = l[@c].
Proof.
  t.
Qed.

Lemma lookup_none_nin :  forall (l:assoc) (a:A), l [@ a] = None -> ~ In a (domain l).
Proof.
  induction l; t; eauto.
Qed.

Lemma update_domain : forall (l:assoc) (a:A) (v:B), domain (l [a~~>v]) = domain l.
Proof.
  induction l; t.
Qed.

Lemma lookup_update1 : forall l a v v', l[@a] = Some v' ->
  (l[a~~>v])[@a] = Some v.
Proof.
  induction l; simpl; intros. 
    discriminate.
    t; eauto.
Qed.

Lemma lookup_update2 : forall l a1 a2 v, a1 <> a2 -> (l[a1~~>v])[@a2] = l[@a2].
Proof.
  induction l; simpl; trivial. 
  t; eauto.
Qed.

Lemma mswap_in : forall l a b, In (a,b) l <-> In (b,a) (mswap l).
Proof.
  induction l; simpl in *; trivial; intros.
    intuition.
  destruct a; simpl. 
  intuition; try inversion H0; intuition.
  right; apply IHl; auto.
  right; apply IHl; auto.  
Qed.

Lemma in_dom : forall {l:assoc} {a b}, In (a,b) l -> In a (domain l).
Proof.
  unfold domain; induction l; simpl; trivial.
  intros. destruct a; simpl in *; intuition.
  inversion H0; intuition.
  eauto.
Qed.

Lemma in_domain_in : forall {l:assoc} {a}, In a (domain l) -> exists b, In (a,b) l.
Proof.
  induction l; simpl. intuition.
  intuition.
    simpl in *. subst; econstructor. intuition.
    
    destruct (IHl _ H0); eauto.
Qed.

Lemma nodup_in_eq : forall {l:assoc} {a b c}, NoDup (domain l) -> In (a,b) l -> In (a,c) l -> b = c.
Proof.
  induction l; simpl; intros; inversion H.
    intuition.
    t;
    try inversion H0; try inversion H2.
      rewrite <- H8, H6; trivial.
      subst. elim H4. eapply in_dom; eauto.

      subst. elim H4. eapply in_dom; eauto.
      eauto.
Qed.


Lemma lookup_in : forall {l:assoc} {a:A} {b:B}, l[@a] = Some b -> In (a,b) l.
Proof.
  induction l; t. inversion H; subst; intuition.
Qed.

Lemma in_dom_lookup :  forall {l:assoc} {a:A}, In a (domain l) -> exists v, l[@a] = Some v.
Proof.
  induction l; t; eauto. 
Qed.

Lemma in_lookup :  forall {l:assoc} {a:A} {b0:B}, In (a,b0) l -> exists v, l[@a] = Some v.
Proof.
  Hint Resolve in_dom_lookup in_dom.
  intros. eauto.
Qed.

Lemma in_lookup_nodup : forall {l:assoc} {a:A} {b:B}, NoDup (domain l) -> In (a,b) l -> l[@a] = Some b.
Proof.
  intros.
  destruct (in_lookup H0).
  generalize (lookup_in H1); intros.
  generalize (nodup_in_eq H H0 H2); congruence.
Qed.

Lemma domain_app : forall (a b:assoc), domain(a++b) = domain a ++ domain b.
Proof.
  intros; apply map_app.
Qed.

Lemma mswap_app : forall (a b:assoc), mswap(a++b) = mswap a ++ mswap b.
Proof.
  intros; apply map_app.
Qed.


Global Instance mswap_perm : Proper (@Permutation (A*B) ==> @Permutation (B*A)) mswap.
  repeat red; intros.
  apply Permutation_map; auto.
Qed.

Global Instance dom_perm : Proper (@Permutation (A*B) ==> @Permutation A) domain.
  repeat red; intros.
  apply Permutation_map; auto.
Qed.

Lemma obj_compact_dom {l:assoc} {a}:
  In a (domain (obj_compact l)) <-> In a (domain l).
Proof.
  revert a.
  induction l; simpl in *; intuition; simpl.
  - destruct (l[@a0]); simpl in *; intuition;
    right; apply IHl; auto.
  - simpl in *; subst.
    case_eq (l[@a]); intros.
    + apply IHl. eapply in_dom. eapply lookup_in; eauto.
    + simpl; intuition.
  - case_eq (l[@a0]); intros.
    + apply IHl; auto. 
    + simpl. right. eapply IHl; auto.
Qed.

Lemma obj_compact_in {l:assoc} {e v} e0 :
          In (e,v) (obj_compact l) ->
          obj_compact ((e, e0) :: l) = obj_compact l.
Proof.
  revert e v e0.
  induction l; simpl; intuition.
  destruct (e == a0); unfold equiv, complement in *; subst.
  - rewrite lookup_cons_eq; trivial.
  - rewrite lookup_cons_neq; auto.
    assert (In (e,v) (obj_compact l)).
    destruct (l[@a0]); simpl in *; intuition.
      elim c. inversion H0; trivial.
    apply in_dom in H0.
    rewrite obj_compact_dom in H0.
    destruct (in_dom_lookup H0).
    rewrite H1; trivial.
Qed.

Section Ord.

Context {gt:A->A->Prop}.
Context (gt_dec : forall (a1 a2:A), {gt a1 a2} + {~ gt a1 a2}).
Context {gt_order : StrictOrder gt}.

  Definition sorted_nd_domain (l:assoc) := sorted_nd gt_dec (domain l).

  Ltac tac :=
  repeat progress (match goal with 
    | [H: ?a = S ?a |- _ ] => elim (n_Sn _ H)
    | [H: S ?a = ?a |- _ ] => elim (n_Sn _ (symmetry H))
    | [H:?X = ?X |- _ ] => try clear H
    | [H: gt ?X ?X |- _] => elim (irreflexivity H)
    | [H: exists _, _ |- _ ] => destruct H
    | [H: context [gt_dec ?a ?n] |-_ ] => destruct (gt_dec a n); subst; try congruence
    | [|- context [gt_dec ?a ?n]] => destruct (gt_dec a n); subst; try congruence

    | [H: prod _ _ |- _] => destruct H
    | [H: ?X _ = ?X _  |- _] => inversion_clear H
    | [H: _ /\ _ |- _] => destruct H
    | [H:context [(@equiv_dec ?A ?B ?C ?D ?X ?Y)] |- _] => let Heq := (fresh "Heq") in 
      destruct (@equiv_dec A B C D X Y) as [Heq|Heq]; unfold equiv, complement in *; [try rewrite Heq in *|]; try subst; try congruence
    | [|- context [(@equiv_dec ?A ?B ?C ?D ?X ?Y)]] =>  let Heq := (fresh "Heq") in 
      destruct (@equiv_dec A B C D X Y) as [Heq|Heq]; unfold equiv, complement in *; [try rewrite Heq in *|]; try subst; try congruence
    end; intros; simpl in *; trivial).

Lemma Forall_gt_nodup : forall {l n}, Forall (gt n) (domain l) -> l [@n] = None.
Proof.
  unfold lookup; induction l; intuition; simpl in *.
  inversion H; subst; tac; auto.
Qed.

Lemma Forall_lookup {l} n1 n2 {v} : Forall (gt n1) (domain l) ->  l[@n2] = Some v -> gt n1 n2.
Proof.
  unfold lookup; induction l; simpl in *; intuition.
    discriminate.
    inversion H.
    subst.
    destruct a; simpl in *.
    match goal with 
      | [H:context [(@equiv_dec ?A ?B ?C ?D ?X ?Y)] |- _] => let Heq := (fresh "Heq") in 
        destruct (@equiv_dec A B C D X Y) as [Heq|Heq]; unfold equiv, complement in *; [rewrite Heq in *|]
    end;
    subst; auto.
Qed.

(* if two association lists are sorted by key (with a strict order, so no duplicate keys), and
   they map the same key to the same value (for all keys), then they are the same list *)
Lemma extensionality_Sorted : forall l l', StronglySorted gt (domain l) -> StronglySorted gt (domain l') -> (forall a, l[@a] = l'[@a]) -> l = l'.
Proof.
  unfold lookup; induction l; destruct l'; simpl; intros; trivial; tac.
  generalize (H1 a); tac. 
  generalize (H1 a); tac; congruence.

  apply StronglySorted_inv in H; apply StronglySorted_inv in H0; tac.

  generalize (H1 a0); generalize (H1 a); tac.
  f_equal. apply IHl; auto.
  intros. generalize (H1 a0); intros. tac.
  repeat rewrite Forall_gt_nodup; auto.

  elim (@irreflexivity _ _ _ a0).
  transitivity a; eapply Forall_lookup; eauto.
Qed.    

Lemma extensionality_ : forall l l' , sorted_nd_domain l = true -> sorted_nd_domain l' = true -> (forall a, l[@a] = l'[@a]) -> l = l'.
Proof.
  Hint Resolve extensionality_Sorted.
  unfold sorted_nd_domain; intros.
  apply sorted_StronglySorted in H; auto.
  apply sorted_StronglySorted in H0; auto.
Qed.

End Ord.

Section lookup_incl.

(* association list inclusion, defined via the lookup operator.
  Unlike incl (the standard list inclusion, defined via In),
  this allows l1 to have elements not in l2,
  as long as they are not "found" by lookup
  (i.e., they their key is also found in an earlier entry. 
   Of course, if we now that one of the lists does not have duplicate keys, then
   we can prove that the definitions are related. *)
Definition lincl (l1 l2:assoc) := forall a b, l1[@a]=Some b -> l2[@a]=Some b.

Global Instance lincl_pre : PreOrder lincl.
Proof.
  split; red; unfold lincl; eauto.
Qed.

Lemma lincl_incl : forall {l1 l2}, NoDup (domain l1) -> lincl l1 l2 -> incl l1 l2.
Proof.
  unfold lincl, incl; intros.
  destruct a.
  Hint Resolve in_lookup_nodup lookup_in.
  auto.
Qed.

Lemma incl_lincl : forall {l1 l2}, NoDup (domain l2) -> incl l1 l2 -> lincl l1 l2.
Proof.
  unfold lincl, incl; intros.
  Hint Resolve in_lookup_nodup lookup_in.
  auto.
Qed.

Lemma lincl_perm : forall {l1 l2}, NoDup (domain l1) -> Permutation l1 l2 -> lincl l1 l2. 
Proof.
  intros. apply incl_lincl.
  - rewrite <- (dom_perm _ _ H0); trivial.
  - intro; apply Permutation_in; trivial.
Qed.

Lemma lookup_app_none : forall l1 l2 a, (l1 ++ l2)[@a] = None <-> l1[@a]=None /\ l2[@a]=None.
Proof.
  induction l1; simpl; t.
  apply IHl1 in H; intuition.
  apply IHl1 in H; intuition.
  apply IHl1; intuition.
Qed.  

Lemma lookup_app_some : forall l1 l2 a b, (l1 ++ l2)[@a]=Some b <-> l1[@a]=Some b \/ (l1[@a]=None /\ l2[@a]=Some b).
Proof.  
  induction l1; simpl; t.
  apply IHl1 in H; intuition.
  apply IHl1; intuition.
  apply IHl1; intuition.
Qed.

Lemma lincl_appr: forall l1 l2, lincl l1 (l1++l2).
Proof.
  unfold lincl; intros.
  apply lookup_app_some; intuition.
Qed.

Lemma lincl_appl : forall l1 {l2}, disjoint (domain l1) (domain l2) -> lincl l2 (l1++l2).
Proof.
  unfold disjoint, lincl.
  intros.
  apply lookup_app_some.
  generalize (in_dom (lookup_in H0)).
  generalize (@lookup_in l1 a).
  unfold lookup; intros.
  destruct (lookup_assoc l1 a); eauto.
  eelim H; eauto.
Qed.

Lemma lincl_cons : forall a l, ~ In (fst a) (domain l) -> lincl l (a::l).
Proof.
  red; intros.
  t.
  apply lookup_in in H0.
  apply in_dom in H0.
  elim H; auto.
Qed.

Lemma nodup_domain_weaken : forall {l}, NoDup (domain l) -> NoDup l.
Proof.
  Hint Constructors NoDup.
  induction l; simpl; intuition.
  inversion H; subst.
  constructor; auto.
  intro; elim H2.
  destruct a; simpl.
  eapply in_dom; eauto.
Qed.
  
Lemma lincl_asym : forall {l1 l2}, NoDup (domain l1) -> NoDup (domain l2) -> lincl l1 l2 -> lincl l2 l1 -> Permutation l1 l2.
Proof.
  Hint Resolve nodup_domain_weaken.
  intros.
  apply NoDup_Permutation; intuition.
Qed.

End lookup_incl.

End Assoc.

Lemma swap_swap : forall {A B:Type} (ab:(A*B)), swap (swap ab) = ab.
Proof.
  unfold swap; simpl; destruct ab; trivial.
Qed.

Lemma mswap_mswap : forall {A B:Type} (l:list (A*B)), (mswap (mswap l)) = l.
Proof.
  unfold mswap.
  induction l; simpl in *; auto.
  rewrite swap_swap. congruence.
Qed.

Hint Rewrite @mswap_mswap : rewrites.
Hint Rewrite @domain_app @mswap_app : rewrites.

Section det.

Lemma swap_lookup_nodup' {A B:Type} {decA:EqDec A equiv} {decB:EqDec B equiv} : forall {l:list (A*B)} {a:A} {b:B}, NoDup (domain l) -> (mswap l)[@b] = Some a -> l[@a] = Some b.
Proof.
  intros.
  poses (lookup_in H0).
  rewrite <- mswap_in in P.
  poses (in_lookup_nodup H P); auto.
Qed.

Lemma swap_lookup_nodup {A B:Type} {decA:EqDec A equiv} {decB:EqDec B equiv} : forall {l} {a:A} {b:B}, NoDup (domain (mswap l)) -> l[@a] = Some b -> (mswap l)[@b] = Some a.
Proof.
  intros.
  apply swap_lookup_nodup'; dts idtac.
Qed.

End det.

Section bidet_assoc.

(* bidet says that an association list has not duplicate keys or duplicate values.
   This is important if we want to via the assocation list as a map in both directions,
   and don't want "garbage" -- key/values that are never found by lookup *)
Definition bidet {A B:Type} (l:list (A*B)) := NoDup (domain l) /\ NoDup (domain (mswap l)).

Context {A B:Type}.

Hint Unfold bidet.
Lemma bidet_swap : forall (l:list (A*B)), bidet l -> bidet (mswap l).
Proof.
  dts idtac.
Qed.

Global Instance bidet_perm : Proper (@Permutation (A*B) ==> iff) bidet.
Proof.
  dts idtac; first [rewrite <- H; auto | rewrite H; auto].
Qed.

Lemma bidet_app_inv : forall {a b:list (A*B)}, bidet (a++b) -> bidet a.
Proof.
  Hint Resolve NoDup_app_inv.  
  dts idtac.
Qed. 

Lemma bidet_nil : @bidet A B nil.
Proof.
  Hint Constructors NoDup.
  dts idtac.
Qed.

Lemma swap_lookup_nodup_iff {decA:EqDec A equiv} {decB:EqDec B equiv} : forall {l} (a:A) (b:B), bidet l -> ((mswap l)[@a] = Some b <-> l[@b] = Some a).
Proof.
  dts idtac.
  - apply swap_lookup_nodup'; auto.
  - apply swap_lookup_nodup; auto.
Qed.

Lemma bidet_in_eq : forall {l} {a:A} {b c:B}, bidet l -> In (a,b) l -> In (a,c) l -> b = c.
Proof.
  unfold bidet.
  Hint Resolve nodup_in_eq.
  intuition; eauto.
Qed.

Lemma bidet_in_eq_sym : forall {l} {a:A} {b:B} {c:A}, bidet l -> In (a,b) l -> In (c,b) l -> a = c.
Proof.
  unfold bidet.
  Hint Resolve nodup_in_eq.
  intuition; eauto.
  rewrite mswap_in in H0,H1.
  eauto.
Qed.

End bidet_assoc.

Ltac bidet_tac := 
  try match goal with
        | [H1:bidet ?l, H2: In (?a,?b) ?l, H3: In (?a,?c) ?l |- _ ] =>
          match H1 with
            | H2 => fail 1
            | _ => poses (bidet_in_eq H1 H2 H3); clear H2; try subst
          end
        | [H1:bidet ?l, H2: In (?a,?b) ?l, H3: In (?c,?b) ?l |- _ ] =>
          match H1 with
            | H2 => fail 1
            | _ => poses (bidet_in_eq_sym H1 H2 H3); clear H2; try subst
          end
        | [H1:bidet ?l, H2: lookup_assoc ?l ?a = Some ?b, H3: In (?a,?c) ?l |- _ ] =>
          match H1 with
            | H2 => fail 1
            | _ => poses (bidet_in_eq H1 (lookup_in H2) H3); clear H2; try subst
          end
        | [H1:bidet ?l, H2: lookup_assoc ?l ?a = Some ?b, H3: In (?c,?b) ?l |- _ ] =>
          match H1 with
            | H2 => fail 1
            | _ => poses (bidet_in_eq_sym H1 (lookup_in H2) H3); clear H2; try subst
          end
        | [H1:bidet ?l, H2: lookup_assoc ?l ?a = Some ?b, H3: lookup_assoc ?l ?a = Some ?c |- _ ] =>
          match H1 with
            | H2 => fail 1
            | _ => poses (bidet_in_eq H1 (lookup_in H2) (lookup_in H3)); clear H2; try subst
          end
        | [H1:bidet ?l, H2: lookup_assoc ?l ?a = Some ?b, H3: lookup_assoc ?l ?c = Some ?b |- _ ] =>
          match H1 with
            | H2 => fail 1
            | _ => poses (bidet_in_eq_sym H1 (lookup_in H2) (lookup_in H3)); clear H2; try subst
          end
      end.

