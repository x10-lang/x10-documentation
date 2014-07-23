(*
 *  (C) Copyright IBM Corporation 2013-2014.
 *)

(* Properties of functional lists needed by parts of the development *)
Require Export Util.
Require Export List.
Require Export Permutation.

Require Import Le.

Require Import Coq.Sorting.Sorted.
Require Import Coq.Logic.Eqdep_dec.

Section ListUtil.

Context {A:Type}.
Context {dec:forall x y : A, {x = y} + {x <> y}}.

Ltac list_tac := try match goal with
    | [H:NoDup (_ :: _) |- _] => inversion H; subst; clear H
    | [H:context [(dec ?x ?y)] |- _] =>   let Heq := (fresh "Heq") in 
    destruct (dec x y) as [Heq|Heq]; [try rewrite Heq in *|]
    | [|- context [(dec ?x ?y)]] => let Heq := (fresh "Heq") in 
    destruct (dec x y) as [Heq|Heq]; [try rewrite Heq in *|]
    | [|- NoDup (_ :: _)] => constructor
end.

Ltac t' tac := dts ltac:(list_tac; try tac).

Ltac t := t' idtac.

Hint Unfold incl.

Global Instance incl_pre : PreOrder (@incl A).
Proof.
  split; t.
Qed.

Ltac app_tac := try match goal with 
    | [H: In _ (_ ++ _) |- _ ] => apply in_app_iff in H
end.

Lemma incl_trans_app {a:list A} b {c d}: incl a (c ++ b) -> incl b (c ++ d) -> incl a (c ++ d).
Proof.
unfold incl; intuition.
specialize (H _ H1).
app_tac; intuition.
Qed.

Lemma remove_in : forall l x a,  In x (remove dec a l) -> In x l.
Proof.
  induction l; t' firstorder.
Qed.
  
Lemma nin_remove : forall l a,  ~ In a l -> remove dec a l = l.
Proof.
  induction l; t.
Qed.

Hint Rewrite nin_remove using solve[eauto] : rewrites.

Lemma nodup_in_remove_length : forall l a, In a l -> NoDup l -> S (length (remove dec a l)) = length l.
Proof.
  induction l; t.
Qed.

Hint Resolve remove_in.

Lemma incl_nin : forall l l' (a:A), ~In a l -> incl l (a::l') -> incl l l'.
Proof.
  firstorder t.
Qed.

Lemma remove_nodup : forall l a, NoDup l -> NoDup (remove dec a l).
Proof.
  induction l; t.
Qed.

Lemma remove_incl_cons : forall l l' a, incl l (a :: l') -> incl (remove dec a l) l'.
Proof.
  t.
  destruct (H a0); t.
  eelim (remove_In); t.
Qed.

Hint Resolve remove_nodup remove_incl_cons incl_nin.

Lemma remove_app x (l1 l2:list A)
  : remove dec x (l1 ++ l2) = remove dec x l1 ++ remove dec x l2.
Proof.
  revert l2. induction l1; simpl; trivial; intros.
  destruct (dec x a); subst; auto.
  rewrite <- app_comm_cons; congruence.
Qed.

Lemma remove_idem (x:A) l : remove dec x (remove dec x l) = remove dec x l.
Proof.
  induction l; dt idtac.
  destruct (dec x a); subst; auto; simpl;
  destruct (dec x a); congruence.
Qed.

Lemma remove_comm (x v:A) l : remove dec x (remove dec v l) = remove dec v (remove dec x l).
Proof.
  induction l; dt idtac.
  destruct (dec v a); simpl; destruct (dec x a); subst; simpl; auto.
  - destruct (dec a a); congruence.
  - destruct (dec v a); congruence.
Qed.

Lemma remove_nin  (x:A) l :  ~ In x (remove dec x l).
Proof.
  induction l; dt idtac.
  destruct (dec x a); intuition; dts idtac.
Qed.

Lemma remove_in_iff (x a:A) l : x <> a -> (In x (remove dec a l) <-> In x l).
Proof.
  induction l; dt idtac; intuition; subst.
  - destruct (dec a a0); subst; simpl in *; intuition.
  - destruct (dec a x); subst; simpl in *; intuition.
  - destruct (dec a a0); subst; simpl in *; intuition.
Qed.

Lemma nodup_incl_le : forall (l l':list A), NoDup l -> incl l l' -> length l <= length l'.
Proof.
  intros l l'; revert l.
  induction l'; t.
  - destruct l; t. eelim H0; auto.
  - generalize (H0 a); intros.
    destruct (in_dec dec a l'); t.
    + firstorder t.
    + destruct (in_dec dec a l); [|firstorder t].
      rewrite <- (nodup_in_remove_length l a i H); t.
      apply le_n_S; apply IHl'; t.
      destruct (H0 _ (remove_in _ _ _ H1)); t.
      eelim (remove_In); t.
Qed.

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ => idtac
  end.

Ltac extend P :=
  let t := type of P in
    notHyp t; generalize P; intro.

Ltac perm_tac := 
        try match goal with
          | [H1:In ?x ?l, H3:Permutation ?l2 ?l |- _ ] =>
            extend (Permutation_in _ (symmetry H3) H1)
          | [H1:In ?x ?l, H3:Permutation ?l ?l2 |- _ ] =>
            extend (Permutation_in _ H3 H1)
            end.

Lemma NoDup_perm : forall {a b:list A}, NoDup a -> Permutation a b -> NoDup b.
Proof.
intros a b nd p.
revert nd.
 revert a b p.
    apply (Permutation_ind_bis (fun l l' => NoDup l -> NoDup l')); t' perm_tac.
Qed.

Global Instance NoDup_perm' : Proper (@Permutation A ==> iff) (@NoDup A).
Proof.
Hint Resolve NoDup_perm Permutation_sym.
t. 
Qed.

Section nodup_eqdec.
Variable (A_eqdec:forall (x y:A), {x = y} + { x <> y}).
Hint Constructors NoDup.
Program Fixpoint NoDup_dec (l:list A) : {NoDup l} + {~NoDup l} 
  := match l with
       | nil => left _
       | x::ls => match in_dec A_eqdec x ls, NoDup_dec ls with
                    | right _, left _ => left _
                    | left _, _ => right _
                    | _, right _ => right _
                  end
     end.
Next Obligation.
inversion 1; subst; intuition.
inversion 1; subst; intuition.
Defined.
Next Obligation.
inversion 1; subst; intuition.
Defined.
End nodup_eqdec.

Hint Rewrite app_nil_r app_ass : rewrites.
Hint Resolve NoDup_remove_1 NoDup_remove_2.

Hint Rewrite @remove_idem @remove_app : rewrites.

Lemma NoDup_app_inv : forall {a b:list A}, NoDup (a++b) -> NoDup a.
Proof.
  induction b; t.
Qed.

Hint Resolve NoDup_app_inv.

Lemma NoDup_app_inv2 : forall {a b:list A}, NoDup (a++b) -> NoDup b.
Proof.
  Hint Resolve Permutation_app_comm.
  t.
Qed.

Hint Resolve NoDup_app_inv2.

Lemma incl_perm1 : forall {a b c:list A}, incl a c -> Permutation a b -> incl b c.
Proof.
  Hint Resolve Permutation_in Permutation_sym.
  t.
Qed.

Lemma incl_perm2 : forall {a b c:list A}, incl a b -> Permutation b c -> incl a c.
Proof.
  Hint Resolve Permutation_in Permutation_sym.
  t.
Qed.

Global Instance incl_perm' : Proper (@Permutation A ==> @Permutation A ==> iff) (@incl A).
Proof.
Hint Resolve Permutation_sym.
t.
Qed.

Definition disjoint (l1 l2:list A) := forall a, In a l1 -> In a l2 -> False.

Hint Unfold disjoint.
Global Instance disjoint_perm : Proper ((@Permutation A) ==> (@Permutation A) ==> iff) disjoint.
Proof.
  t' perm_tac.
Qed.

Global Instance disjoint_symm : Symmetric disjoint.
Proof.
  t.
Qed.

Lemma disjoint_irrefl : forall {l}, disjoint l l -> l = nil.
Proof.
  unfold disjoint; destruct l; intuition.
  eelim H; t. 
Qed.

Lemma disjoint_cons : forall {a} {l1 l2:list A}, (disjoint l1 l2 /\ ~ In a l2) <-> disjoint (a::l1) l2.
Proof.
  t.
Qed.  

Hint Resolve in_or_app.
Lemma disjoint_app : forall {l1 l2 l3:list A},
                       disjoint l1 l3 /\ disjoint l2 l3 <-> disjoint (l1 ++ l2) l3.
Proof.
  t' app_tac.
Qed.

Lemma NoDup_app_dis : forall a b, NoDup (a++b) -> disjoint a b.
Proof.
  t.
  destruct (in_split _ _ H0) as [a1[a2 aeq]].
  t.
  apply NoDup_app_inv2 in H.
  t.
Qed.

Lemma NoDup_app : forall a b, disjoint a b -> NoDup a -> NoDup b -> NoDup (a++b).
Proof.
  induction a; t' app_tac.
Qed.

Lemma NoDup_app_iff : forall a b, (disjoint a b /\ NoDup a /\ NoDup b) <-> NoDup (a++b).
Proof.
  Hint Resolve NoDup_app NoDup_app_dis NoDup_app_inv NoDup_app_inv2.
  intuition; eauto.
Qed.

Section Ord.
(* defines a list that is sorted, for some order *)
Context {gt:A->A->Prop}.
Context (gt_dec : forall (a1 a2:A), {gt a1 a2} + {~ gt a1 a2}).
Context {gt_order : StrictOrder gt}.

  Fixpoint sorted_nd (l:list A) :=
    match l with
      | nil => true
      | x::xs => match xs with
                   | nil => true
                   | y :: ys => if gt_dec x y then sorted_nd xs else false
                 end
    end.

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
    | [H:context [(@equiv_dec ?A ?B ?C ?D ?X ?Y)] |- _] => destruct (@equiv_dec A B C D X Y); unfold equiv, complement in *; try subst; try congruence
    | [|- context [(@equiv_dec ?A ?B ?C ?D ?X ?Y)]] => destruct (@equiv_dec A B C D X Y);  unfold equiv, complement in *; try subst; try congruence
    end; intros; simpl in *; trivial).

  Lemma sorted_nd_ext : forall l (p1 p2:sorted_nd l = true), p1 = p2.
    Proof.
      intros. apply eq_proofs_unicity. decide equality.
    Qed.


  Lemma sorted_LocallySorted : forall l, sorted_nd l = true <-> LocallySorted gt l.
Proof.
  induction l; simpl; intuition try constructor;
    destruct l; tac; try solve[constructor; auto].

  inversion H1; auto.
  inversion H1; auto.
Qed.

Lemma sorted_StronglySorted : forall l, sorted_nd l = true <-> StronglySorted gt l.
Proof.
  intros.
  rewrite sorted_LocallySorted, <- Sorted_LocallySorted_iff. 
  split.
  apply Sorted_StronglySorted. 
  red. apply transitivity. 
  apply StronglySorted_Sorted.
Qed.


Lemma Forall_nin : forall a l, Forall (gt a) l -> ~ In a l.
Proof.
  induction l; [auto|intros].
  inversion H; subst; intro.
  inversion H0; subst. 
    eapply irreflexivity; eauto.
    elim IHl; auto.
Qed.  

Lemma Sorted_NoDup : forall l, StronglySorted gt l -> NoDup l.
Proof.
  induction l; intros.
   constructor.
   inversion H; subst.
   constructor; auto. eapply Forall_nin; eauto.
Qed.

Lemma sorted_nd_NoDup : forall l, sorted_nd l = true -> NoDup l.
Proof.
  intros. 
  eapply Sorted_NoDup; eapply sorted_StronglySorted; eauto.
Qed.


End Ord.

End ListUtil.

Section List2Util.
Context {A B:Type}.

Section fb2.
Context (f:A->B->bool).
Fixpoint forallb2 (l1:list A) (l2:list B): bool :=
      match l1,l2 with
        | nil, nil => true
        | a1::l1, a2::l2 => f a1 a2 && forallb2 l1 l2
        | _, _ => false
      end.


Lemma forallb2_forallb : forall (l1:list A) (l2:list B), 
  (length l1 = length l2) ->
  forallb (fun xy => f (fst xy) (snd xy)) (combine l1 l2) = forallb2 l1 l2.
Proof.
  induction l1; destruct l2; dt idtac. 
  rewrite IHl1 by congruence.
  trivial.
Qed.

Lemma forallb2_forallb_true : forall (l1:list A) (l2:list B), 
  (length l1 = length l2 /\ forallb (fun xy => f (fst xy) (snd xy)) (combine l1 l2) = true)
   <->
   forallb2 l1 l2 = true.
Proof.
  Hint Unfold iff.
  induction l1; destruct l2; dt firstorder.
Qed.  

Lemma forallb2_Forallb : forall l1 l2, forallb2 l1 l2 = true <-> Forall2 (fun x y => f x y = true) l1 l2.
Proof.
  Hint Constructors Forall2.
  Ltac inv := try match goal with 
                | [H:Forall2 _ _ (_::_) |- _ ] => inversion H; clear H
                | [H:Forall2 _ (_::_) _ |- _ ] => inversion H; clear H
              end; firstorder.
  induction l1; destruct l2; dt inv.
Qed.

End fb2.

Lemma Forall2_incl : forall (f1 f2:A->B->Prop) l1 l2, 
  (forall x y, In x l1 -> In y l2 -> f1 x y-> f2 x y) ->
  Forall2 f1 l1 l2 -> Forall2 f2 l1 l2.
Proof.
  Hint Constructors Forall2.
  intros.
  induction H0; dts firsorder.
Qed.

Lemma forallb2_eq : forall (f1 f2:A->B->bool) l1 l2, 
  (forall x y, In x l1 -> In y l2 -> f1 x y = f2 x y) ->
  forallb2 f1 l1 l2 = forallb2 f2 l1 l2.
Proof.
  induction l1; destruct l2; simpl; intuition.
  f_equal; auto.
Qed.

End List2Util.

Lemma forallb2_sym : forall {A B} {f:A->B->bool} {l1 l2}, 
                       forallb2 f l1 l2 = forallb2 (fun x y => f y x) l2 l1.
Proof.
  induction l1; destruct l2; simpl; intuition.
  f_equal; trivial.
Qed.

Lemma forallb_map {A B} f (mf:A->B) m : forallb f (map mf m) = forallb ((fun x => f (mf x))) m.
Proof.
  induction m; simpl; auto.
  f_equal; auto.
Qed.

Lemma forallb_eq {A} (f g:A->bool) m : 
  (forall a, In a m -> f a = g a) ->
  forallb f m = forallb g m.
Proof.
  induction m; simpl; intuition.
  f_equal; auto.
Qed.

Lemma forallb_forall_false {A:Type} {f l} : forallb f l = false 
                                            -> exists x:A, In x l /\  f x = false.
Proof.
  induction l; simpl; intuition.
  rewrite andb_false_iff in H.
  destruct H; eauto.
  destruct (IHl H); intuition; eauto.
Qed.

Lemma incl_dec {A:Type} {dec:EqDec A eq} (l1 l2:list A) : {incl l1 l2} + {~ incl l1 l2}.
Proof.
  case_eq (forallb (fun a => if (in_dec dec a l2) then true else false) l1); intro fb; unfold incl.
  - left; intros a ia. rewrite forallb_forall in fb.
    specialize (fb _ ia). destruct (in_dec dec a l2); intuition.
  - right. destruct (forallb_forall_false fb); intuition.
    destruct (in_dec dec x l2); intuition.
Qed.

Global Instance perm_in {A} : Proper (eq ==> (@Permutation A) ==> iff) (@In A).
Proof.
  Hint Resolve Permutation_in Permutation_sym.
  dts idtac.
Qed.

Ltac app_tac := try match goal with 
    | [H: In _ (_ ++ _) |- _ ] => apply in_app_iff in H
end.

Hint Rewrite @remove_idem @remove_app : rewrites.

Lemma fold_right_map {A B C:Type} (f:B->C->C) (g:A->B) (v:C) (l:list A) :
  fold_right f v (map g l) = fold_right (fun x => f (g x)) v l.
Proof.
  induction l; simpl; trivial.
  rewrite IHl; trivial.
Qed.

Lemma fold_right_equiv {A B:Type} (f g:A->B->B) v l :
  (forall a, In a l -> forall b, f a b = g a b) ->
  fold_right f v l = fold_right g v l.
Proof.
  induction l; simpl; trivial; intros.
  rewrite IHl; auto.
Qed.

Lemma fold_right_Forall {A:Type} (f:A->Prop) l :
  fold_right (fun a b => f a /\ b) True l <-> Forall f l.
Proof.
  Hint Constructors Forall.
  induction l; simpl; intuition; inversion H1; intuition.
Qed.
