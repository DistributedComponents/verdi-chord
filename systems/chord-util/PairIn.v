Require Import List.
Import ListNotations.
Require Import mathcomp.ssreflect.ssreflect.

Require Import StructTact.StructTactics.

Inductive pair_in {A : Type} : A -> A -> list A -> Prop :=
| pair_in_head :
    forall a b l,
      pair_in a b (a :: b :: l)
| pair_in_rest :
    forall a b l,
      pair_in a b l ->
      forall x,
        pair_in a b (x :: l).

Lemma pair_in_sound :
  forall A (l : list A) xs a b ys,
    l = xs ++ a :: b :: ys ->
    pair_in a b l.
Proof.
move => A.
elim => //=; first by case.
move => a l IH.
case => /= [a0 b|a0 l0 a1 b] ys H_eq.
- find_injection.
  exact: pair_in_head.
- find_injection.
  apply pair_in_rest.
  exact: IH.
Qed.
Hint Resolve pair_in_sound.

Lemma pair_in_map :
  forall A B (f : A -> B) a b l,
    pair_in a b (map f l) ->
    exists a0 b0,
      a = f a0 /\
      b = f b0 /\
      pair_in a0 b0 l.
Proof.
  intros.
  remember (map f l) as fl; revert Heqfl.
  generalize l.
  induction H; intros; subst.
  - destruct l1 as [|? [|? ?]]; simpl in *.
    + congruence.
    + congruence.
    + find_injection.
      repeat eexists.
      constructor.
  - destruct l1; simpl in *.
    + congruence.
    + find_injection.
      specialize (IHpair_in l1 eq_refl); break_exists; break_and;
        do 2 eexists; repeat split; try constructor; eauto.
Qed.

Lemma map_pair_in :
  forall A B (f : A -> B) a b a0 b0 l,
    pair_in a0 b0 l ->
    a = f a0 ->
    b = f b0 ->
    pair_in a b (map f l).
Proof.
  induction 0; intros.
  - repeat inv_prop (@pair_in A).
  - inv_prop (@pair_in A).
    + constructor; eauto.
    + constructor; eauto.
Qed.

Lemma pair_in_firstn :
  forall (A : Type) (a b : A) k l,
    pair_in a b (firstn k l) ->
    pair_in a b l.
Proof.
move => A a b k l.
move: l a b k.
elim => //=.
- move => a b.
  by case.
- move => a l IH.
  move => a0 b.
  case => //=; first by move => H_p; inversion H_p.
  move => n H_p.
  inversion H_p; subst.
  * destruct n => //=.
    destruct l => //=.
    simpl in *.
    find_injection.
    exact: pair_in_head.
  * apply pair_in_rest.
    by eapply IH; eauto.
Qed.
