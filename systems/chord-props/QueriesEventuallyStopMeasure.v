Require Import List.
Import ListNotations.
Require Import Relations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Update.
Require Import StructTact.Dedup.
Require Import StructTact.ListTactics.
Require Import StructTact.ListUtil.
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.
Require Import Chord.InfSeqTactics.

Require Import Chord.Chord.

Require Import Chord.HandlerLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.
Require Import Chord.LabeledLemmas.
Require Import Chord.ChannelLemmas.
Require Import Chord.LiveNodesNotClients.
Require Import Chord.QueryInvariant.
Require Import Chord.NodesHaveState.

Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.

Section find_chain.

  Variable A : Type.
  Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.
  Variable all : list A.
  Variable nodup_all : NoDup all.
  Variable next : A -> option A.

  Variable next_in_all :
    forall a a',
      In a all ->
      next a = Some a' ->
      In a' all.

  Fixpoint nextn a n : option A :=
    match n with
    | 0 => Some a
    | S n => match next a with
            | None => None
            | Some a => nextn a n
            end
    end.

  Variable no_cycles :
    forall a n,
      nextn a n <> Some a.

  Lemma nextn_in_all :
    forall n a a',
      In a all ->
      nextn a n = Some a' ->
      In a' all.
  Proof.
    induction n; intros; simpl in *.
    - solve_by_inversion.
    - break_match; try congruence. eauto.
  Qed.

  Fixpoint chain (a : A) (fuel : nat) :=
    match fuel with
    | 0 => None
    | S fuel =>
      match (next a) with
      | None => Some [a]
      | Some a' =>
        match (chain a' fuel) with
        | None => None
        | Some c =>
          Some (a :: c)
        end
      end
    end.

  Lemma more_fuel_preserves_some :
    forall n n' a c,
      n <= n' ->
      chain a n = Some c ->
      chain a n' = Some c.
  Proof.
    induction n; intros; simpl in *.
    - congruence.
    - destruct n'; try omega.
      simpl.
      break_match; intuition.
      destruct (chain a0 n) eqn:chain_def; try congruence.
      specialize (IHn n').
      eapply IHn in chain_def; eauto; try omega.
      repeat find_rewrite. auto.
  Qed.      

  Lemma sufficient_fuel' :
    forall fuel l a,
      NoDup l ->
      (forall a' n, nextn a n = Some a' -> In a' l) ->
      S (length l) <= fuel ->
      exists c,
        chain a fuel = Some c.
  Proof.
    induction fuel; intros.
    - simpl in *. omega.
    - simpl.
      break_match; eauto.
      specialize (IHfuel (remove A_eq_dec a0 l) a0).
      conclude_using ltac:(eauto using remove_NoDup).
      forward IHfuel.
      {
        intros.
        apply remove_preserve.
        - intro. subst. intuition. eauto.
        - cut (nextn a (S n) = Some a'); eauto.
          simpl. repeat find_rewrite. auto.
      }
      concludes.
      assert (length l <> 0).
      {
        destruct l; simpl in *; auto.
        cut (nextn a 1 = Some a0); eauto.
        simpl. repeat find_rewrite. auto.
      }
      forward IHfuel.
      {
        cut (S (length (remove A_eq_dec a0 l)) = length l); [omega|].
        eapply remove_length_in; eauto.
        cut (nextn a 1 = Some a0); eauto.
        simpl. repeat find_rewrite. auto.
      } concludes.
      break_exists. repeat find_rewrite. eauto.
  Qed.

  Lemma sufficient_fuel :
    forall a,
      In a all ->
      exists c,
        chain a (length all) = Some c.
  Proof.
    intros.
    eapply sufficient_fuel' with (l := (remove A_eq_dec a all)).
    - eauto using remove_NoDup.
    - intros. apply remove_preserve; eauto. eauto using nextn_in_all.
    - erewrite remove_length_in; eauto.
  Qed.
    
End find_chain.