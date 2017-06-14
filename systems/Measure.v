Require Import Omega.

Require Import StructTact.StructTactics.
Require Import InfSeqExt.infseq.

Require Import Chord.Chord.
Import Chord.Chord.Chord.
Require Import Chord.ChordSemantics.
Import ChordSemantics.

Section Measure.

  Variable measure : global_state -> nat.
  Notation "| gst |" := (measure gst) (at level 50).

  Definition measure_bounded (n : nat) : infseq occurrence -> Prop :=
    always (now (fun o => |occ_gst o| <= n)).

  Definition measure_nonincreasing (o o' : occurrence) : Prop :=
    |occ_gst o'| <= |occ_gst o|.

  Definition measure_decreasing (o o' : occurrence) : Prop :=
    |occ_gst o'| < |occ_gst o|.

  Definition measure_zero (o : occurrence) : Prop :=
    |occ_gst o| = 0.

  Lemma measure_zero_elim :
    forall o,
      measure_zero o ->
      |occ_gst o| = 0.
  Proof.
    easy.
  Qed.

  Definition decreasing_inf_often_or_zero : infseq occurrence -> Prop :=
    now measure_zero \/_
    inf_often (consecutive measure_decreasing).

  Lemma measure_nonincreasing_stays_zero :
    forall o o',
      measure_nonincreasing o o' ->
      measure_zero o ->
      measure_zero o'.
  Proof.
    unfold measure_nonincreasing, measure_zero.
    intros.
    omega.
  Qed.

  Lemma measure_zero_stays_zero :
    forall ex,
      always (consecutive measure_nonincreasing) ex ->
      now measure_zero ex ->
      always (now measure_zero) ex.
  Proof.
    cofix c.
    intros.
    constructor; auto.
    do 2 destruct ex; simpl in *.
    apply c.
    - eauto using always_invar.
    - inv_prop always.
      unfold consecutive in *.
      simpl.
      eauto using measure_nonincreasing_stays_zero.
  Qed.

  Lemma measure_bounded_hd_elim :
    forall m n ex,
      measure_bounded n ex ->
      |occ_gst (hd ex)| = m ->
      m <= n.
  Proof.
    intros; destruct ex.
    now inv_prop measure_bounded.
  Qed.

  Lemma measure_bounded_monotonic :
    forall m n ex,
      m <= n ->
      measure_bounded m ex ->
      measure_bounded n ex.
  Proof.
    cofix c.
    intros.
    constructor; destruct ex as [o [o' ex]]; simpl in *.
    - inv_prop measure_bounded; simpl in *.
      omega.
    - eapply c; eauto.
      eapply always_invar; eauto.
  Qed.

  (** If the measure never increases and you can bound the measure of the first
      state, you can bound the entire sequence. *)
  Lemma nonincreasing_preserves_bound :
    forall ex,
      always (consecutive measure_nonincreasing) ex ->
      forall n,
        |occ_gst (hd ex)| <= n ->
        measure_bounded n ex.
  Proof.
    cofix c.
    constructor; destruct ex as [o [o' ex]]; simpl in *; [omega|].
    eapply c.
    - eauto using always_invar.
    - inv_prop measure_nonincreasing.
      unfold measure_nonincreasing in *.
      simpl in *.
      omega.
  Qed.

  (** If the measure never increases, you can bound the entire sequence by the
      measure of the first state. *)
  Lemma nonincreasing_global :
    forall ex,
      always (consecutive measure_nonincreasing) ex ->
      forall n,
        |occ_gst (hd ex)| = n ->
        measure_bounded n ex.
  Proof.
    auto using Nat.eq_le_incl, nonincreasing_preserves_bound.
  Qed.

  (** If the measure never increases and drops infinitely often, then it will
      eventually be less than its initial value (provided the initial value is
      nonzero). *)
  Lemma measure_drops :
    forall ex,
      always (consecutive measure_nonincreasing) ex ->
      decreasing_inf_often_or_zero ex ->
      forall n,
        |occ_gst (hd ex)| = S n ->
        eventually (now (fun o => |occ_gst o| < S n)) ex.
  Proof.
    intros.
    unfold decreasing_inf_often_or_zero in *.
    find_copy_apply_lem_hyp nonincreasing_global; auto.
    invc_prop or_tl.
    - destruct ex.
      simpl in *.
      congruence.
    - inv_prop inf_often.
      match goal with
      | H : eventually (consecutive measure_decreasing) _ |- _ =>
        induction H
      end.
      + destruct s as [o [o' s]].
        apply E_next; apply E0.
        unfold measure_decreasing in *.
        simpl in *; omega.
      + simpl.
        destruct s as [o s].
        destruct (lt_dec (|occ_gst o|) (|occ_gst x|)).
        * apply E_next; apply E0.
          simpl in *; omega.
        * assert (|occ_gst o| = |occ_gst x|).
          {
            find_apply_lem_hyp not_lt.
            apply Nat.le_antisymm; auto.
            inv_prop (always (consecutive measure_nonincreasing)).
            unfold measure_nonincreasing in *.
            auto.
          }
          apply E_next.
          simpl in *.
          repeat find_rewrite.
          eapply IHeventually; eauto;
            eapply always_invar; eauto.
  Qed.

  Lemma nat_strong_ind : 
    forall (P : nat -> Prop), 
      (forall n, (forall m, m < n -> P m) -> P n) -> 
      forall n, P n.
  Proof.
  Admitted.

  Lemma less_than_Sn_bounded_n :
    forall n ex,
      always (consecutive measure_nonincreasing) ex ->
      now (fun occ => |occ_gst occ| < S n) ex ->
      measure_bounded n ex.
  Proof.
  Admitted.

(**
Given a hypothesis H of the form

    H: forall ex,
          P ex ->
          Q ex ->
          rest,

replace H with

    H: forall ex,
          (Q /\_ P) ex ->
          rest.
*)
Ltac accum_and_tl H P Q rest ex :=
  let H' := fresh in
  rename H into H';
  assert (H: forall ex, (and_tl Q P) ex -> rest)
    by firstorder;
  clear H'.


Ltac prep_eventually_monotonic :=
  repeat lazymatch goal with
         | [H: forall ex, ?fst ex -> ?P ex -> @?conclusion ex,
              H_P : eventually ?P ?s |- _] =>
           fail
         | H: forall ex, ?fst ex -> ?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, ?fst ex -> @?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, @?fst ex -> ?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, @?fst ex -> @?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         end.

Ltac prep_always_inv :=
  apply always_inv;
  unfold and_tl in *;
  [intros; repeat break_and; break_and_goal|tauto].

Ltac lift_eventually lem :=
  pose proof lem;
  unfold continuously in *;
  prep_eventually_monotonic;
  eapply eventually_monotonic; eauto;
  try prep_always_inv.

  Lemma measure_bound_drops :
    forall n ex,
      measure_bounded (S n) ex ->
      always (consecutive measure_nonincreasing) ex ->
      decreasing_inf_often_or_zero ex ->
      eventually (measure_bounded n) ex.
  Proof.
    intros.
    destruct ex as [o ex].
    destruct (|occ_gst o|) eqn:?H.
    - apply E0.
      eapply measure_bounded_monotonic with (m:=0); [omega|].
      eapply nonincreasing_global; eauto.
    - find_copy_eapply_lem_hyp nonincreasing_global; eauto.
      inv_prop decreasing_inf_often_or_zero; [congruence|].
      eapply eventually_monotonic_simple.
      {
        intros; eapply (measure_bounded_monotonic n0 n); eauto.
        apply le_S_n.
        eapply measure_bounded_hd_elim; eauto.
      }
      eapply eventually_monotonic; try eapply less_than_Sn_bounded_n; eauto using always_invar.
      eapply measure_drops; eauto.
  Qed.

  Lemma measure_bounded_zero :
    forall ex,
      measure_bounded 0 ex ->
      always (now measure_zero) ex.
  Proof.
    cofix c.
    intros; constructor.
    - inv_prop measure_bounded.
      destruct ex; simpl in *.
      unfold measure_zero; omega.
    - destruct ex.
      simpl in *.
      apply c.
      eapply always_invar; eauto.
  Qed.

  (** TODO(ryan) move to infseq *)
  Lemma eventually_idempotent :
    forall T (P : infseq T -> Prop) ex,
      eventually (eventually P) ex ->
      eventually P ex.
  Proof.
  Admitted.

  Lemma decreasing_inf_often_or_zero_invar_when_nonincreasing :
    forall o ex,
      always (consecutive measure_nonincreasing) (Cons o ex) ->
      decreasing_inf_often_or_zero (Cons o ex) ->
      decreasing_inf_often_or_zero ex.
  Proof.
  Admitted.

  Lemma measure_decreasing_to_zero' :
    forall n ex,
      always (consecutive measure_nonincreasing) ex ->
      decreasing_inf_often_or_zero ex ->
      measure_bounded n ex ->
      eventually (now measure_zero) ex.
  Proof.
    intros n.
    induction n using nat_strong_ind.
    destruct n; subst_max.
    - intros.
      apply E0.
      find_apply_lem_hyp measure_bounded_zero.
      inv_prop always.
      assumption.
    - intros.
      find_copy_apply_lem_hyp measure_bound_drops; auto.
      pose proof (H n).
      forwards.
      omega.
      specialize (H4 H5); clear H5.
      eapply eventually_idempotent.
      lift_eventually H4.
      + unfold and_tl; intros; break_and_goal; break_and.
        * eauto using decreasing_inf_often_or_zero_invar_when_nonincreasing.
        * eauto using always_invar.
      + split; auto.
  Qed.

  Lemma measure_decreasing_to_zero :
    forall ex,
      decreasing_inf_often_or_zero ex ->
      always (consecutive measure_nonincreasing) ex ->
      continuously (now measure_zero) ex.
  Proof.
    intros.
    remember (|occ_gst (hd ex)|) as n.
    find_copy_eapply_lem_hyp nonincreasing_global; auto.
    find_copy_eapply_lem_hyp measure_decreasing_to_zero'; eauto.
    lift_eventually measure_zero_stays_zero.
    eauto using always_invar.
  Qed.

  (* TODO(ryan) move to infseq *)
  Lemma eventually_and_tl_comm :
    forall T (P Q : infseq T -> Prop) s,
      eventually (P /\_ Q) s ->
      eventually (Q /\_ P) s.
  Proof.
    intros until 0.
    apply eventually_monotonic_simple.
    intros.
    now rewrite and_tl_comm.
  Qed.

  Lemma measure_decreasing_to_zero_continuously :
    forall ex,
      continuously (consecutive measure_nonincreasing) ex ->
      always decreasing_inf_often_or_zero ex ->
      continuously (now measure_zero) ex.
  Proof.
    intros.
    eapply eventually_idempotent.
    eapply eventually_monotonic_simple with (P:=decreasing_inf_often_or_zero /\_ always (consecutive measure_nonincreasing)).
    - intros.
      unfold and_tl in *; break_and.
      eapply measure_decreasing_to_zero; eauto.
    - find_eapply_lem_hyp eventually_always_cumul; eauto.
      apply eventually_and_tl_comm.
      eapply eventually_monotonic_simple; [|eauto].
      intros.
      split.
      + now inv_prop and_tl.
      + inv_prop and_tl.
        now inv_prop always.
  Qed.

End Measure.
