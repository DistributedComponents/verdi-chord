Require Import Omega.

Require Import StructTact.StructTactics.
Require Import InfSeqExt.infseq.

Require Import Chord.Chord.
Import Chord.Chord.Chord.
Require Import Chord.ChordSemantics.
Import ChordSemantics.

Definition measure_nonincreasing (measure : global_state -> nat) (o o' : occurrence) : Prop :=
  measure (occ_gst o') <= measure (occ_gst o).

Definition measure_decreasing (measure : global_state -> nat) (o o' : occurrence) : Prop :=
  measure (occ_gst o') < measure (occ_gst o).

Definition measure_zero (measure : global_state -> nat) (o : occurrence) : Prop :=
  measure (occ_gst o) = 0.

Lemma measure_zero_elim :
  forall measure o,
    measure_zero measure o ->
    measure (occ_gst o) = 0.
Proof.
  easy.
Qed.

Definition decreasing_inf_often_or_zero (measure : global_state -> nat) : infseq occurrence -> Prop :=
  inf_often (consecutive (measure_decreasing measure)) \/_ now (measure_zero measure).

Lemma measure_nonincreasing_stays_zero :
  forall measure o o',
    measure_nonincreasing measure o o' ->
    measure_zero measure o ->
    measure_zero measure o'.
Proof.
  unfold measure_nonincreasing, measure_zero.
  intros.
  omega.
Qed.

Lemma measure_zero_stays_zero :
  forall measure ex,
    always (consecutive (measure_nonincreasing measure)) ex ->
    now (measure_zero measure) ex ->
    always (now (measure_zero measure)) ex.
Proof.
  intros measure.
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

Lemma always_measure_le_monotonic :
  forall measure ex m n,
    m <= n ->
    always (now (fun o => measure (occ_gst o) <= m)) ex ->
    always (now (fun o => measure (occ_gst o) <= n)) ex.
Proof.
  intro measure.
  cofix c.
  intros.
  constructor; destruct ex as [o [o' ex]]; simpl in *.
  - inv_prop always; simpl in *.
    omega.
  - eapply c; eauto using always_invar.
Qed.

Definition measure_bounded (measure : global_state -> nat) (n : nat) : infseq occurrence -> Prop :=
  always (now (fun o => measure (occ_gst o) <= n)).

Lemma nonincreasing_preserves_bound :
  forall measure ex,
    always (consecutive (measure_nonincreasing measure)) ex ->
    forall n,
      measure (occ_gst (hd ex)) <= n ->
      always (now (fun o => measure (occ_gst o) <= n)) ex.
Proof.
  intros measure.
  cofix c.
  constructor; destruct ex as [o [o' ex]]; simpl in *; [omega|].
  eapply c.
  - eauto using always_invar.
  - inv_prop measure_nonincreasing.
    unfold measure_nonincreasing in *.
    simpl in *.
    omega.
Qed.

Lemma nonincreasing_global :
  forall measure ex,
    always (consecutive (measure_nonincreasing measure)) ex ->
    forall n,
      measure (occ_gst (hd ex)) = n ->
      always (now (fun o => measure (occ_gst o) <= n)) ex.
Proof.
  auto using Nat.eq_le_incl, nonincreasing_preserves_bound.
Qed.

Lemma measure_drops :
  forall measure ex,
    always (consecutive (measure_nonincreasing measure)) ex ->
    decreasing_inf_often_or_zero measure ex ->
    forall n,
      measure (occ_gst (hd ex)) = S n ->
      eventually (now (fun o => measure (occ_gst o) < S n)) ex.
Proof.
  intros.
  unfold decreasing_inf_often_or_zero in *.
  find_copy_apply_lem_hyp nonincreasing_global; auto.
  invc_prop or_tl.
  - inv_prop inf_often.
    induction H0.
    + destruct s as [o [o' s]].
      apply E_next; apply E0.
      unfold measure_decreasing in *.
      simpl in *; omega.
    + simpl.
      destruct s as [o s].
      destruct (lt_dec (measure (occ_gst o)) (measure (occ_gst x))).
      * apply E_next; apply E0.
        simpl in *; omega.
      * assert (measure (occ_gst o) = measure (occ_gst x)).
        {
          find_apply_lem_hyp not_lt.
          apply Nat.le_antisymm; auto.
          inv_prop (always (consecutive (measure_nonincreasing measure))).
          unfold measure_nonincreasing in *.
          auto.
        }
        apply E_next.
        simpl in *.
        repeat find_rewrite.
        eauto using always_invar.
  - destruct ex.
    simpl in *.
    congruence.
Qed.

Lemma measure_decreasing_to_zero' :
  forall measure ex,
    always (consecutive (measure_nonincreasing measure)) ex ->
    decreasing_inf_often_or_zero measure ex ->
    continuously (now (measure_zero measure)) ex.
Proof.
Admitted.

Lemma measure_decreasing_to_zero :
  forall measure ex,
    continuously (consecutive (measure_nonincreasing measure)) ex ->
    decreasing_inf_often_or_zero measure ex ->
    continuously (now (measure_zero measure)) ex.
Proof.
Admitted.