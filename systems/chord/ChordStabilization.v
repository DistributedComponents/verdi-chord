Require Import InfSeqExt.infseq.
Require Import StructTact.StructTactics.
Require Import Chord.InfSeqTactics.

Require Import Chord.Chord.

Require Import Chord.LabeledLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.
Require Import Chord.LabeledMeasures.

Require Import Chord.QueriesEventuallyStop.

Require Import Chord.ChordCorrectPhaseOne.
Require Import Chord.ChordCorrectPhaseTwo.
Require Import Chord.ChordCorrectPhaseThree.

Set Bullet Behavior "Strict Subproofs".
(* Open Scope nat_scope. *)

Definition ideal (gst : global_state) : Prop :=
  forall h st,
    live_node gst (addr_of h) ->
    wf_ptr h ->
    sigma gst (addr_of h) = Some st ->
    correct_succs gst h st /\
    length (succ_list st) = Chord.SUCC_LIST_LEN /\
    pred_correct gst h (pred st).

Theorem phases_locally_sufficient :
  forall gst,
    preds_and_first_succs_correct gst ->
    all_succs_correct gst ->
    ideal gst.
Proof.
  intros gst H_preds H_succs.
  unfold ideal; intros h st.
  destruct H_preds as [H_preds _].
  specialize (H_preds h st).
  specialize (H_succs h st).
  tauto.
Qed.

Theorem phases_sufficient :
  forall ex,
    now (fun occ =>
           preds_and_first_succs_correct (occ_gst occ) /\
           all_succs_correct (occ_gst occ))
      ex ->
    now (fun occ => ideal (occ_gst occ)) ex.
Proof.
  eapply now_monotonic.
  intros.
  break_and.
  now auto using phases_locally_sufficient.
Qed.

Lemma phase_two_without_phase_one :
  forall ex : infseq occurrence,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ now circular_wait) ex ->
    continuously (now phase_two) ex.
Proof.
  intros.
  find_copy_eapply_lem_hyp phase_one_continuously; eauto.
  apply eventually_idempotent.
  lift_eventually phase_two_continuously.
  - intros.
    unfold and_tl in *; break_and.
    repeat (split; invar_eauto).
  - firstorder.
Qed.

Theorem chord_stabilization :
  forall ex : infseq.infseq occurrence,
    reachable_st (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    continuously (now (fun o => ideal (occ_gst o))) ex.
Proof.
  intros.
  find_copy_eapply_lem_hyp phase_two_without_phase_one; eauto.
  find_copy_eapply_lem_hyp phase_three; eauto.
  eapply continuously_monotonic.
  eapply phases_sufficient.
  find_continuously_and_tl.
  eapply continuously_monotonic; [|eassumption].
  intros [o s].
  cbn; eauto.
Qed.
