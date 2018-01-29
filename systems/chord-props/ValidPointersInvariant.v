Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.

Require Import Chord.Chord.

Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.

Set Bullet Behavior "Strict Subproofs".

Theorem valid_ptrs_global_inductive :
  forall gst,
    reachable_st gst ->
    valid_ptrs_global gst.
Proof using.
Admitted.

Lemma cur_request_valid :
  forall gst,
    reachable_st gst ->
    forall h st dst q m,
      sigma gst h = Some st ->
      cur_request st = Some (dst, q, m) ->
      valid_ptr gst dst.
Proof.
  intros.
  find_apply_lem_hyp valid_ptrs_global_inductive.
  unfold valid_ptrs_global in *.
  assert (lift_pred_opt (valid_ptrs_state gst) (Some st)).
  {
    repeat find_reverse_rewrite.
    firstorder.
  }
  invcs_prop valid_ptrs_state.
  unfold valid_ptrs_state, valid_ptrs_cur_request, valid_ptrs_some_cur_request in *.
  break_and.
  repeat find_rewrite.
  inv_prop valid_ptr; tauto.
Qed.
