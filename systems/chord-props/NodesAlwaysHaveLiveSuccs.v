Require Import List.
Import ListNotations.
Require Import Omega.

Require Import StructTact.StructTactics.

Require Import Chord.Chord.

Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.RingCorrect.

Definition nonempty_succ_lists (gst : global_state) : Prop :=
  forall h st,
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    joined st = true ->
    succ_list st <> [].

Lemma nodes_have_nonempty_succ_lists :
  forall gst,
    reachable_st gst ->
    nonempty_succ_lists gst.
Proof.
  unfold nonempty_succ_lists.
  intros.
  assert (live_node_in_succ_lists gst) by eauto.
  unfold live_node_in_succ_lists in *.
  assert (exists s, best_succ gst h s) by
      eauto using live_node_characterization.
  break_exists_name s.
  inv_prop best_succ; repeat break_exists; break_and.
  repeat find_rewrite.
  find_injection.
  intro.
  repeat find_rewrite.
  find_apply_lem_hyp (f_equal (@length addr)).
  rewrite app_length in *.
  simpl in *; omega.
Qed.
