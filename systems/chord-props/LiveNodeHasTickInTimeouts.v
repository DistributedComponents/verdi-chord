Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.
Require Import StructTact.Util.

Require Import InfSeqExt.infseq.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.

Set Bullet Behavior "Strict Subproofs".

Lemma live_node_has_Tick_in_timeouts' :
  forall gst h,
    reachable_st gst ->
    live_node gst h ->
    In Tick (timeouts gst h).
Proof.
  intros. induct_reachable_st.
  - intros. unfold live_node in *.
    intuition. break_exists. intuition.
    find_copy_apply_lem_hyp sigma_initial_st_start_handler.
    assert (In h initial_nodes) by admit.
    find_apply_lem_hyp timeouts_initial_st_start_handler.
    break_exists.
    repeat find_rewrite.
    simpl in *.
    subst. unfold start_handler in *.
    repeat break_match; simpl in *; try discriminate.
    + subst. unfold empty_start_res in *. find_inversion.
      simpl in *. discriminate.
    + subst. find_inversion. simpl in *. discriminate.
    + find_inversion. rewrite_update. in_crush.
  -

    
  
(*
New nodes have no Tick.
A node with no Tick sets joined = true iff it also registers a Tick.
Having a Tick is preserved by the step.
DIFFICULTY: 3
USED: In phase one.
*)

Admitted.


Lemma live_node_has_Tick_in_timeouts :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    live_node (occ_gst (hd ex)) h ->
    In Tick (timeouts (occ_gst (hd ex)) h).
Proof.
  eauto using live_node_has_Tick_in_timeouts'.
Qed.
