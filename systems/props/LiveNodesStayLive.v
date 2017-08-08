Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Verdi.DynamicNet.

Require Import Chord.Chord.

Ltac live_node_invariant_finish_goal :=
  unfold live_node in *; simpl in *; intuition;
  update_destruct; subst; rewrite_update; eauto;
  break_exists; repeat find_inversion; eexists; intuition; eauto; simpl in *; congruence.

Lemma live_node_invariant :
  forall gst l gst' h,
    labeled_step_dynamic gst l gst' ->
    live_node gst h ->
    live_node gst' h.
Proof.
  intros.
  match goal with
  | H : labeled_step_dynamic _ _ _ |- _ =>
    inv H
  end.
  - unfold timeout_handler_l, timeout_handler_eff,
    tick_handler, keepalive_handler, do_rectify, request_timeout_handler,
    add_tick, handle_query_timeout, clear_query, end_query, start_query,
    update_query, update_succ_list in *.
    repeat break_match; live_node_invariant_finish_goal.
  - repeat unfold recv_handler_l, recv_handler,
    handle_msg, do_delayed_queries,
    clear_delayed_queries, tick_handler, keepalive_handler, do_rectify, request_timeout_handler,
    handle_rectify, handle_query_req,
    handle_query_req_busy, handle_query_res, start_query,
    schedule_rectify_with,
    handle_stabilize,
    add_tick,
    update_query, update_succ_list,
    end_query, clear_query
      in *. repeat break_match; live_node_invariant_finish_goal.
  - live_node_invariant_finish_goal.
  - live_node_invariant_finish_goal.
Qed.
