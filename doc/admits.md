# ChordCorrectPhaseOne: 2 admits
- open_stabilize_request_until_timeout
* phase_one_error_continuously_nonincreasing

# ChordCorrectPhaseTwo: 34 admits
- length_filter_by_cmp_same_eq
? pred_between_improves_error
? succ_between_improves_error
* phase_two_zero_error_locally_correct
* joins_stop
* pred_error_nonincreasing
* first_succ_error_nonincreasing
? pred_error_bound
? first_succ_error_bound
* notify_when_pred_None_eventually_improves
* notify_when_pred_dead_eventually_improves
* notify_when_pred_worse_eventually_improves
? notify_causes_rectify
? rectify_with_live_pred_sets_pred
** better_pred_eventually_improves_succ
** open_stabilize_request_until_response
- live_successor_changed_improves
- pred_changing_suffices
- pred_same_until_improvement
- first_succ_same_until_improvement
? a_before_pred_merge_point_with_stabilize_request
* pred_bound_pred_not_worse
- successors_are_live_nodes
- live_nodes_not_clients
** merge_points_preserved_until_error_drops
* open_request_with_response_on_wire_closed_or_preserved
** incoming_GotPredAndSuccs_with_a_after_p_causes_improvement
* succ_error_means_merge_point
- correct_pred_exists
- correct_pred_unique
- correct_first_succ_unique
- first_succs_correct_succ_right
** error_decreases_when_succs_right
- error_means_merge_point_or_wrong_pred

# LabeledLemmas: 18 admits
- RecvMsg_enabled_until_occurred
- recv_handler_never_clears_RectifyTick
- constrained_Request_not_cleared_by_recv_handler
- request_constraint_prevents_recv_adding_msgs
* Tick_eventually_enabled
- clients_not_in_failed
- other_timeouts_not_cleared
- channel_stays_empty
* dead_node_channel_empties_out
- request_stays_in
- msgs_remain_after_timeout
* timeout_constraint_lifted_by_clearing
* queries_are_closed_by_recvmsg_occ
* inv_responses_are_unique
* inv_Request_payload_has_response
* now_recvmsg_now_clears_timeout
* Request_implies_open_request_to
* requests_eventually_get_responses

# SystemLemmas: 2 admits
- nodes_have_state
- adding_nodes_did_not_affect_best_succ

# SystemPointers: 9 admits
- valid_ptrs_global_timeout_handler
- valid_ptrs_global_recv_handler
- apply_handler_result_In_timeouts
* valid_ptrs_global_timeouts
- valid_ptrs_global_sigma
* valid_ptrs_global_net
* valid_ptrs_global_trace
* valid_ptrs_state_nodes_subset
* start_handler_valid_ptrs_state

# SystemReachable: 3 admits
* queries_always_remote
query_state_net_invariant_inductive

# Chord: 1 admit
- ext_succ_list_span_includes

# ChordCorrectPhaseThree: 1 admit
** phase_three

categories (topic)
1. when pointers change, they improve
   a) preds
   b) first succs
   c) other succs
2. changing one thing suffices to improve merge point
3. how first

categories (difficulty)
1. needs a more general invariant
2. needs to be reduced to safety properties
3. needs some ltl facts about sub-operations
4. easily proven by induction or by using existing facts
