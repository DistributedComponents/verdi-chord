Admits are grouped by file and by a rough priority measure.

1. The "useless" heading means the lemma is never used in the phase *n*
   arguments or is only used in proofs of facts that are themselves useless.

2. The "straightforward" heading means that the admitted fact is likely provable
   using a straightforward inductive argument and crank-turning. It doesn't mean
   the right spec lemmas already exist to do that crank turning.

3. The "some intervention" heading means that the lemma might be a consequence
   of a larger invariant or requires being broken down into smaller admits
   before it's straightforward to prove.

4. The "complicated" heading means it's my problem and needs a lot of new lemmas
   or reformulation of definitions before it's provable.

# ChordCorrectPhaseOne: 2 admits

## some intervention

- phase_one_error_continuously_nonincreasing

## straightforward

- open_stabilize_request_until_timeout

# ChordCorrectPhaseTwo: 34 admits

## complicated

- better_pred_eventually_improves_succ
- open_stabilize_request_until_response
- merge_points_preserved_until_error_drops
- incoming_GotPredAndSuccs_with_a_after_p_causes_improvement
- error_decreases_when_succs_right

## some intervention

- phase_two_zero_error_locally_correct
- joins_stop
- pred_error_nonincreasing
- first_succ_error_nonincreasing
- notify_when_pred_None_eventually_improves
- notify_when_pred_dead_eventually_improves
- notify_when_pred_worse_eventually_improves
- pred_bound_pred_not_worse
- open_request_with_response_on_wire_closed_or_preserved
- succ_error_means_merge_point

## straightforward

- length_filter_by_cmp_same_eq
- live_successor_changed_improves
- pred_changing_suffices
- pred_same_until_improvement
- first_succ_same_until_improvement
- successors_are_live_nodes
- live_nodes_not_clients
- correct_pred_exists
- correct_pred_unique
- correct_first_succ_unique
- first_succs_correct_succ_right
- error_means_merge_point_or_wrong_pred

## useless

- pred_between_improves_error
- succ_between_improves_error
- pred_error_bound
- first_succ_error_bound
- notify_causes_rectify
- rectify_with_live_pred_sets_pred
- a_before_pred_merge_point_with_stabilize_request

# ChordCorrectPhaseThree: 1 admit

## complicated

- phase_three


# LabeledLemmas: 18 admits

## complicated / some intervention

- Tick_eventually_enabled
- dead_node_channel_empties_out
- timeout_constraint_lifted_by_clearing
- queries_are_closed_by_recvmsg_occ
- inv_responses_are_unique
- inv_Request_payload_has_response
- now_recvmsg_now_clears_timeout
- Request_implies_open_request_to
- requests_eventually_get_responses

## straightforward

- RecvMsg_enabled_until_occurred
- recv_handler_never_clears_RectifyTick
- constrained_Request_not_cleared_by_recv_handler
- request_constraint_prevents_recv_adding_msgs
- clients_not_in_failed
- other_timeouts_not_cleared
- channel_stays_empty
- request_stays_in
- msgs_remain_after_timeout

# SystemLemmas: 2 admits

## straightforward

- nodes_have_state
- adding_nodes_did_not_affect_best_succ

# SystemPointers: 9 admits

## complicated / some intervention

- valid_ptrs_global_timeouts
- valid_ptrs_global_net
- valid_ptrs_global_trace
- valid_ptrs_state_nodes_subset
- start_handler_valid_ptrs_state

## straightforward

- valid_ptrs_global_timeout_handler
- valid_ptrs_global_recv_handler
- apply_handler_result_In_timeouts
- valid_ptrs_global_sigma

# SystemReachable: 3 admits

## complicated / some intervention

- queries_always_remote

## useless

- query_state_net_invariant_inductive

# Chord: 1 admit

## straightforward

- ext_succ_list_span_includes
