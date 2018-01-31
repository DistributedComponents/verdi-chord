I've admitted the top level phase two theorem and commented the rest of the file
out. This leaves 28 admits.

Out of those 28, we won't try to prove
(1 admit) The phase two admit
- `phase_two_without_phase_one`

(4 admits) facts about pointers never getting worse.
- `phase_one_error_continuously_nonincreasing`
- `succs_error_nonincreasing`
- `succs_error_helper_invar`
- `has_first_succ_stable`

(7 admits) facts about pointers pointing to live and/or joined nodes
- `valid_ptrs_global_inductive`
- `wf_ptr_succ_list_invariant'`
- `successors_are_live_nodes`
- `stabilize2_target_joined`
- `join2_target_joined`
- `stabilize_target_joined`
- `successor_nodes_always_valid`

(1 'admit') An axiom saying SUCC_LIST_LEN >= 2
- `succ_list_len_lower_bound`

This leaves the following 15 admits, which I think are provable in two months'
worth of work.

2 tricky facts
- `open_stabilize_request_until_response`
- `not_skipped_means_incoming_succs_not_skipped`

5 things of a list lemma flavor
- `in_concat`
- `initial_esl_is_sorted_nodes_chopped`
- `sorted_list_elements_not_between`
- `live_node_in_succs_best_succ`
- `has_succ_has_pred_inv`

2 grab bag
- `adopting_succs_decreases_succs_error`
- `constrained_Request_not_cleared_by_recv_handler`

2 grindy invariants
- `query_message_ok_invariant`
- `at_most_one_request_timeout_invariant`

4 eventually... arguments
- `joins_stop`
- `queries_eventually_stop`
- `dead_node_channel_empties_out`
- `dead_nodes_go_quiet`
