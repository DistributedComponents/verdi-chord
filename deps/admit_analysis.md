```diff
% diff -u stabilization_admits.txt all_used_admits.txt 
--- stabilization_admits.txt	2018-01-25 15:45:04.395871563 -0500
+++ all_used_admits.txt	2018-01-25 15:45:09.109204864 -0500
@@ -1,7 +1,8 @@
 adopting_succs_decreases_succs_error
 at_most_one_request_timeout_invariant
+best_pred_is_best_first_succ
+better_pred_bool_total'
 better_pred_eventually_improves_succ
-Classical_Prop:classic
 constrained_Request_not_cleared_by_recv_handler
 dead_node_channel_empties_out
 dead_nodes_go_quiet
@@ -16,9 +17,11 @@
 initial_esl_is_sorted_nodes_chopped
 join2_target_joined
 joins_stop
+length_filter_by_cmp_same_eq
 live_node_in_succs_best_succ
 merge_points_preserved_until_error_drops
 notify_when_pred_None_eventually_improves
+notify_when_pred_worse_eventually_improves
 not_skipped_means_incoming_succs_not_skipped
 open_stabilize_request_until_response
 phase_one_error_continuously_nonincreasing
 ```

 This means that the following lemmas are used in other proofs but aren't
 connected to the top-level theorem:
 - `best_pred_is_best_first_succ`
 - `better_pred_bool_total'`
 - `notify_when_pred_worse_eventually_improves`
 - `length_filter_by_cmp_same_eq`
