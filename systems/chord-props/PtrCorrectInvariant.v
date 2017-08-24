Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.

Set Bullet Behavior "Strict Subproofs".


Lemma sigma_apply_handler_result_same :
  forall h res es gst,
    sigma (apply_handler_result h res es gst) h =
    Some (fst (fst (fst res))).
Proof.
  intros. unfold apply_handler_result.
  repeat break_match. subst. simpl.
  now rewrite_update.
Qed.

Lemma sigma_apply_handler_result_diff :
  forall h h' res es gst,
    h <> h' ->
    sigma (apply_handler_result h res es gst) h' =
    sigma gst h'.
Proof.
  intros. unfold apply_handler_result.
  repeat break_match. subst. simpl.
  now rewrite_update.
Qed.

Lemma initial_nodes_ptr_correct:
  forall l h init,
    sigma (fold_left run_init_for l init) h = sigma (run_init_for init h) h \/
    sigma (fold_left run_init_for l init) h = sigma init h.
Proof.
  induction l; intros; simpl in *; auto.
  specialize (IHl h (run_init_for init a)).
  intuition.
  - repeat find_rewrite.
    unfold run_init_for.
    repeat rewrite sigma_apply_handler_result_same. auto.
  - repeat find_rewrite. unfold run_init_for.
    destruct (addr_eq_dec a h); subst.
    + repeat rewrite sigma_apply_handler_result_same. auto.
    + rewrite sigma_apply_handler_result_diff; auto.
Qed.

Lemma initial_nodes_ptr_correct_Some :
  forall (h : addr) (st : data) l init,
    sigma (fold_left run_init_for l init) h = Some st ->
    sigma init h = None ->
    Some st = sigma (run_init_for init h) h.
Proof.
  intros.
  pose proof (initial_nodes_ptr_correct l h init).
  intuition congruence.
Qed.

Lemma do_delayed_queries_ptr :
  forall h st st' ms ts cts,
    do_delayed_queries h st = (st', ms, ts, cts) ->
    ptr st' = ptr st.
Proof.
  intros.
  unfold do_delayed_queries, clear_delayed_queries in *.
  break_match; find_inversion; auto.
Qed.

Ltac simpler := repeat (repeat find_inversion; subst; simpl in *); auto.
Lemma handle_msg_ptr :
  forall h h' st m st' ms ts cts,
    handle_msg h h' st m = (st', ms, ts, cts) ->
    ptr st' = ptr st.
Proof.
  intros.
  unfold handle_msg in *.
  repeat (break_match; simpler);
    unfold handle_query_res in *; repeat (break_match; simpler);
    unfold handle_query_req_busy in *; repeat (break_match; simpler);
    unfold handle_stabilize in *; repeat (break_match; simpler);
    unfold schedule_rectify_with in *; repeat (break_match; simpler);
    unfold end_query in *; repeat (break_match; simpler);
    unfold handle_rectify in *; repeat (break_match; simpler);
    unfold start_query in *; repeat (break_match; simpler).
Qed.

(*
This is a very good and easy invariant.  At a node h, ptr st is a copy
of a pointer to h. It's set when the node starts up and never changed
anywhere.

USED: In phase two.
*)
Lemma ptr_correct :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    ptr st = make_pointer h.
Proof.
  intros. induct_reachable_st.
  - intros.
    unfold initial_st in *.
    find_apply_lem_hyp initial_nodes_ptr_correct_Some; simpl in *; auto.
    unfold run_init_for in *. simpl in *.
    repeat break_match. subst. simpl in *.
    rewrite_update. find_inversion.
    unfold start_handler in *. repeat break_match.
    + unfold empty_start_res in *.
      find_inversion. auto.
    + unfold start_query in *.
      repeat break_match; subst; simpl in *;
        find_inversion; auto.
    + find_inversion. auto.
  - intros. invcs H0; auto.
    + update_destruct; subst; rewrite_update; auto.
      now find_inversion.
    + update_destruct; subst; rewrite_update; auto.
      find_inversion.
      unfold timeout_handler, timeout_handler_eff in *.
      break_match.
      * unfold tick_handler in *. break_match; simpl in *; try solve_by_inversion.
        break_if; simpl in *; try solve_by_inversion.
        unfold add_tick, start_query in *.
        repeat break_let.
        subst. find_inversion.
        break_match; simpl in *; try solve_by_inversion.
        repeat break_let. find_inversion. simpl. auto.
      * unfold do_rectify in *. simpl in *.
        break_match; simpl in *; try solve_by_inversion.
        break_match; simpl in *; try solve_by_inversion.
        break_match; simpl in *; try solve_by_inversion.
        unfold start_query in *;
          repeat break_match; simpl in *; find_inversion; simpl; auto.
      * simpl in *. find_inversion. auto.
      * unfold request_timeout_handler in *.
        repeat break_match; simpl in *; try solve_by_inversion.
        subst. unfold handle_query_timeout in *.
        repeat break_match; simpl in *; try find_inversion; simpl in *; auto.
        unfold start_query in *.
        repeat break_match; try find_inversion; simpl in *; auto.
    + update_destruct; subst; rewrite_update; auto.
      find_inversion.
      unfold recv_handler in *. repeat break_let. find_inversion.
      find_apply_lem_hyp do_delayed_queries_ptr.
      repeat find_rewrite.
      find_apply_lem_hyp handle_msg_ptr.
      repeat find_rewrite. auto.
Qed.
