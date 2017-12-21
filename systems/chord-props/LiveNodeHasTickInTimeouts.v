Require Import List.
Import ListNotations.

Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Update.
Require Import StructTact.Util.

Require Import InfSeqExt.infseq.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.
Require Import Chord.HandlerLemmas.

Set Bullet Behavior "Strict Subproofs".

Lemma live_node_fail_node :
  forall h h' gst,
    live_node (fail_node gst h) h' ->
    live_node gst h'.
Proof.
  intros.
  unfold live_node in *. simpl in *.
  intuition.
Qed.

Ltac simpler := repeat (repeat find_inversion; subst; simpl in *; repeat rewrite_update); auto.

Lemma do_delayed_queries_never_clears_tick :
  forall (h : addr) (st st' : data) (ms : list (addr * payload))
    (nts cts : list timeout),
    do_delayed_queries h st = (st', ms, nts, cts) ->
    ~ In Tick cts.
Proof.
  intros.
  unfold do_delayed_queries in *.
  break_match; simpl in *; subst; find_inversion; simpl in *; intuition; congruence.
Qed.

Lemma tick_not_in_timeouts_in :
  forall st,
    ~ In Tick (timeouts_in st).
Proof.
  intros.
  unfold timeouts_in.
  repeat break_match; in_crush.
  discriminate.
Qed.

Lemma handle_msg_never_clears_tick :
  forall (h h' : addr) (st st' : data) m (ms : list (addr * payload))
    (nts cts : list timeout),
    handle_msg h h' st m = (st', ms, nts, cts) ->
    ~ In Tick cts.
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
    unfold start_query in *; repeat (break_match; simpler);
      eauto using tick_not_in_timeouts_in;
      in_crush; eauto using tick_not_in_timeouts_in; try discriminate;
        eapply tick_not_in_timeouts_in; eauto.
Qed.

Lemma handle_msg_adds_tick_when_setting_joined :
  forall (h h' : addr) (st st' : data) m (ms : list (addr * payload))
    (nts cts : list timeout),
    joined st = false ->
    joined st' = true ->
    handle_msg h h' st m = (st', ms, nts, cts) ->
    In Tick nts.
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
    unfold start_query in *; repeat (break_match; simpler); congruence.
Qed.

Lemma live_node_has_Tick_in_timeouts' :
  forall gst h,
    reachable_st gst ->
    live_node gst h ->
    In Tick (timeouts gst h).
Proof.
  intros. induct_reachable_st; intros.
  - unfold live_node in *.
    rewrite Tick_in_initial_st; eauto with datatypes.
  - inv_prop step_dynamic.
    + subst. simpl in *.
      unfold live_node in *. simpl in *.
      intuition.
      * subst. exfalso. rewrite_update.
        break_exists. intuition.
        solve_by_inversion.
      * assert (h <> h0) by
            (intro;
             subst; rewrite_update;
             break_exists; intuition; solve_by_inversion).
        repeat rewrite_update. auto.
    + subst. simpl in *. eauto using live_node_fail_node.
    + subst. simpl in *.
      update_destruct; subst;
        unfold live_node in *; simpl in *; repeat rewrite_update; auto.
      intuition. break_exists. intuition. find_inversion.
      assert (joined st = true -> In Tick (timeouts gst h)) by
          (intros; apply IHreachable_st; intuition; eauto).
      unfold timeout_handler, timeout_handler_eff in *.
      break_match.
      * unfold tick_handler in *.
        repeat (break_match; simpler).
        concludes.
        unfold add_tick in *. repeat break_let.
        subst. find_inversion. in_crush.
      * unfold do_rectify in *.
        unfold start_query in *.
        repeat (break_match; simpler);
          try solve [apply remove_preserve; simpler; congruence].
        right.
        rewrite timeouts_in_None; auto.
        apply remove_preserve; simpler; congruence.
      * unfold keepalive_handler in *. simpl in *.
        find_inversion. simpl in *.
        right. apply remove_preserve; simpler; congruence.
      * unfold request_timeout_handler in *.
        repeat (break_match; simpler);
          try solve [apply remove_preserve; simpler; congruence].
        unfold handle_query_timeout in *.
        in_crush. right.
        unfold start_query in *.
        repeat (break_match; simpler);
          try solve [apply remove_preserve; simpler; congruence];
          apply in_remove_all_preserve;
          try solve [match goal with
          | |- ~ In _ _ =>
            unfold timeouts_in; repeat break_match; in_crush; congruence
                     end];
          try solve [apply remove_preserve; simpler; congruence].
    + subst. simpl in *.
      update_destruct; subst;
        unfold live_node in *; simpl in *; repeat rewrite_update; auto.
      intuition. break_exists. intuition. find_inversion.
      assert (joined d = true -> In Tick (timeouts gst (fst (snd m)))) by
          (intros; apply IHreachable_st; intuition; eauto).
      unfold recv_handler in *. repeat break_let.
      find_copy_apply_lem_hyp do_delayed_queries_never_clears_tick.
      repeat find_inversion. in_crush.
      match goal with
      | |- In Tick (?new_do_delayed
                    ++ remove_all ?dec ?cleared_do_delayed ?new_handle_msg)
          \/ In Tick (remove_all _ (?cleared_handle_msg ++ ?cleared_do_delayed) ?old) =>
        cut (In Tick new_handle_msg \/ In Tick (remove_all dec cleared_handle_msg old))
      end.
      { intros. intuition.
        - left. in_crush. right.
          eauto using in_remove_all_preserve.
        - right. rewrite remove_all_app_l.
          rewrite remove_all_del_comm.
          eauto using in_remove_all_preserve.
      }
      find_copy_apply_lem_hyp handle_msg_never_clears_tick.
      match goal with
      | H : context [joined] |- _ =>
        erewrite <- HandlerLemmas.joined_preserved_by_do_delayed_queries in H by eauto
      end.
      destruct (joined d) eqn:?; auto.
      * concludes. eauto using in_remove_all_preserve.
      * left.
        eauto using handle_msg_adds_tick_when_setting_joined.
    + subst. simpl in *. auto.
    + subst. simpl in *. auto.
Qed.

(*
New nodes have no Tick.
A node with no Tick sets joined = true iff it also registers a Tick.
Having a Tick is preserved by the step.
USED: In phase one.
*)

Lemma live_node_has_Tick_in_timeouts :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    live_node (occ_gst (hd ex)) h ->
    In Tick (timeouts (occ_gst (hd ex)) h).
Proof.
  eauto using live_node_has_Tick_in_timeouts'.
Qed.
