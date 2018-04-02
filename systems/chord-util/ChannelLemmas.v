Require Import List.
Import ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Set Bullet Behavior "Strict Subproofs".

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.

Require Import Verdi.DynamicNet.

Require Import Chord.InfSeqTactics.

Require Import Chord.Chord.

Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.

Require Import Chord.LiveNodesStayLive.
Require Import Chord.NodesHaveState.
Require Import Chord.QueryInvariant.
Require Import Chord.TimeoutMeansActive.
Require Import Chord.ValidPointersInvariant.
Require Import Chord.LabeledLemmas.
Require Import Chord.LabeledMeasures.


Lemma channel_stays_empty' :
  forall gst gst' src dst,
    (forall p, In (src, (dst, p)) (msgs gst') -> In (src, (dst, p)) (msgs gst)) ->
    channel gst src dst = [] ->
    channel gst' src dst = [].
Proof.
  intros.
  destruct (channel gst' src dst) eqn:?; auto.
  exfalso.
  assert (In p (channel gst' src dst)) by (find_rewrite; intuition).
  find_apply_lem_hyp in_channel_in_msgs. find_apply_hyp_hyp.
  find_apply_lem_hyp in_msgs_in_channel. repeat find_rewrite. solve_by_inversion.
Qed.

Lemma channel_stays_empty :
  forall ex src dst,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    In src (failed_nodes (occ_gst (hd ex))) ->
    channel (occ_gst (hd ex)) src dst = [] ->
    channel (occ_gst (hd (tl ex))) src dst = [].
Proof.
  intros. destruct ex. simpl in *.
  inv_prop lb_execution.
  inv_prop labeled_step_dynamic; simpl in *; repeat find_rewrite.
  - destruct (addr_eq_dec h src); subst; try congruence.
    eapply channel_stays_empty'; [|eauto]; simpl in *.
    intros. in_crush. destruct x. find_rewrite_lem send_definition.
    congruence.
  - destruct (addr_eq_dec (fst (snd m)) src); subst; try congruence.
    eapply channel_stays_empty'; [|eauto]; simpl in *.
    intros. repeat find_rewrite. in_crush.
    destruct x. find_rewrite_lem send_definition.
    congruence.
  - find_eapply_lem_hyp clients_not_in_failed; eauto.
    intuition. destruct (addr_eq_dec h src); subst; intuition.
    eapply channel_stays_empty'; [|eauto]; simpl in *.
    intros. intuition.
    find_rewrite_lem send_definition.
    congruence.
  - eapply channel_stays_empty'; [|eauto]; simpl in *.
    intros. find_rewrite. in_crush.
(*
USED: In phase one (transitively)
DIFFICULTY: 1
*)
Qed.

Lemma open_request_until_timeout :
  forall h dst req ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->

    channel (occ_gst (hd ex)) dst h = [] ->
    In h (active_nodes (occ_gst (hd ex))) ->
    In dst (failed_nodes (occ_gst (hd ex))) ->
    open_request_to (occ_gst (hd ex)) h dst req ->

    weak_until (now (fun occ => open_request_to (occ_gst occ) h dst req))
               (now (occurred (Timeout h (Request dst req) DetectFailure)))
               ex.
Proof.
  intros h dst req.
  cofix c.
  destruct ex.
  intros.
  inv_prop lb_execution.
  find_copy_eapply_lem_hyp open_request_to_dead_node_preserved_or_times_out;
    (* eauto will grab the coinduction hypothesis if we don't do something like this *)
    match goal with
    | |- weak_until _ _ _ => idtac
    | _ => eauto using in_active_in_nodes, in_active_not_failed
    end.
  break_or_hyp.
  - apply W_tl; [assumption|].
    apply c;
      invar_eauto;
      eauto using active_nodes_invar, failed_nodes_never_removed, channel_stays_empty.
  - now apply W0.
Qed.

Definition channel_measure from to gst :=
  length (channel gst from to).

Lemma channel_measure_nonincreasing :
  forall ex dead h,
    lb_execution ex ->
    In dead (failed_nodes (occ_gst (hd ex))) ->
    always (consecutive (measure_nonincreasing (channel_measure dead h))) ex.
Admitted.

Lemma dead_node_channel_empties_out :
  forall ex dead h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    live_node (occ_gst (hd ex)) h ->
    In dead (failed_nodes (occ_gst (hd ex))) ->
    weak_local_fairness ex ->
    continuously (now (fun occ => channel (occ_gst occ) dead h = [])) ex.
Proof.
(*
USED: In phase one (transitively)
DIFFICULTY: 3/Doug
*)
Admitted.

Lemma live_node_in_active :
  forall h gst,
    live_node gst h ->
    In h (active_nodes gst).
Proof.
  intros.
  inv_prop live_node; expand_def.
  eapply in_nodes_not_failed_in_active; auto.
Qed.

Lemma request_eventually_fires :
  forall h dst req ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->

    live_node (occ_gst (hd ex)) h ->
    In dst (failed_nodes (occ_gst (hd ex))) ->
    open_request_to (occ_gst (hd ex)) h dst req ->
    channel (occ_gst (hd ex)) dst h = [] ->

    eventually (now (occurred (Timeout h (Request dst req) DetectFailure))) ex.
Proof.
  intros.
  find_apply_lem_hyp open_request_until_timeout; auto using live_node_in_active.
  find_apply_lem_hyp weak_until_until_or_always.
  break_or_hyp; [eauto using until_eventually|].
  find_copy_apply_lem_hyp (dead_node_channel_empties_out ex dst h); auto.
  find_apply_lem_hyp always_continuously.
  destruct ex. apply always_now.
  match goal with
  | H : weak_local_fairness _ |- _ => apply H
  end.
  assert (continuously
            (now (fun occ => open_request_to (occ_gst occ) h dst req) /\_
             now (fun occ => channel (occ_gst occ) dst h = []) /\_
             (fun ex => lb_execution ex /\
                     now (fun occ => live_node (occ_gst occ) h /\
                                  In dst (failed_nodes (occ_gst occ))) ex))
            (Cons o ex)).
  {
    apply continuously_and_tl; auto.
    apply continuously_and_tl; auto.
    apply E0.
    apply always_inv; [|firstorder].
    intros.
    split; break_and; eauto using lb_execution_invar.
    destruct s.
    inv_prop lb_execution; simpl in *; break_and.
    split.
    - eapply live_node_invariant; eauto.
    - eapply failed_nodes_never_removed; eauto.
  }
  eapply continuously_monotonic; [|eauto].
  intros.
  destruct s.
  do 2 invcs_prop and_tl.
  repeat break_and.
  inv_prop live_node; expand_def.
  eapply Timeout_enabled_when_open_request_to_dead_node; eauto.
  intros.
  rewrite channel_contents.
  find_rewrite.
  tauto.
Qed.

Lemma reachable_st_lb_execution_cons :
  forall o o' ex,
    lb_execution (Cons o (Cons o' ex)) ->
    reachable_st (occ_gst o) ->
    reachable_st (occ_gst o').
Proof using.
  intros.
  inv_lb_execution.
  eauto using reachableStep, labeled_step_is_unlabeled_step.
Qed.

Lemma reachable_st_always :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    always ((fun ex' => reachable_st (occ_gst (hd ex'))) /\_ lb_execution) ex.
Proof.
  intros.
  eapply always_inv.
  - intros.
    destruct s.
    inv_prop and_tl.
    split;
      eauto using lb_execution_invar, reachable_st_lb_execution_cons.
  - firstorder.
Qed.

Lemma sent_message_means_in_nodes_or_client :
  forall gst src dst p,
    reachable_st gst ->
    In (src, (dst, p)) (msgs gst) ->
    In src (nodes gst) \/ client_payload p /\ client_addr src.
Proof.
  intros.
  generalize dependent p.
  generalize dependent dst.
  generalize dependent src.
  pattern gst.
  apply chord_net_invariant; do 2 autounfold; simpl; intros;
    repeat find_rewrite; intuition eauto;
      try solve [
            find_apply_lem_hyp in_app_or; break_or_hyp;
            [find_apply_lem_hyp in_map_iff; expand_def; unfold send in *; find_injection; in_crush
            |in_crush; eauto with datatypes]
          ].
  - inv_prop initial_st; break_and.
    repeat find_rewrite.
    in_crush.
  - in_crush; eauto.
    + unfold send in *.
      find_injection; tauto.
    + find_apply_hyp_hyp; tauto.
  - unfold send in *.
    simpl in *.
    break_or_hyp.
    + find_injection; tauto.
    + find_apply_hyp_hyp; tauto.
  - simpl in *.
    assert (In (src, (dst, p)) (xs ++ m :: ys)) by in_crush.
    find_apply_hyp_hyp; tauto.
Qed.

(*TODO move to wherever response_payload is defined *)
Definition response_payload_dec :
  forall p,
    {response_payload p} + {~ response_payload p}.
Proof.
  destruct p;
    solve [left; constructor
          |right; intro; inv_prop response_payload].
Defined.
Lemma req_res_pair_response_payload :
  forall req res,
    request_response_pair req res ->
    response_payload res.
Proof.
  intros.
  inv_prop request_response_pair; constructor.
Qed.
Hint Resolve req_res_pair_response_payload.

Lemma open_request_with_response_on_wire_closed_or_preserved :
  forall gst l gst' src dst req res,
    reachable_st gst ->
    In src (nodes gst) ->
    labeled_step_dynamic gst l gst' ->
    open_request_to gst src dst req ->
    request_response_pair req res ->
    In res (channel gst dst src) ->
    RecvMsg dst src res = l \/
    open_request_to gst' src dst req /\
    In res (channel gst' dst src).
Proof.
(*
If there's a response to a request on the wire, we'll either recieve the
response or the situation will stay the same.

This still needs some set-up to be proved easily since it relies on the
assumption that there's only ever one request.

DIFFICULTY: Ryan.
USED: In phase two.
 *)
  intros.
  assert (exists st__src, sigma gst src = Some st__src)
    by eauto.
  break_exists_name st__src.
  assert (exists st__src, sigma gst' src = Some st__src)
    by eauto with invar.
  break_exists_name st__src'.
  assert (~ client_payload res0)
    by (intro; inv_prop client_payload; inv_prop request_response_pair).
  assert (In dst (nodes gst))
    by eauto.
  assert (exists st__dst, sigma gst dst = Some st__dst)
    by eauto.
  break_exists_name st__dst.
  assert (exists st__dst, sigma gst' dst = Some st__dst)
    by eauto with invar.
  break_exists_name st__dst'.
  assert (query_message_ok src dst (cur_request st__src) (delayed_queries st__dst)
                           (channel gst src dst) (channel gst dst src)).
    by (eapply query_message_ok_invariant; eauto).
  assert (query_message_ok src dst (cur_request st__src') (delayed_queries st__dst')
                           (channel gst' src dst) (channel gst' dst src))
    by (eapply query_message_ok_invariant; eauto with invar).
  inv_prop open_request_to; expand_def.
  assert (cur_request_timeouts_ok' (cur_request st__src) (timeouts gst src))
    by eauto.
  assert (cur_request_timeouts_ok' (cur_request st__src') (timeouts gst' src)).
  {
    eapply cur_request_timeouts_ok'_complete.
    eapply cur_request_timeouts_related_invariant; eauto with invar.
  }

  inv_prop labeled_step_dynamic.
  - handler_def.
    handler_def.
    + right; simpl in *.
      update_destruct; subst; rewrite_update; simpl; auto.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto;
             repeat (handler_def || handler_simpl);
             eauto using remove_preserve.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
    + right; simpl in *.
      update_destruct; subst; rewrite_update; simpl; auto.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto;
             repeat (handler_def || handler_simpl);
             eauto using remove_preserve.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
    + right; simpl in *.
      update_destruct; subst; rewrite_update; simpl; auto.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto;
             repeat (handler_def || handler_simpl);
             eauto using remove_preserve.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
    + right; simpl in *.
      update_destruct; subst; rewrite_update; simpl; auto.
      * match goal with
           | H : In (Request ?x1 ?y1) _, H' : In (Request ?x2 ?y2) _ |- _ =>
             assert (Request x1 y1 = Request x2 y2) by
                 eauto using at_most_one_request_timeout_uniqueness,
                 at_most_one_request_timeout_invariant
        end. find_inversion.
        exfalso.
        inv_prop timeout_constraint.
        find_apply_lem_hyp in_channel_in_msgs.
        intuition. eauto.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
  - handler_def.
    destruct m as [m__src [m__dst p]].
    simpl (fst _) in *; simpl (snd _) in *.
    assert (In (m__src, (m__dst, p)) (msgs gst))
      by (repeat find_rewrite; in_crush).
    assert (m__src <> (addr_of x1) /\ client_addr m__src /\ client_payload p \/ exists stm, sigma gst m__src = Some stm).
    {
      find_eapply_lem_hyp sent_message_means_in_nodes_or_client; eauto.
      break_or_hyp.
      right; eauto.
      left.
      break_and.
      split; auto.
      intro; subst.
      find_eapply_lem_hyp clients_not_in_failed; eauto.
      break_and; eauto.
    }
    break_or_hyp; break_and.
    {
      right; split.
      - eapply open_request_to_intro; eauto.
        + repeat find_rewrite; find_injection.
          simpl; update_destruct; rewrite_update; eauto.
          subst.
          repeat find_rewrite; find_injection.
          find_eapply_lem_hyp (recv_msg_not_right_response_never_removes_request_timeout m__src src); eauto.
          break_or_hyp; try now in_crush.
          apply in_or_app; right; eauto using in_remove_all_preserve.
          intro; inv_prop client_payload; inv_prop query_response.
        + repeat find_rewrite; find_injection.
          simpl in *.
          destruct (addr_eq_dec m__dst src).
          * repeat rewrite_update.
            find_injection.
            repeat find_rewrite; find_injection.
            find_eapply_lem_hyp recv_msg_not_right_response_preserves_cur_request; eauto.
            congruence.
            intro; inv_prop query_response; inv_prop client_payload.
          * repeat rewrite_update.
            congruence.
      - repeat find_apply_lem_hyp in_channel_in_msgs.
        apply in_msgs_in_channel.
        simpl.
        repeat find_rewrite; in_crush;
          find_injection; tauto.
    }
    break_exists_name stm.
    assert (query_message_ok src m__src (cur_request st__src) (delayed_queries stm)
                             (channel gst src m__src) (channel gst m__src src))
      by (eapply query_message_ok_invariant; eauto).
    destruct (addr_eq_dec m__dst src); repeat find_rewrite.
    + subst.
      find_injection.
      inv H11; repeat find_rewrite; find_injection;
        try congruence;
        try (exfalso; eapply_prop no_responses; eauto).
      repeat find_rewrite; find_injection.
      assert (res1 = res0); subst.
      {
        repeat find_apply_lem_hyp in_split; break_exists.
        assert (no_responses (x0 ++ x2)) by eauto.
        assert (~ In res0 x0).
          by (intro; eapply_prop no_responses; [in_crush|]; eauto).
        assert (~ In res0 x2).
          by (intro; eapply_prop no_responses; [in_crush|]; eauto).
        assert (In res0 (x11 ++ res0 :: x12)) by in_crush.
        repeat find_rewrite.
        in_crush.
      }
      destruct (response_payload_dec p).
      * inv_prop query_message_ok;
          try solve [exfalso; eapply_prop no_responses; eauto;
                     eapply in_msgs_in_channel; find_rewrite; in_crush].
        repeat find_rewrite; find_injection.
        assert (res0 = p).
        {
          assert (In p (channel gst (addr_of x1) src))
            by (eapply in_msgs_in_channel; find_rewrite; in_crush).
          repeat find_apply_lem_hyp in_split; break_exists.
          repeat find_rewrite.
          assert (no_responses (x5 ++ x6)) by eauto.
          assert (~ In p x5)
            by (intro; eapply_prop no_responses; [in_crush|]; eauto).
          assert (~ In p x6)
            by (intro; eapply_prop no_responses; [in_crush|]; eauto).
          assert (In p (x0 ++ p :: x2)) by in_crush.
          assert (In p (x5 ++ res0 :: x6)) by congruence.
          in_crush.
        }
        subst; left; auto.
      * assert (p <> res0) by (intro; subst; eauto).
        right; split.
        -- assert (~ query_response x p).
           {
             intro; find_eapply_prop response_payload.
             inv_prop query_response; constructor.
           }
           find_copy_eapply_lem_hyp recv_msg_not_right_response_never_removes_request_timeout; eauto.
           eapply open_request_to_intro; try erewrite sigma_ahr_updates; simpl; eauto.
           rewrite_update.
           break_or_hyp; try now in_crush.
           apply in_or_app; right; eauto using in_remove_all_preserve.
           find_copy_eapply_lem_hyp recv_msg_not_right_response_preserves_cur_request; eauto.
           congruence.
        -- apply in_msgs_in_channel; repeat find_apply_lem_hyp in_channel_in_msgs.
           apply in_or_app; right.
           repeat find_rewrite.
           simpl; in_crush; congruence.
    + right; split.
      * find_injection.
        repeat find_rewrite.
        eapply open_request_to_intro; try erewrite sigma_ahr_passthrough; simpl; eauto.
        rewrite_update.
        repeat invcs_prop cur_request_timeouts_ok'; auto.
      * apply in_msgs_in_channel; simpl.
        apply in_or_app; right.
        repeat find_apply_lem_hyp in_channel_in_msgs.
        repeat find_rewrite.
        in_crush; find_injection; tauto.
  - right. split; eauto.
    -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
         in_crush.
  - right. split; eauto.
    -- find_apply_lem_hyp in_channel_in_msgs. repeat find_rewrite.
       apply in_msgs_in_channel; simpl;
         in_crush.
       find_eapply_lem_hyp clients_not_in_failed; eauto. intuition.
Qed.