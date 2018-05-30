Require Import List.
Import ListNotations.


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

Set Bullet Behavior "Strict Subproofs".

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

Definition channel_measure_zero_empty :
  forall s from to,
    now (measure_zero (channel_measure from to)) s ->
    now (fun occ => channel (occ_gst occ) from to = []) s.
Proof.
  intros. destruct s. simpl in *.
  unfold measure_zero, channel_measure in *.
  destruct (channel (occ_gst o) from to); simpl in *; congruence.
Qed.

Lemma filterMap_map :
  forall A B C (f : B -> option C) (g : A -> B) (l : list A),
    filterMap f (map g l) =
    filterMap (fun x => f (g x)) l.
Proof.
  intros. induction l; auto.
  - simpl. break_match; congruence.
Qed.

Lemma channel_measure_nonincreasing :
  forall ex dead h,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    In dead (failed_nodes (occ_gst (hd ex))) ->
    always (consecutive (measure_nonincreasing (channel_measure dead h))) ex.
Proof.
  cofix c.
  intros.
  apply Always.
  - clear c.
    inv_prop lb_execution. simpl in *.
    unfold measure_nonincreasing, channel_measure.
    inv_prop labeled_step_dynamic.
    + simpl in *.
      unfold channel.
      repeat find_rewrite. simpl.
      rewrite filterMap_app.
      rewrite filterMap_map.
      simpl.
      destruct (addr_eq_dec h0 dead); subst; try congruence.
      simpl.
      rewrite filterMap_all_None; intuition.
    + simpl in *. unfold channel.
      repeat find_rewrite. simpl.
      rewrite filterMap_app.
      simpl.
      rewrite filterMap_map.
      simpl.
      destruct (addr_eq_dec (fst (snd m)) dead); subst; try congruence.
      simpl.
      rewrite filterMap_all_None; intuition.
      simpl.
      repeat rewrite filterMap_app. repeat rewrite app_length.
      simpl; break_match; simpl; intuition.
    + simpl in *. unfold channel.
      repeat find_rewrite. simpl.
      destruct (addr_eq_dec h0 dead); subst; [exfalso; eapply clients_not_in_failed; eauto|].
      simpl. auto.
    + unfold channel. repeat find_rewrite.
      simpl.
      repeat rewrite filterMap_app. repeat rewrite app_length.
      simpl; break_match; simpl; intuition.
  - inv_prop lb_execution.
    simpl in *.
    apply c; eauto using reachable_st_lb_execution_cons.
    simpl in *.
    erewrite <- labeled_step_dynamic_preserves_failed_nodes; eauto.
Qed.

Lemma channel_measure_zero_or_eventually_decreasing :
  forall ex dead h,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    weak_local_fairness ex ->
    In dead (failed_nodes (occ_gst (hd ex))) ->
    In h (nodes (occ_gst (hd ex))) ->
    ~ In h (failed_nodes (occ_gst (hd ex))) ->
    always (zero_or_eventually_decreasing (channel_measure dead h)) ex.
Proof.
  cofix c.
  intros.
  apply Always.
  - clear c.
    unfold zero_or_eventually_decreasing.
    unfold or_tl.
    destruct (channel (occ_gst (hd ex)) dead h) eqn:?.
    + left. destruct ex. simpl in *. unfold measure_zero, channel_measure.
      repeat find_rewrite. auto.
    + right.
      find_copy_apply_lem_hyp nodes_have_state; auto. break_exists.
      eapply eventually_monotonic with (J := lb_execution); auto.
      eauto using lb_execution_invar.
      2:eapply RecvMsg_eventually_occurred with (src := dead) (m := p); eauto.
      * intros.
        inv_prop lb_execution.
        simpl in *.
        unfold occurred in *.
        repeat find_reverse_rewrite.
        inv_prop labeled_step_dynamic.
        -- unfold timeout_handler_l in *.
           break_let. solve_by_inversion.
        -- unfold recv_handler_l in *.
           find_inversion.
           unfold measure_decreasing, channel_measure, channel.
           repeat find_rewrite. simpl.
           rewrite filterMap_app.
           simpl.
           rewrite filterMap_map.
           simpl.
           destruct (addr_eq_dec (fst (snd m)) (fst m));
             repeat find_rewrite; intuition.
           simpl.
           rewrite filterMap_all_None; intuition.
           simpl.
           repeat rewrite filterMap_app.
           simpl.
           repeat match goal with
                  | |- context [addr_eq_dec ?x ?x] =>
                    destruct (addr_eq_dec x x); try congruence
                  end.
           simpl. repeat rewrite app_length. simpl. intuition.
        -- unfold label_input in *. congruence.
        -- unfold label_output in *. congruence.
      * apply in_channel_in_msgs; repeat find_rewrite; in_crush.
  - destruct ex. simpl.
    inv_prop lb_execution.
    apply c;
      eauto using weak_local_fairness_invar, reachable_st_lb_execution_cons;
      try solve [erewrite <- labeled_step_dynamic_preserves_failed_nodes; eauto];
      try solve [erewrite <- labeled_step_dynamic_preserves_nodes; eauto].
Qed.

Lemma dead_node_channel_empties_out' :
  forall ex dead h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    In h (nodes (occ_gst (hd ex))) ->
    ~ In h (failed_nodes (occ_gst (hd ex))) ->
    In dead (failed_nodes (occ_gst (hd ex))) ->
    weak_local_fairness ex ->
    continuously (now (fun occ => channel (occ_gst occ) dead h = [])) ex.
Proof.
  intros.
  eapply continuously_monotonic; [intros; eapply channel_measure_zero_empty; eauto|].
  eapply measure_decreasing_to_zero;
    eauto using channel_measure_nonincreasing, channel_measure_zero_or_eventually_decreasing.
Qed.

Lemma dead_node_channel_empties_out :
  forall ex dead h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    live_node (occ_gst (hd ex)) h ->
    In dead (failed_nodes (occ_gst (hd ex))) ->
    weak_local_fairness ex ->
    continuously (now (fun occ => channel (occ_gst occ) dead h = [])) ex.
Proof.
  unfold live_node in *. eauto using dead_node_channel_empties_out'.
Qed.

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

