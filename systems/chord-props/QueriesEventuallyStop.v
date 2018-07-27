Require Import List.
Import ListNotations.
Require Import Relations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Update.
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.
Require Import Chord.InfSeqTactics.

Require Import Chord.Chord.

Require Import Chord.HandlerLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.
Require Import Chord.LabeledLemmas.
Require Import Chord.ChannelLemmas.
Require Import Chord.LiveNodesNotClients.
Require Import Chord.QueryInvariant.
Require Import Chord.NodesHaveState.

Set Bullet Behavior "Strict Subproofs".

(* The (blocked_by s h) relation relates a live node h to a node s when
   a message from h is stored in the delayed_queries list at s. *)
Definition blocked_by (gst : global_state) (s h : addr) : Prop :=
  In h (nodes gst) /\
  In s (nodes gst) /\
  exists st__h st__s dstp q m,
    sigma gst h = Some st__h /\
    sigma gst s = Some st__s /\
    cur_request st__h = Some (dstp, q, m) /\
    addr_of dstp = s /\
    In (h, m) (delayed_queries st__s).

Lemma blocked_by_intro :
  forall gst s h,
    In h (nodes gst) ->
    In s (nodes gst) ->
    forall st__h st__s dstp q m,
      sigma gst h = Some st__h ->
      sigma gst s = Some st__s ->
      cur_request st__h = Some (dstp, q, m) ->
      addr_of dstp = s ->
      In (h, m) (delayed_queries st__s) ->
      blocked_by gst s h.
Proof.
  unfold blocked_by.
  intuition (repeat eexists; eauto).
Qed.
Hint Resolve blocked_by_intro.

(* There is a cycle in a relation iff there's an element related to
   itself by the transitive closure of the relation. *)
Definition has_cycle {A : Type} (R : A -> A -> Prop) : Prop :=
  exists x,
    clos_trans_1n A R x x.

(* A circular wait (in a given state) is a cycle in the blocked_by
   relation (for that state). *)
Definition circular_wait (occ : occurrence) : Prop :=
  has_cycle (blocked_by (occ_gst occ)).

Inductive fin_chain {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
| FinChainNil : fin_chain R []
| FinChainOne : forall x, fin_chain R [x]
| FinChainCons : forall x y l,
    R x y ->
    fin_chain R (y :: l) ->
    fin_chain R (x :: y :: l).
Hint Constructors fin_chain.

Theorem pigeon_cycle :
  forall A (R : A -> A -> Prop) l,
    (forall a b, R a b -> In a l /\ In b l) ->
    forall c,
    fin_chain R c ->
    length c > length l ->
    has_cycle R.
Proof.
(* not sure I need this machinery yet *)
Admitted.

Definition busy_if_live (h : addr) (occ : occurrence) :=
  forall st,
    live_node (occ_gst occ) h ->
    sigma (occ_gst occ) h = Some st ->
    cur_request st <> None.

Definition not_busy_if_live (h : addr) (occ : occurrence) :=
  forall st,
    live_node (occ_gst occ) h ->
    sigma (occ_gst occ) h = Some st ->
    cur_request st = None.

Lemma now_const :
  forall T (P : T -> Prop),
    (forall t, P t) ->
    forall ex,
      (now P) ex.
Proof.
  destruct ex.
  simpl; auto.
Qed.
Hint Resolve now_const.

Lemma always_const :
  forall T (P : infseq T -> Prop),
    (forall s, P s) ->
    forall ex,
      always P ex.
Proof.
  intros.
  eapply always_monotonic; [|eapply always_true].
  auto.
Qed.
Hint Resolve always_const.

Theorem joined_nodes_never_run_join :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    joined st = true ->
    forall dst q m k,
      cur_request st = Some (dst, q, m) ->
      q <> Join k.
Proof.
Admitted.

Lemma continuously_false_false :
  forall T (s : infseq T),
    continuously (fun _ => False) s ->
    False.
Proof.
  intros.
  induction 0 as [[o s] ?|o s];
    now inv_prop always.
Qed.

Theorem l_enabled_RecvMsg_means_in_msgs :
  forall src dst m occ,
    l_enabled (RecvMsg src dst m) occ ->
    In (src, (dst, m)) (msgs (occ_gst occ)).
Proof.
  intros.
  inv_prop l_enabled.
  inv_labeled_step.
  handler_def.
  repeat find_rewrite; destruct m0 as [? [? ?]];
    repeat find_rewrite || find_injection;
    eauto with datatypes.
Qed.
Hint Resolve l_enabled_RecvMsg_means_in_msgs.

Theorem cur_request_constant_when_res_on_wire :
  forall gst l gst' h st st' dstp q m,
    labeled_step_dynamic gst l gst' ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    cur_request st = Some (dstp, q, m) ->
    query_request q m ->
    In (h, (addr_of dstp, m)) (msgs gst) ->
    ~ In (addr_of dstp) (failed_nodes gst) -> 
    cur_request st' = Some (dstp, q, m).
Proof.
Admitted.

Theorem req_on_wire_until_response :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall dstp q m st,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      query_request q m ->
      In m (channel (occ_gst (hd ex)) h (addr_of dstp)) ->
      live_node (occ_gst (hd ex)) (addr_of dstp) ->
      until (now (fun o =>
                    In m (channel (occ_gst o) h (addr_of dstp))))
            (next (now (fun o =>
                          blocked_by (occ_gst o) (addr_of dstp) h \/
                          exists res,
                            request_response_pair m res /\
                            In res (channel (occ_gst o) (addr_of dstp) h))))
            ex.
Proof.
  intros.
  assert (until (now (l_enabled (RecvMsg h (addr_of dstp) m)))
                (now (occurred (RecvMsg h (addr_of dstp) m))) ex).
  {
    find_apply_lem_hyp in_channel_in_msgs.
    inv_prop live_node; expand_def; eauto.
    eapply RecvMsg_strong_until_occurred;
      eauto using strong_local_fairness_weak.
  }
  assert (forall st, sigma (occ_gst (hd ex)) h = Some st -> cur_request st = Some (dstp, q, m))
    by (intros; congruence).
  repeat match goal with
         | H: In _ (channel _ _ _) |- _ => clear H
         | H: sigma _ _ = _ |- _ => clear H
         | H: cur_request st = _ |- _ => clear H
         end.
  match goal with
  | H: until _ _ _ |- _ => induction H
  end.
  - destruct s as [o [o' s]].
    eapply U0; simpl in *.
    unfold occurred in *;
      inv_lb_execution;
      inv_labeled_step;
      clean_up_labeled_step_cases.
    handler_def.
    destruct m0 as [? [? ?]]; repeat find_rewrite || find_injection.
    simpl (fst _) in *; simpl (snd _) in *.
    find_copy_apply_lem_hyp requests_get_response_or_queued; eauto.
    break_or_hyp; break_and.
    + left.
      repeat split; invar_eauto.
      simpl.
      assert (live_node (occ_gst o') a) by invar_eauto.
      assert (live_node (occ_gst o') (addr_of dstp)) by invar_eauto.
      assert (live_node (occ_gst o) a) by invar_eauto.
      assert (live_node (occ_gst o) (addr_of dstp)) by invar_eauto.
      do 4 invcs_prop live_node; expand_def.
      pose proof (query_message_ok_invariant (occ_gst o') ltac:(invar_eauto) a (addr_of dstp)) as Qi'.
      do 2 insterU Qi'.
      repeat conclude Qi' eauto.
      pose proof (query_message_ok_invariant (occ_gst o) ltac:(invar_eauto) a (addr_of dstp)) as Qi.
      do 2 insterU Qi.
      repeat conclude Qi eauto.

      rewrite update_same.
      assert (cur_request x1 = Some (dstp, q, p)) by eauto.
      assert (cur_request st0 = cur_request d).
      {
        destruct (cur_request x2) as [[[? ?] ?]|] eqn:?.
        - repeat find_rewrite || find_injection.
          simpl in *.
          repeat find_inversion.
          repeat find_reverse_rewrite.
          eapply recv_msg_not_right_response_preserves_cur_request; eauto.
        - congruence.
      }
      destruct_update.
      * repeat (find_rewrite; find_injection).
        repeat eexists; eauto.
        instantiate (1:=q).
        congruence.
      * repeat eexists; eauto.
    + right.
      break_exists_exists; intuition eauto.
      apply in_msgs_in_channel; simpl.
      apply in_or_app; left.
      apply in_map_iff; eauto.
  - destruct s as [o [o' s]]; simpl in *.
    apply U_next; eauto.
    + simpl.
      eapply in_msgs_in_channel, l_enabled_RecvMsg_means_in_msgs.
      eauto.
    + apply IHuntil; invar_eauto.
      intros.
      inv_prop lb_execution.
      repeat invcs_prop live_node; expand_def.
      eapply cur_request_constant_when_res_on_wire; invar_eauto.
Qed.

Theorem have_cur_request_msg_on_wire_preserves :
  forall h dst ex q m r,
    reachable_st (occ_gst (hd ex)) ->
    live_node (occ_gst (hd ex)) h ->
    (exists st, sigma (occ_gst (hd ex)) (addr_of dst) = Some st) ->
    lb_execution ex ->
    In r (channel (occ_gst (hd ex)) (addr_of dst) h) ->
    (forall st, 
        sigma (occ_gst (hd ex)) h = Some st ->
        cur_request st = Some (dst, q, m)) ->
    request_response_pair m r ->
    weak_until (now (fun o => In r (channel (occ_gst o) (addr_of dst) h) ->
                           exists st,
                             sigma (occ_gst o) h = Some st /\
                             cur_request st = Some (dst, q, m)))
               (now (fun o => ~ In r (channel (occ_gst o) (addr_of dst) h)))
               ex.
Proof.
  cofix c.
  intros.
  eapply W_tl; simpl.
  - intros.
    destruct ex; simpl.
    repeat invcs_prop live_node; expand_def.
    eexists; split; eauto.
  - destruct ex as [o [o' ex]].
    set (gst := occ_gst o).
    pose proof (query_message_ok'_invariant gst ltac:(eauto) h (addr_of dst)).
    destruct (label_eq_dec (RecvMsg (addr_of dst) h r) (occ_label o)).
    + eapply W0.
      simpl.
      inv_prop lb_execution.
      repeat find_reverse_rewrite.
      inv_labeled_step; clean_up_labeled_step_cases.
      repeat find_rewrite; intuition.
      repeat invcs_prop live_node; expand_def.
      copy_eapply_prop_hyp query_message_ok' sigma; eauto.
      inv_prop query_message_ok';
        try inv_prop query_message_ok;
        try solve [congruence
                  |eapply_prop no_responses;
                   repeat find_rewrite; eauto].
      * assert (res0 = r) by admit; subst.
        admit.
      * assert (res0 = r) by admit; subst.
        admit.
      * inv_option_map.
        repeat find_rewrite.
        admit.
    + assert (live_node (occ_gst o') h) by invar_eauto.
      apply c; invar_eauto.
      * admit.
      * apply in_msgs_in_channel.
        simpl.
        inv_lb_execution.
        inv_labeled_step; repeat find_rewrite; simpl.
        -- eauto with datatypes.
        -- handler_def.
           assert (m0 <> (addr_of dst, (h, r)))
             by (destruct m0 as [? [? ?]]; simpl in *; congruence).
           find_apply_lem_hyp in_channel_in_msgs; simpl in *.
           repeat find_rewrite.
           apply in_or_app; right.
           find_apply_lem_hyp in_app_or; simpl in *.
           intuition eauto with datatypes.
        -- eauto.
        -- assert (m0 <> (addr_of dst, (h, r))).
           {
             intro; subst.
             exfalso; eapply live_nodes_not_clients; invar_eauto.
           }
           find_apply_lem_hyp in_channel_in_msgs; simpl in *.
           repeat find_rewrite.
           find_apply_lem_hyp in_app_or; simpl in *.
           intuition eauto with datatypes.
      * admit.
Admitted.

Theorem never_stuck_on_non_stabilize_with_res_on_wire :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall dstp q m res st,
      q <> Stabilize ->
      query_response q res ->
      In res (channel (occ_gst (hd ex)) (addr_of dstp) h) ->
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      always (now
                (fun o =>
                   forall st,
                     sigma (occ_gst o) h = Some st ->
                     cur_request st <> None))
             ex ->
      False.
Proof.
  intros.
  cut (continuously (fun _ => False) ex);
    [eauto using continuously_false_false|].
  find_copy_eapply_lem_hyp have_cur_request_msg_on_wire_preserves; eauto;
    [
    |eapply nodes_have_state; try eapply sent_non_client_message_means_in_nodes; invar_eauto;
     inv_prop query_response; intro; inv_prop client_payload
    |intros; repeat find_rewrite; find_injection; eauto
    ].
  find_apply_lem_hyp in_channel_in_msgs.
  find_eapply_lem_hyp RecvMsg_strong_until_occurred;
    eauto using strong_local_fairness_weak, l_enabled_RecvMsg_In_msgs.
  match goal with
  | H: In _ (msgs _) |- _ => clear H
  end.
  match goal with
  | H: until _ _ _ |- _ => induction H
  end.
  - destruct s as [o [o' [o'' s]]]; simpl in *.
    break_and; do 2 invcs_prop lb_execution.
    assert (In res0 (channel (occ_gst o) (addr_of dstp) h)).
    { simpl in *.
      unfold occurred in *.
      repeat find_reverse_rewrite.
      inv_prop RecvMsg; clean_up_labeled_step_cases.
      handler_def; find_injection.
      apply in_msgs_in_channel; repeat find_rewrite.
      replace (fst m0, (fst (snd m0), snd (snd m0))) with m0
        by (destruct m0 as [? [? ?]]; reflexivity).
      eauto with datatypes.
    }
    inv_prop channel;
      [simpl in *; tauto|].
    simpl in *; concludes.
    expand_def; repeat find_rewrite || find_injection.
    assert (exists st, sigma (occ_gst o') h = Some st /\ cur_request st = None).
    {
      unfold occurred in *; repeat find_reverse_rewrite.
      inv_prop (labeled_step_dynamic (occ_gst o)); clean_up_labeled_step_cases.
      recover_msg_from_recv_step_equality.
      subst; simpl in *.
      find_apply_lem_hyp always_now'; simpl in * |-.
      repeat find_rewrite; simpl in *.
      eexists; rewrite_update; split; eauto.
      repeat find_rewrite || find_injection.
      eapply recv_handler_response_clears_cur_request_q_single;
        try eapply recv_handler_labeling; eauto.
      intros.
      eapply joined_nodes_never_run_join; invar_eauto.
      inv_prop live_node; expand_def; congruence.
    }
    break_exists; expand_def.
    find_apply_lem_hyp always_invar; find_apply_lem_hyp always_now'.
    assert (cur_request _ <> None) by eauto.
    tauto.
  - inv_prop weak_until.
    + simpl in *; intuition; find_false; eauto.
    + eapply E_next, IHuntil; invar_eauto.
Qed.

Theorem always_stuck_blocked_always_blocked :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall dstp q m,
      live_node (occ_gst (hd ex)) (addr_of dstp) ->
      always (now
                (fun o =>
                   forall st,
                     sigma (occ_gst o) h = Some st ->
                     cur_request st = Some (dstp, q, m)))
             ex ->
      blocked_by (occ_gst (hd ex)) (addr_of dstp) h ->
      always (now (fun o => blocked_by (occ_gst o) (addr_of dstp) h)) ex.
Proof.
  intros.
  inv_prop blocked_by.
Admitted.

Theorem stuck_on_a_single_query_means_blocked :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall dstp q m,
      live_node (occ_gst (hd ex)) (addr_of dstp) ->
      always (now
                (fun o =>
                   forall st,
                     sigma (occ_gst o) h = Some st ->
                     cur_request st = Some (dstp, q, m)))
             ex ->
      continuously (now (fun o => blocked_by (occ_gst o) (addr_of dstp) h)) ex.
Proof.
  intros.
  destruct ex as [o ex].

  pose proof (query_message_ok'_invariant
                (occ_gst o) ltac:(eauto) h (addr_of dstp))
    as Qok.
  set (gst := occ_gst o).
  set (dst := addr_of dstp).
  find_copy_apply_lem_hyp (live_node_means_state_exists gst h).
  break_exists_name st__h.
  find_copy_apply_lem_hyp (live_node_means_state_exists gst dst).
  break_exists_name st__dst.
  specialize (Qok st__h ltac:(eauto)).
  find_copy_apply_lem_hyp always_now; simpl in *.
  inv_prop query_message_ok';
    try inv_prop query_message_ok.
  - find_apply_hyp_hyp; congruence.
  - find_apply_hyp_hyp; congruence.
  - admit.
  - admit.
  - eapply always_continuously, always_stuck_blocked_always_blocked;
      invar_eauto.
    admit.
  - admit.
  - admit.
Admitted.

Lemma blocking_node_continuously_also_blocked :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    forall h s,
      always (now (fun o => blocked_by (occ_gst o) s h)) ex ->
      exists w,
        continuously (now (fun o => blocked_by (occ_gst o) w s)) ex.
Proof.
Admitted.

Lemma now_and_tl_comm :
  forall T (P Q : T -> Prop) s,
    (now P /\_ now Q) s = now (fun o => P o /\ Q o) s.
Proof.
  intros.
  destruct s.
  reflexivity.
Qed.
Hint Rewrite now_and_tl_comm.

Theorem query_always_stuck_gives_chain :
  forall k ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    always (~_ (now circular_wait)) ex ->
    forall dstp q m,
      always (now (fun o => forall st,
                       sigma (occ_gst o) h = Some st ->
                       cur_request st = Some (dstp, q, m)))
           ex ->
      k >= 1 ->
      exists c,
        length c = k /\
        In h c /\
        continuously
          (now (fun occ => fin_chain (blocked_by (occ_gst occ)) c)) ex.
Proof.
  induction k as [|[|?]]; intros.
  - omega.
  - exists [h]; intuition.
    constructor; eauto.
  - find_copy_eapply_lem_hyp IHk; eauto; [|omega].
    break_exists_name c; intuition.
    induction H9; intros; subst.
    + destruct c as [|w [|w' c]];
        [simpl in * |-; tauto| |].
      * assert (w = h) by (simpl in *; tauto); subst.
        exists [addr_of dstp; h]; intuition.
        simpl in *; congruence.
        find_copy_eapply_lem_hyp stuck_on_a_single_query_means_blocked; eauto.
        find_apply_lem_hyp always_continuously.
        find_continuously_and_tl.
        eapply continuously_monotonic; try eassumption.
        intro s0; rewrite now_and_tl_comm.
        apply now_monotonic; intuition eauto.
        admit.
      * assert (always (now (fun o => blocked_by (occ_gst o) w w')) s).
        {
          eapply always_monotonic;
            [eapply now_monotonic|eassumption].
          intros; now inv_prop @fin_chain.
        }
        find_eapply_lem_hyp blocking_node_continuously_also_blocked; eauto.
        break_exists_name w0.
        exists (w0 :: w :: w' :: c).
        intuition; simpl in *; try omega.
        find_apply_lem_hyp always_continuously.
        find_continuously_and_tl.
        eapply continuously_monotonic; try eassumption.
        intro s0; rewrite now_and_tl_comm.
        apply now_monotonic; intuition eauto.
    + assert (exists c : list addr,
                 length c = S (S n) /\
                 In h c /\
                 continuously (now (fun occ => fin_chain (blocked_by (occ_gst occ)) c)) s)
        by (eapply IHeventually; invar_eauto).
      break_exists_exists; intuition.
      constructor; now auto.
Admitted.

Theorem never_stopping_means_stuck_on_a_single_query :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall st dstp q m,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      always (~_ (now circular_wait)) ex ->
      always (now (fun o => forall st',
                           sigma (occ_gst o) h = Some st' ->
                           cur_request st' <> None)) ex ->
      exists dstp' q' m',
        continuously (now (fun o =>
                             forall st',
                               sigma (occ_gst o) h = Some st' ->
                               cur_request st' = Some (dstp', q', m')))
                     ex.
Proof.
Admitted.

Theorem queries_dont_always_not_stop :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall st dstp q m,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      always (~_ (now circular_wait)) ex ->
      ~ always (now (fun o => forall st',
                         sigma (occ_gst o) h = Some st' ->
                         cur_request st' <> None)) ex.
Proof.
  intuition.
  cut (eventually (now circular_wait) ex).
  {
    intros.
    clear H3.
    induction H7.
    -  repeat find_apply_lem_hyp always_now'.
       unfold not_tl in *.
       destruct s; auto.
    - apply IHeventually; invar_eauto.
  }
  find_eapply_lem_hyp never_stopping_means_stuck_on_a_single_query; eauto; break_exists.
  match goal with
  | H: sigma _ h = Some _ |- _ => clear H
  end.
  match goal with
  | H: continuously _ _ |- _ => induction H
  end.
  - remember (length (nodes (occ_gst (hd s)))) as k.
    find_eapply_lem_hyp (query_always_stuck_gives_chain (S k)); omega || eauto.
    break_exists; break_and.
    match goal with
    | H: continuously _ _ |- _ => induction H
    end.
    + destruct s; apply E0.
      find_apply_lem_hyp always_now'; simpl in *.
      eapply pigeon_cycle with (l := nodes (occ_gst o));
        [|eassumption|omega].
      intros; inv_prop blocked_by; tauto.
    + eapply E_next, IHeventually; invar_eauto.
      inv_prop lb_execution.
      inv_prop labeled_step_dynamic;
        simpl;
        repeat (find_rewrite || find_injection);
        auto using apply_handler_result_nodes.
  - eapply E_next, IHeventually; invar_eauto.
Qed.

Theorem queries_eventually_stop' :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall st dstp q m,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      always (~_ (now circular_wait)) ex ->
      eventually (now (fun o => forall st',
                           sigma (occ_gst o) h = Some st' ->
                           cur_request st' = None)) ex.
Proof.
  intros.
  find_eapply_lem_hyp queries_dont_always_not_stop; eauto.
  eapply not_always_eventually_not in H5.
  eapply eventually_monotonic_simple; [|eassumption].
  unfold not_tl; destruct s; simpl.
  intros.
  apply Classical_Prop.NNPP.
  firstorder.
Qed.

(** the big assumption for inf_often stabilization *)
Theorem queries_eventually_stop :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    busy_if_live h (hd ex) ->
    always (~_ (now circular_wait)) ex ->
    eventually (now (not_busy_if_live h)) ex.
Proof.
  intros.
  inv_prop live_node; repeat (break_exists || break_and).
  copy_eapply_prop_hyp busy_if_live live_node;
    forwards; eauto; concludes; eauto.
  destruct (cur_request x) as [[[? ?] ?]|] eqn:?; try congruence.
  find_eapply_lem_hyp queries_eventually_stop'; eauto.
  eapply eventually_monotonic_simple; try eassumption.
  destruct s; unfold not_busy_if_live.
  simpl; firstorder.
(*
This is tricky.

  If you have an open request, you're in the middle of some operation.
  Operations (stabilization, rectifying, etc) undertaken by joined nodes complete
  in finitely many request-response pairs.
  A request eventually gets a response if there are no circular waits...

DIFFICULTY: Ryan
USED: In phase one for the proof of eventual stabilization.
*)
Qed.
