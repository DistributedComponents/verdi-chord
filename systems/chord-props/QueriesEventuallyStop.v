Require Import List.
Import ListNotations.
Require Import Relations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Update.
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.
Require Import Chord.InfSeqTactics.
Require Import Chord.LabeledWF.

Require Import Chord.Chord.

Require Import Chord.HandlerLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemPointers.
Require Import Chord.LabeledLemmas.
Require Import Chord.LiveNodesNotClients.
Require Import Chord.QueryInvariant.
Require Import Chord.NodesHaveState.
Require Import Chord.ValidPointersInvariant.

Set Bullet Behavior "Strict Subproofs".

(* The (blocked_by s h) relation relates a live node h to a node s when
   a message from h is stored in the delayed_queries list at s. *)
Definition blocked_by (gst : global_state) (s h : addr) : Prop :=
  live_node gst h /\
  live_node gst s /\
  exists st__h st__s dstp q m,
    sigma gst h = Some st__h /\
    sigma gst s = Some st__s /\
    cur_request st__h = Some (dstp, q, m) /\
    cur_request st__s <> None /\
    addr_of dstp = s /\
    In (h, m) (delayed_queries st__s).

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
      unfold blocked_by.
      repeat (split; invar_eauto).
      assert (live_node (occ_gst o') a) by invar_eauto.
      assert (live_node (occ_gst o') (addr_of dstp)) by invar_eauto.
      assert (live_node (occ_gst o) a) by invar_eauto.
      assert (live_node (occ_gst o) (addr_of dstp)) by invar_eauto.
      do 4 invcs_prop live_node; expand_def.
      pose proof (query_message_ok_invariant (occ_gst o') ltac:(invar_eauto) a (addr_of dstp)) as Qi'.
      do 2 insterU Qi'.
      forwards; eauto. concludes.
      forwards; eauto. concludes.
      pose proof (query_message_ok_invariant (occ_gst o) ltac:(invar_eauto) a (addr_of dstp)) as Qi.
      do 2 insterU Qi.
      forwards; eauto. concludes.
      forwards; eauto. concludes.

      rewrite update_same.
      assert (cur_request x1 = Some (dstp, q, p)) by eauto.
      assert (cur_request st0 = cur_request d).
      {
        destruct (cur_request x2) as [[[? ?] ?]|] eqn:?.
        - repeat find_rewrite || find_injection.
          simpl in *.
          do 4 find_inversion.
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
    pose proof (query_message_ok_invariant gst ltac:(eauto) h (addr_of dst)).
    destruct (label_eq_dec (RecvMsg (addr_of dst) h r) (occ_label o)).
    + eapply W0.
      simpl.
      inv_prop lb_execution.
      repeat find_reverse_rewrite.
      inv_labeled_step; clean_up_labeled_step_cases.
      repeat find_rewrite; intuition.
      repeat invcs_prop live_node; expand_def.
      copy_eapply_prop_hyp query_message_ok sigma; eauto.
      inv_prop query_message_ok; try congruence.
      * exfalso; eapply_prop no_responses;
          repeat find_rewrite; eauto.
      * admit.
      * admit.
      * assert (res0 = r) by admit; subst.
        admit.
      * exfalso; eapply_prop no_responses;
          repeat find_rewrite; eauto.
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

Inductive cr_order (h : addr) : rel global_state :=
| CRNone :
    forall gst gst' st st' dstp q m,
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      cur_request st = Some (dstp, q, m) ->
      cur_request st' = None ->
      cr_order h gst' gst
| CRStabilizeStabilize2 :
    forall gst gst' st st' dstp m dstp' ns m',
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      cur_request st = Some (dstp, Stabilize, m) ->
      cur_request st' = Some (dstp', Stabilize2 ns, m') ->
      cr_order h gst' gst
| CRStabilizeStabilize :
    forall gst gst' st st' dstp m dstp' m' s rest,
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      cur_request st = Some (dstp, Stabilize, m) ->
      succ_list st = s :: rest ->
      cur_request st' = Some (dstp', Stabilize, m') ->
      succ_list st' = rest ->
      cr_order h gst' gst.

Lemma none_best_cur_request :
  forall h gst,
    stuck (cr_order h) gst ->
    forall st,
      sigma gst h = Some st ->
      cur_request st = None.
Proof.
  intros.
  destruct (cur_request st) as [[[dstp q] m]|] eqn:?; auto.
  set (st' := clear_query st).
  set (gst' := {| nodes := nodes gst;
                  failed_nodes := failed_nodes gst;
                  timeouts := timeouts gst;
                  sigma := update addr_eq_dec (sigma gst) h (Some st');
                  msgs := msgs gst;
                  trace := trace gst |}).
  find_eapply_lem_hyp (CRNone h gst gst'); simpl; rewrite_update; eauto.
  firstorder.
Qed.
Hint Resolve none_best_cur_request.

Lemma stuck_if_cr_none :
  forall h gst st,
    sigma gst h = Some st ->
    cur_request st = None ->
    stuck (cr_order h) gst.
Proof.
  unfold stuck; intros.
  inv_prop cr_order; congruence.
Qed.
Hint Resolve stuck_if_cr_none.

Lemma cr_order_stabilize2_acc :
  forall h gst st dstp ns m,
    sigma gst h = Some st ->
    cur_request st = Some (dstp, Stabilize2 ns, m)  ->
    Acc (cr_order h) gst.
Proof.
  intros.
  constructor; intros;
    inv_prop cr_order;
    congruence || eauto.
Qed.
Hint Resolve cr_order_stabilize2_acc.

Lemma cr_order_stabilize_acc :
  forall h gst st dstp m,
    sigma gst h = Some st ->
    cur_request st = Some (dstp, Stabilize, m) ->
    Acc (cr_order h) gst.
Proof.
  intros.
  remember (succ_list st) as succs.
  generalizeEverythingElse succs.
  induction succs;
    constructor; intros.
  - inv_prop cr_order;
      solve [eauto | congruence].
  - inv_prop cr_order; eauto.
    eapply IHsuccs;
      solve [eauto | congruence].
Qed.
Hint Resolve cr_order_stabilize_acc.

Theorem cr_order_wf :
  forall h,
    well_founded (cr_order h).
Proof.
  unfold well_founded.
  constructor.
  intros; inv_prop cr_order; eauto.
Qed.
Hint Resolve cr_order_wf.

Inductive channel_order (src : addr) : global_state -> global_state -> Prop :=
  COReqRes :
    forall dstp q m st st' st__dstp st__dstp' gst gst' req res xs ys xs' ys',
      sigma gst src = Some st ->
      cur_request st = Some (dstp, q, m) ->
      request_response_pair req res ->

      channel gst src (addr_of dstp) = xs ++ req :: ys ->
      no_requests (xs ++ ys) ->
      no_responses (channel gst (addr_of dstp) src) ->
      sigma gst (addr_of dstp) = Some st__dstp ->
      (forall r, ~ In (src, r) (delayed_queries st__dstp)) ->

      no_requests (channel gst' src (addr_of dstp)) ->
      sigma gst' src = Some st' ->
      cur_request st' = Some (dstp, q, m) ->
      channel gst' (addr_of dstp) src = xs' ++ res :: ys' ->
      no_responses (xs' ++ ys') ->
      sigma gst' (addr_of dstp) = Some st__dstp' ->
      (forall r, ~ In (src, r) (delayed_queries st__dstp')) ->

      channel_order src gst' gst
| COReqDelayed :
    forall dstp q m gst gst' req st st' xs ys st__dst st__dst',
      sigma gst src = Some st ->
      cur_request st = Some (dstp, q, m) ->
      request_payload req ->

      channel gst src (addr_of dstp) = xs ++ req :: ys ->
      no_requests (xs ++ ys) ->
      no_responses (channel gst (addr_of dstp) src) ->
      sigma gst (addr_of dstp) = Some st__dst ->
      (forall r, ~ In (src, r) (delayed_queries st__dst)) ->

      sigma gst' src = Some st' ->
      cur_request st' = Some (dstp, q, m) ->
      no_requests (channel gst' src (addr_of dstp)) ->
      no_responses (channel gst' (addr_of dstp) src) ->
      sigma gst' (addr_of dstp) = Some st__dst' ->
      In (src, req) (delayed_queries st__dst') ->

      channel_order src gst' gst
| CODelayedRes :
    forall dstp q m gst gst' req res st st__dstp st' st__dstp' xs' ys',
      sigma gst src = Some st ->
      cur_request st = Some (dstp, q, m) ->
      request_response_pair req res ->

      sigma gst (addr_of dstp) = Some st__dstp ->
      In (src, req) (delayed_queries st__dstp) ->
      no_requests (channel gst src (addr_of dstp)) ->
      no_responses (channel gst (addr_of dstp) src) ->

      sigma gst' src = Some st' ->
      cur_request st' = Some (dstp, q, m) ->
      no_requests (channel gst' src (addr_of dstp)) ->
      channel gst' (addr_of dstp) src = xs' ++ res :: ys' ->
      no_responses (xs' ++ ys') ->
      sigma gst' (addr_of dstp) = Some st__dstp' ->
      (forall r, ~ In (src, r) (delayed_queries st__dstp')) ->

      channel_order src gst' gst.

Lemma res_exists_for_req :
  forall req,
    request_payload req ->
    exists res,
      request_response_pair req res.
Proof.
  intros.
  inv_prop request_payload; eexists; constructor.
  Unshelve.
  all:auto using nil, None.
Qed.
Hint Resolve res_exists_for_req.

Lemma res_best_channel_config :
  forall src gst st dstp q m,
    reachable_st gst ->
    stuck (channel_order src) gst ->
    sigma gst src = Some st ->
    cur_request st = Some (dstp, q, m) ->
    no_requests (channel gst src (addr_of dstp)) /\
    (forall st__dstp req,
        sigma gst (addr_of dstp) = Some st__dstp ->
        ~ In (src, req) (delayed_queries st__dstp)).
Proof.
  unfold stuck; intros.
  find_copy_eapply_lem_hyp cur_request_valid; eauto.
  inv_prop valid_ptr.
  find_apply_lem_hyp nodes_have_state; eauto.
  break_exists_name st__dstp.
  find_copy_eapply_lem_hyp (query_message_ok_invariant gst ltac:(auto) src (addr_of dstp));
    eauto.
  inv_prop query_message_ok.
  - congruence.
  - congruence.
  - simpl in *.
    assert (request_payload req) by eauto.
    find_copy_apply_lem_hyp (res_exists_for_req req).
    break_exists_name r.
    set (gst' := {| nodes := nodes gst;
                    failed_nodes := failed_nodes gst;
                    timeouts := timeouts gst;
                    sigma := sigma gst;
                    msgs := [((addr_of dstp), (src, r))];
                    trace := trace gst |}).
    assert (no_requests (channel gst' src (addr_of dstp))).
    {
      unfold no_requests.
      intros.
      find_apply_lem_hyp in_channel_in_msgs.
      simpl in *; intuition; find_injection; eauto.
    }
    assert (channel gst' (addr_of dstp) src = [r]).
    {
      unfold channel, ssrbool.is_left; simpl.
      destruct (addr_eq_dec (addr_of dstp) (addr_of dstp)); try congruence.
      destruct (addr_eq_dec src src); try congruence.
      reflexivity.
    }
    replace dstp0 with dstp in * by congruence; clear dstp0.
    find_apply_lem_hyp in_split; break_exists.
    exfalso; find_eapply_prop False.
    instantiate (1:=gst').
    econstructor 1; eauto.
    repeat find_rewrite.
    change [r] with ([] ++ r :: []); eauto.
    simpl; unfold no_responses; tauto.
  - split; auto.
    intros.
    replace st__dstp0 with st__dstp by congruence.
    eauto.
  - assert (request_payload req) by eauto.
    find_copy_apply_lem_hyp (res_exists_for_req req).
    break_exists_name r.
    set (st' := clear_delayed_queries st).
    set (gst' := {| nodes := nodes gst;
                    failed_nodes := failed_nodes gst;
                    timeouts := timeouts gst;
                    sigma := update addr_eq_dec (sigma gst) (addr_of dstp) (Some st');
                    msgs := [((addr_of dstp), (src, r))];
                    trace := trace gst |}).
    assert (no_requests (channel gst' src (addr_of dstp))).
    {
      unfold no_requests.
      intros.
      find_apply_lem_hyp in_channel_in_msgs.
      simpl in *; intuition; find_injection; eauto.
    }
    assert (channel gst' (addr_of dstp) src = [] ++ [r]).
    {
      unfold channel, ssrbool.is_left; simpl.
      destruct (addr_eq_dec (addr_of dstp) (addr_of dstp)); try congruence.
      destruct (addr_eq_dec src src); try congruence.
      reflexivity.
    }
    replace dstp0 with dstp in * by congruence; clear dstp0.
    find_apply_lem_hyp in_split; break_exists.
    exfalso; find_eapply_prop False.
    instantiate (1:=gst').
    destruct (addr_eq_dec (addr_of dstp) src).
    + econstructor 3; simpl; rewrite_update; eauto.
      * repeat find_rewrite || find_injection.
        auto with datatypes.
      * unfold no_responses; tauto.
    + econstructor 3; simpl; rewrite_update; eauto.
      * repeat find_rewrite || find_injection.
        auto with datatypes.
      * unfold no_responses; tauto.
Qed.

Lemma co_res_acc :
  forall src gst dstp xs ys res st q m,
    sigma gst src = Some st ->
    cur_request st = Some (dstp, q, m) ->
    response_payload res ->
    channel gst (addr_of dstp) src = xs ++ res :: ys ->
    no_responses (xs ++ ys) ->
    Acc (channel_order src) gst.
Proof.
  intros.
  assert (In res0 (channel gst (addr_of dstp) src))
    by (find_rewrite; auto with datatypes).
  constructor; intros; inv_prop channel_order;
    assert (dstp0 = dstp) by congruence; subst;
      exfalso;
      find_eapply_prop (no_responses (channel gst (addr_of dstp) src));
      eauto.
Qed.
Hint Resolve co_res_acc.

Lemma co_delayed_acc :
  forall src gst dstp req st q m st__dstp,
    sigma gst src = Some st ->
    cur_request st = Some (dstp, q, m) ->
    sigma gst (addr_of dstp) = Some st__dstp ->
    In (src, req) (delayed_queries st__dstp) ->
    request_payload req ->
    Acc (channel_order src) gst.
Proof.
  intros.
  constructor; intros; inv_prop channel_order;
    assert (dstp0 = dstp) by congruence; subst.
  - exfalso.
    replace st__dstp0 with st__dstp in * by congruence.
    find_eapply_prop (delayed_queries st__dstp); eauto.
  - exfalso.
    replace st__dst with st__dstp in * by congruence.
    find_eapply_prop (delayed_queries st__dstp); eauto.
  - eauto.
Qed.
Hint Resolve co_delayed_acc.

Lemma co_req_acc :
  forall gst src st dstp q m req xs ys st__dstp,
    sigma gst src = Some st ->
    cur_request st = Some (dstp, q, m) ->
    sigma gst (addr_of dstp) = Some st__dstp ->
    query_request q req ->
    channel gst src (addr_of dstp) = xs ++ req :: ys ->
    no_requests (xs ++ ys) ->
    no_responses (channel gst (addr_of dstp) src) ->
    (forall r, ~ In (src, r) (delayed_queries st__dstp)) ->
    Acc (channel_order src) gst.
Proof.
  intros.
  constructor; intros; inv_prop channel_order; eauto.
Qed.
Hint Resolve co_req_acc.

Lemma channel_order_wf :
  forall src,
    well_founded (channel_order src).
Proof.
  unfold well_founded; intros.
  constructor; intros; inv_prop channel_order; eauto.
Qed.
Hint Resolve channel_order_wf.

Definition occ_order (R : rel global_state) : rel occurrence :=
  fun o o' => R (occ_gst o) (occ_gst o').

Lemma occ_order_wf :
  forall R,
    well_founded R ->
    well_founded (occ_order R).
Proof.
  unfold well_founded, occ_order.
  intros.
  remember (occ_gst a) as o.
  assert (Hacc: Acc R o) by auto.
  generalizeEverythingElse Hacc.
  induction Hacc; intros.
  constructor; intros; subst.
  eauto.
Qed.
Hint Resolve occ_order_wf.

Lemma occ_order_stuck :
  forall R o,
    stuck (occ_order R) o ->
    stuck R (occ_gst o).
Proof.
  unfold stuck, occ_order; intros.
  (* bogus *)
  set (o':={| occ_gst := t';
              occ_label := Timeout (String.EmptyString) Tick Ineffective|}).
  change (R t' (occ_gst o)) with (R (occ_gst o') (occ_gst o)) in *.
  eauto.
Qed.
Hint Resolve occ_order_stuck.

Definition query_order (h : addr) :=
  occ_order (lex_diag (cr_order h) (channel_order h)).

Theorem query_order_wf :
  forall h,
    well_founded (query_order h).
Proof.
  unfold query_order; eauto.
Qed.
Hint Resolve query_order_wf.

Lemma stuck_query_order_cr_order :
  forall h o,
    stuck (query_order h) o ->
    stuck (cr_order h) (occ_gst o).
Proof.
  eauto.
Qed.
Hint Resolve stuck_query_order_cr_order.

Theorem stuck_query_order_done :
  forall h o st,
    stuck (query_order h) o ->
    sigma (occ_gst o) h = Some st ->
    cur_request st = None.
Proof.
  eauto.
Qed.
Hint Resolve stuck_query_order_done.
Print Assumptions stuck_query_order_done.

Definition query_order_stuck_dec :
  forall h o,
    {stuck (query_order h) o} + {~ stuck (query_order h) o}.
Proof.
Admitted.
Hint Resolve query_order_stuck_dec.

Theorem eventually_done_or_always_blocked_via_relation :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall st dstp q m,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      always (fun s =>
                ~ stuck (query_order h) (hd s) ->
                eventually (now (fun t => query_order h t (hd s))) s) ex \/
      continuously (now (fun o => exists dstp', blocked_by (occ_gst o) (addr_of dstp') h)) ex.
Proof.
Admitted.

Theorem eventually_done_or_always_blocked :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall st dstp q m,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      eventually ((now (fun o => forall st, sigma (occ_gst o) h = Some st -> cur_request st = None))) ex \/
      continuously (now (fun o => exists dstp', blocked_by (occ_gst o) (addr_of dstp') h)) ex.
Proof.
  intros.
  find_eapply_lem_hyp eventually_done_or_always_blocked_via_relation; eauto.
  break_or_hyp; try tauto.
  left.
  find_eapply_lem_hyp eventual_drop_means_eventually_stuck; eauto.
  eapply eventually_monotonic_simple; try eassumption.
  intros.
  destruct s; simpl in *; eauto.
Qed.

Ltac fold_continuously :=
  match goal with
  | H: context[eventually (always ?P)] |- _ =>
    change (eventually (always P))
      with (continuously P) in H
  end.

Lemma now_and_tl_comm :
  forall T (P Q : T -> Prop) s,
    (now P /\_ now Q) s = now (fun o => P o /\ Q o) s.
Proof.
  intros.
  destruct s.
  reflexivity.
Qed.
Hint Rewrite now_and_tl_comm.

Lemma eventually_now_const :
  forall T (s : infseq T) P,
    eventually (now (fun _ => P)) s ->
    P.
Proof.
  induction 1; destruct s; simpl in *; tauto.
Qed.

Lemma continuously_exists :
  forall T S (s : infseq T) (P: T -> S -> Prop),
    continuously (now (fun o => exists x, P o x)) s ->
    exists x,
      continuously (now (fun o => P o x)) s.
Proof.
Admitted.

Lemma blocking_node_continuously_also_blocked :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
    forall h s,
      always (now (fun o => blocked_by (occ_gst o) s h)) ex ->
      exists w,
        continuously (now (fun o => blocked_by (occ_gst o) w s)) ex.
Proof.
  intros.
  destruct ex.
  find_copy_apply_lem_hyp always_now.
  simpl in *.
  inv_prop blocked_by; break_and.
  break_exists_name st__h.
  break_exists_name st__dst; expand_def.
  assert (exists dstp q m, cur_request st__dst = Some (dstp, q, m))
    by (destruct (cur_request st__dst) as [[[dstp q] m]|] eqn:Heq;
        intuition eauto).
  expand_def.
  change o with (hd (Cons o ex)) in *;
    find_eapply_lem_hyp eventually_done_or_always_blocked;
    try find_eapply_prop (addr_of x1);
    eauto.
  break_or_hyp.
  - exfalso.
    find_eapply_lem_hyp cumul_eventually_always; eauto.
    cut (eventually (fun _ => False) (Cons o ex)).
    {
      repeat match goal with H:_ |- _ => clear H end.
      induction 1; destruct ex; simpl in *; tauto.
    }
    eapply eventually_monotonic_simple; [|eassumption].
    intros.
    unfold and_tl in *; destruct s; break_and; simpl in *.
    firstorder congruence.
  - simpl.
    find_eapply_lem_hyp continuously_exists.
    firstorder.
Qed.

Theorem query_always_stuck_gives_chain :
  forall k ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    always (now (fun o => forall st,
                     sigma (occ_gst o) h = Some st ->
                     cur_request st <> None))
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
    match goal with
    | H: continuously _ _ |- _ =>
      induction H; intros; subst
    end.
    + destruct c as [|w [|w' c]];
        [simpl in * |-; tauto| |].
      * assert (w = h) by (simpl in *; tauto); subst.
        find_copy_apply_lem_hyp live_node_means_state_exists;
          break_exists_name h__st.
        destruct (cur_request h__st) as [[[dstp q] m]|] eqn:?;
            [|destruct s; repeat find_apply_lem_hyp always_now';
              simpl in *; exfalso; eauto].
        find_copy_eapply_lem_hyp eventually_done_or_always_blocked; invar_eauto.
        break_or_hyp.
        -- exfalso.
           eapply_lem_prop_hyp cumul_eventually_always False; eauto.
           repeat match goal with
                  | H: eventually (now _) _ |- _ => clear H
                  | H: context[h__st] |- _ => clear H
                  end.
           induction H3.
           ++ destruct s; firstorder eauto.
           ++ eapply IHeventually; invar_eauto.
        -- find_apply_lem_hyp always_continuously.
           find_apply_lem_hyp continuously_exists.
           break_exists_name dstp'.
           exists [addr_of dstp'; h].
           simpl; intuition eauto.
           find_continuously_and_tl.
           eapply continuously_monotonic; try eassumption.
           intro s0; rewrite now_and_tl_comm.
           apply now_monotonic; intuition eauto.
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
Qed.

Theorem queries_dont_always_not_stop :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
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
  remember (length (nodes (occ_gst (hd ex)))) as k.
  find_copy_eapply_lem_hyp (query_always_stuck_gives_chain (S k)); omega || eauto.
  break_exists; break_and.
  repeat match goal with
         | H: sigma _ h = Some _ |- _ => clear H
         end.
  match goal with
  | H: continuously _ _ |- _ => induction H
  end.
  + destruct s; apply E0.
    find_apply_lem_hyp always_now'; simpl in *.
    eapply pigeon_cycle with (l := nodes (occ_gst o));
      [firstorder|eassumption|omega].
  + eapply E_next, IHeventually; invar_eauto.
    inv_prop lb_execution.
    inv_prop labeled_step_dynamic;
      simpl;
      repeat (find_rewrite || find_injection);
      auto using apply_handler_result_nodes.
Qed.

Theorem queries_eventually_stop' :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
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
    weak_local_fairness ex ->
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
