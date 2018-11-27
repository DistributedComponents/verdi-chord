Require Import List.
Import ListNotations.
Require Import Omega.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.TimeoutMeansActive.
Require Import Chord.NodesHaveState.
Require Import Chord.LiveNodesNotClients.
Require Import Chord.QueryTargetsJoined.

Set Bullet Behavior "Strict Subproofs".

Lemma request_response_pair_response :
  forall req res,
    request_response_pair req res ->
    response_payload res.
Proof.
  intros.
  inv_prop request_response_pair;
    constructor.
Qed.
Hint Resolve request_response_pair_response.

Lemma request_response_pair_request :
  forall req res,
    request_response_pair req res ->
    request_payload req.
Proof.
  intros.
  inv_prop request_response_pair;
    constructor.
Qed.
Hint Resolve request_response_pair_request.

Lemma handle_query_timeout_dqs :
  forall h st dst q st' ms nts cts,
    handle_query_timeout h st dst q = (st', ms, nts, cts) ->
    delayed_queries st' = delayed_queries st.
Proof.
  intros; repeat handler_def; reflexivity.
Qed.

Definition at_most_one_request_timeout' (ts : list timeout) :=
  forall xs ys dst p,
    ts = xs ++ Request dst p :: ys ->
    forall dst' p',
      ~ In (Request dst' p') (xs ++ ys).
Hint Unfold at_most_one_request_timeout'.

Definition at_most_one_request_timeout (gst : global_state) (h : addr) :=
  at_most_one_request_timeout' (timeouts gst h).
Hint Unfold at_most_one_request_timeout.

Lemma at_most_one_request_timeout'_uniqueness :
  forall ts dst dst' p p',
    at_most_one_request_timeout' ts ->
    In (Request dst p) ts ->
    In (Request dst' p') ts ->
    Request dst p = Request dst' p'.
Proof.
  intros.
  find_apply_lem_hyp (in_split (Request dst p)).
  break_exists_name xs.
  break_exists_name ys.
  assert (In (Request dst' p') (xs ++ ys) \/ Request dst p = Request dst' p').
  {
    repeat find_rewrite.
    repeat find_eapply_lem_hyp in_app_or.
    break_or_hyp;
      eauto using in_or_app.
    find_apply_lem_hyp in_inv; break_or_hyp;
      eauto using in_or_app.
  }
  break_or_hyp.
  - exfalso.
    autounfold in *.
    intuition eauto.
  - easy.
Qed.
Hint Resolve at_most_one_request_timeout'_uniqueness.

Lemma at_most_one_request_timeout_uniqueness :
  forall gst h dst dst' p p',
    at_most_one_request_timeout gst h ->
    In (Request dst p) (timeouts gst h) ->
    In (Request dst' p') (timeouts gst h) ->
    Request dst p = Request dst' p'.
Proof.
  eauto.
Qed.
Hint Resolve at_most_one_request_timeout_uniqueness.

Lemma at_most_one_request_timeout'_cons_neq :
  forall t ts,
    (forall dst p, t <> Request dst p) ->
    at_most_one_request_timeout' ts ->
    at_most_one_request_timeout' (t :: ts).
Proof.
  autounfold.
  intros.
  destruct xs; simpl in *; try congruence.
  find_injection.
  intuition eauto.
Qed.
Hint Resolve at_most_one_request_timeout'_cons_neq.

Lemma at_most_one_request_timeout'_none :
  forall ts,
    (forall dst p, ~ In (Request dst p) ts) ->
    at_most_one_request_timeout' ts.
Proof.
  autounfold; unfold not; intros.
  find_eapply_prop False; in_crush.
Qed.
Hint Resolve at_most_one_request_timeout'_none.

Lemma at_most_one_request_timeout'_cons :
  forall t ts,
    (forall dst p, ~ In (Request dst p) ts) ->
    at_most_one_request_timeout' (t :: ts).
Proof.
  intros.
  destruct t; eauto.
  autounfold; unfold not in *; intros.
  destruct xs; simpl in *.
  - find_injection; eauto.
  - find_injection.
    find_eapply_prop False; in_crush.
Qed.
Hint Resolve at_most_one_request_timeout'_cons.

Lemma at_most_one_request_timeout'_drop :
  forall t ts,
    at_most_one_request_timeout' (t :: ts) ->
    at_most_one_request_timeout' ts.
Proof.
  intros.
  unfold at_most_one_request_timeout', not in *.
  intros.
  repeat find_rewrite.
  rewrite app_comm_cons in *.
  simple eapply H.
  - reflexivity.
  - apply in_cons; eauto.
Qed.
Hint Resolve at_most_one_request_timeout'_drop.

Lemma at_most_one_request_timeout'_remove :
  forall ts t,
    at_most_one_request_timeout' ts ->
    at_most_one_request_timeout' (remove timeout_eq_dec t ts).
Proof.
  induction ts; intros.
  - easy.
  - simpl; break_if; destruct a; try eauto.
    assert (forall t, In t ts -> forall dst p, t <> (Request dst p)).
    {
      autounfold in *.
      intros; subst.
      eapply H with (xs:=nil) (ys:=ts);
        simpl; eauto.
    }
    assert (Hnoreq: forall t', In t' (remove timeout_eq_dec t ts) -> forall dst p, t' <> (Request dst p))
      by eauto using in_remove.
    autounfold; unfold not; intros.
    destruct xs.
    + simpl in *.
      find_injection.
      eapply Hnoreq; eauto.
    + simpl in *; find_injection.
      eapply Hnoreq; eauto.
Qed.
Hint Resolve at_most_one_request_timeout'_remove.

Lemma at_most_one_request_timeout'_remove_drops_all :
  forall l dst req dst' req',
    at_most_one_request_timeout' l ->
    In (Request dst' req') l ->
    ~ In (Request dst req) (remove timeout_eq_dec (Request dst' req') l).
Proof.
  intros.
  destruct (timeout_eq_dec (Request dst req) (Request dst' req')).
  - find_injection; apply remove_In.
  - eauto using in_remove.
Qed.
Hint Resolve at_most_one_request_timeout'_remove_drops_all.

Lemma at_most_one_request_timeout'_swap :
  forall t ts dst p,
    at_most_one_request_timeout' ts ->
    In (Request dst p) ts ->
    at_most_one_request_timeout' (t :: (remove timeout_eq_dec (Request dst p) ts)).
Proof.
  intros.
  destruct t; eauto.
Qed.
Hint Resolve at_most_one_request_timeout'_swap.

Definition at_most_one_request (gst : global_state) (src : addr) :=
  forall dst msg xs ys,
    msgs gst = xs ++ (src, (dst, msg)) :: ys ->
    forall dst' msg',
      In (src, (dst', msg')) (xs ++ ys) ->
      ~ request_payload msg'.

Lemma at_most_one_request_in :
  forall gst src,
    at_most_one_request gst src ->
    forall dst p,
      In (src, (dst, p)) (msgs gst) ->
      forall dst' p',
        In (src, (dst', p')) (msgs gst) ->
        request_payload p' ->
        dst = dst' /\ p = p'.
Proof.
  unfold at_most_one_request.
  intros.
  find_apply_lem_hyp (in_split (src, (dst, p))).
  break_exists_name xs.
  break_exists_name ys.
  assert (In (src, (dst', p')) (xs ++ ys) \/ (src, (dst, p)) = (src, (dst', p'))).
  {
    repeat find_rewrite.
    repeat find_eapply_lem_hyp in_app_or.
    break_or_hyp;
      eauto using in_or_app.
    find_apply_lem_hyp in_inv; break_or_hyp;
      eauto using in_or_app.
  }
  break_or_hyp.
  - cut (~ request_payload p'); [tauto|]; eauto.
  - now tuple_inversion.
Qed.

Lemma send_definition :
  forall src dst msg,
    send src (dst, msg) = (src, (dst, msg)).
Proof.
  easy.
Qed.

Theorem req_res_invariant :
  forall gst,
    reachable_st gst ->
    forall src,
      In src (nodes gst) ->
      at_most_one_request gst src.
Proof.
  intros gst H_reachable.
  induction H_reachable.
  - intros; simpl in *.
    unfold at_most_one_request; intros.
    inv_prop initial_st; break_and.
    repeat find_rewrite; find_apply_lem_hyp app_eq_nil; break_and.
    discriminate.
  - intros.
Abort.

Definition open_request_to (gst : global_state) (h : addr) (dst : addr) (m : payload) : Prop :=
  In (Request dst m) (timeouts gst h) /\
  exists q st dstp,
    query_request q m /\
    sigma gst h = Some st /\
    addr_of dstp = dst /\
    cur_request st = Some (dstp, q, m).

Lemma open_request_to_intro :
  forall gst h dst m q st dstp,
    In (Request dst m) (timeouts gst h) ->
    query_request q m ->
    sigma gst h = Some st ->
    addr_of dstp = dst ->
    cur_request st = Some (dstp, q, m) ->
    open_request_to gst h dst m.
Proof.
  firstorder.
Qed.

Definition responses_are_unique (gst : global_state) : Prop :=
  forall src dst p m m',
    In (src, (dst, m)) (msgs gst) ->
    request_response_pair p m ->
    In (src, (dst, m')) (msgs gst) ->
    request_response_pair p m' ->
    m = m'.

Definition Request_has_message (gst : global_state) : Prop :=
  forall src dst p m,
    In (Request dst p) (timeouts gst src) ->
    request_response_pair p m ->
    (~ In dst (failed_nodes gst) /\
     In (src, (dst, p)) (msgs gst)) \/
    In (dst, (src, m)) (msgs gst).

Definition Request_messages_unique (gst : global_state) : Prop :=
  forall src dst p m m',
    In (Request dst p) (timeouts gst src) ->
    request_response_pair p m ->
    In (dst, (src, m)) (msgs gst) ->
    In (dst, (src, m')) (msgs gst) ->
    m = m'.

Definition Request_payload_has_response (gst : global_state) : Prop :=
  forall src dst p,
    In (Request dst p) (timeouts gst src) ->
    exists m,
      request_response_pair p m.

(* TODO(ryan) move to Chord.v *)
Definition query_response_dec :
  forall q p,
    {query_response q p} + {~ query_response q p}.
Proof.
  destruct p, q; solve [auto | right; intro H; inv H].
Defined.

Lemma recv_msg_not_right_response_preserves_cur_request :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    forall dstp q req,
      cur_request st = Some (dstp, q, req) ->
      ~ query_response q p ->
      cur_request st' = cur_request st.
Proof.
  intros.
  repeat (handler_def || handler_simpl);
    repeat find_rewrite;
    find_injection;
    exfalso; intuition.
Qed.

Lemma recv_msg_not_right_response_from_dst_preserves_cur_request :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    forall dstp q req,
      cur_request st = Some (dstp, q, req) ->
      src <> addr_of dstp \/ ~ query_response q p ->
      cur_request st' = cur_request st.
Proof.
  intros.
  repeat (handler_def || handler_simpl);
    repeat find_rewrite;
    find_injection;
    exfalso; intuition.
Qed.

Lemma recv_msg_not_right_response_never_removes_request_timeout :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    forall dstp q req,
      cur_request st = Some (dstp, q, req) ->
      ~ query_response q p ->
      In (Request (addr_of dstp) req) nts \/
      ~ In (Request (addr_of dstp) req) cts.
Proof.
  intros.
  repeat (handler_def || handler_simpl);
    repeat (find_rewrite || find_injection);
    solve [tauto | exfalso; intuition].
Qed.

Inductive cur_request_timeouts_ok (cr : option (pointer * query * payload)) (ts : list timeout) : Prop :=
| QSTNoRequest :
    (forall dst req, ~ In (Request dst req) ts) ->
    cr = None ->
    cur_request_timeouts_ok cr ts
| QSTRequest :
    forall dstp q req,
      In (Request (addr_of dstp) req) ts ->
      cr = Some (dstp, q, req) ->
      at_most_one_request_timeout' ts ->
      query_request q req ->
      cur_request_timeouts_ok cr ts.

(* whoops, that was a bad definition. here's a better one. *)
Inductive cur_request_timeouts_ok' : option (pointer * query * payload) -> list timeout -> Prop :=
| QSTNoRequest' :
    forall ts,
      (forall dst req, ~ In (Request dst req) ts) ->
      cur_request_timeouts_ok' None ts
| QSTRequest' :
    forall ts dstp q req,
      In (Request (addr_of dstp) req) ts ->
      at_most_one_request_timeout' ts ->
      query_request q req ->
      cur_request_timeouts_ok' (Some (dstp, q, req)) ts.
Hint Constructors cur_request_timeouts_ok'.

Lemma cur_request_timeouts_ok'_sound :
  forall cr ts,
    cur_request_timeouts_ok' cr ts ->
    cur_request_timeouts_ok cr ts.
Proof.
  intros.
  inv_prop cur_request_timeouts_ok';
    econstructor; now eauto.
Qed.
Hint Resolve cur_request_timeouts_ok'_sound.

Lemma cur_request_timeouts_ok'_complete :
  forall cr ts,
    cur_request_timeouts_ok cr ts ->
    cur_request_timeouts_ok' cr ts.
Proof.
  intros.
  inv_prop cur_request_timeouts_ok; subst; eauto.
Qed.
Hint Resolve cur_request_timeouts_ok'_complete.

Definition all_nodes_cur_request_timeouts_related (gst : global_state) : Prop :=
  forall h st,
    In h (nodes gst) ->
    sigma gst h = Some st ->
    cur_request_timeouts_ok (cur_request st) (timeouts gst h).
Hint Unfold all_nodes_cur_request_timeouts_related.

Lemma remove_comm :
  forall A A_eq_dec (l : list A) x y,
    remove A_eq_dec x (remove A_eq_dec y l) = remove A_eq_dec y (remove A_eq_dec x l).
Proof.
  induction l; intros.
  - reflexivity.
  - simpl; repeat break_if.
    + now rewrite IHl.
    + simpl; break_if; congruence.
    + simpl; break_if; congruence.
    + simpl; repeat break_if; congruence.
Qed.

Lemma cur_request_timeouts_related_recv_invariant :
  chord_recv_handler_invariant all_nodes_cur_request_timeouts_related.
Proof.
  do 2 autounfold; intros.
  destruct (addr_eq_dec h0 h).
  - subst; rewrite_update.
    assert (cur_request_timeouts_ok (cur_request st) (timeouts gst h))
      by (repeat find_rewrite; auto).
    find_copy_eapply_lem_hyp recv_handler_possible_nts.
    find_copy_eapply_lem_hyp recv_handler_possible_cts.
    assert (st0 = st')
      by (repeat find_rewrite; rewrite_update; congruence);
      subst.
    inv_prop cur_request_timeouts_ok.
    + destruct nts.
      * destruct (cur_request st') as [[[? ?] ?]|] eqn:?.
        -- repeat (handler_def || handler_simpl).
        -- econstructor; eauto;
             repeat find_rewrite; rewrite_update; simpl; auto.
           autounfold; intros.
           find_apply_lem_hyp in_remove_all_was_in.
           cut (~ In (Request dst req) (timeouts gst h)); [intuition|].
           inv_prop cur_request_timeouts_ok; eauto.
      * repeat (handler_def || handler_simpl ||
                match goal with
                | H : context[recv_handler] |- _ =>
                  eapply recv_handler_sets_cur_request_when_adding_new_timeout in H; eauto with datatypes;
                  expand_def;
                  econstructor 2;
                  repeat find_rewrite;
                  try rewrite update_eq;
                  eauto with datatypes
                end).
        econstructor; repeat find_rewrite; rewrite_update; eauto with datatypes.
        autounfold; intros; simpl in *; break_or_hyp; try congruence.
        cut (In (Request dst req) (timeouts gst h)); [eauto|].
        eapply in_remove; eauto.
    + destruct (query_response_dec q p).
      * handler_def.
        handler_def; try solve [invcs_prop query_response].
        -- repeat (handler_def || handler_simpl);
             repeat (find_rewrite || find_injection || rewrite_update);
             eauto using remove_preserve with datatypes.
        -- repeat (handler_def || handler_simpl).
           repeat find_rewrite; rewrite_update; eauto.
        -- find_copy_apply_lem_hyp timeouts_in_Some.
           repeat (handler_def || handler_simpl || expand_def);
             repeat (find_rewrite || find_injection || rewrite_update);
             try inv_prop query_response;
             autorewrite with list;
             eauto using remove_In with datatypes;
             try solve [simpl;
                        eauto with datatypes;
                        econstructor; intros; eauto;
                        rewrite remove_comm;
                        eauto using remove_preserve].
           ++ econstructor 2; try reflexivity; eauto; repeat find_rewrite;
                eauto using at_most_one_request_timeout'_swap with datatypes.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
              intro.
              simpl in *.
              break_or_hyp; try congruence.
              rewrite remove_comm in *.
              find_apply_lem_hyp in_remove.
              eapply at_most_one_request_timeout'_remove_drops_all; eauto.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
              intro.
              simpl in *.
              break_or_hyp; try congruence.
              rewrite remove_comm in *.
              find_apply_lem_hyp in_remove.
              eapply at_most_one_request_timeout'_remove_drops_all; eauto.
        -- repeat (handler_def || handler_simpl).
      * find_copy_eapply_lem_hyp recv_msg_not_right_response_preserves_cur_request; eauto.
        find_copy_eapply_lem_hyp recv_msg_not_right_response_never_removes_request_timeout; eauto.
        inv_prop cur_request_timeouts_ok; try congruence.
        repeat find_rewrite; rewrite_update; find_injection.
        break_or_hyp.
        -- econstructor 2; eauto with datatypes.
           repeat (handler_def || handler_simpl ||
                   solve [exfalso; eapply_prop query_response; constructor]).
           ++ intros.
              destruct xs0;
                [simpl in *; find_inversion; congruence|find_inversion].
              simpl in *; find_injection.
              break_or_hyp; try congruence.
              eauto.
           ++ intros.
              destruct xs0;
                [simpl in *; find_inversion; congruence|find_inversion].
              simpl in *; find_injection.
              break_or_hyp; try congruence.
              eauto.
           ++ intros.
              destruct xs0;
                [simpl in *; find_inversion; congruence|find_inversion].
              simpl in *; find_injection.
              break_or_hyp; try congruence.
              eauto.
           ++ find_copy_eapply_lem_hyp In_timeouts_in; break_exists; break_and.
              repeat find_rewrite.
              do 4 find_inversion.
              intros.
              destruct xs0; simpl in *; find_injection;
                inv_prop cur_request_timeouts_ok; try congruence;
                  find_injection;
                  eapply at_most_one_request_timeout'_remove_drops_all; eauto.
        -- assert (cur_request_timeouts_ok (cur_request st) (timeouts gst h))
            by auto.
           repeat (handler_def || handler_simpl).
           ++ simpl in *.
              repeat find_reverse_rewrite.
              invcs_prop cur_request_timeouts_ok; try congruence.
              econstructor 2; eauto using at_most_one_request_timeout'_cons_neq with datatypes.
           ++ repeat find_reverse_rewrite.
              invcs_prop cur_request_timeouts_ok; try congruence.
              econstructor 2; eauto using at_most_one_request_timeout'_cons_neq with datatypes.
           ++ repeat find_reverse_rewrite.
              invcs_prop cur_request_timeouts_ok; try congruence.
              econstructor 2; eauto using at_most_one_request_timeout'_cons_neq with datatypes.
           ++ exfalso; find_eapply_prop In.
              unfold timeouts_in; repeat find_rewrite.
              repeat break_let; simpl; left; congruence.
           ++ exfalso; find_eapply_prop In.
              unfold timeouts_in; repeat find_rewrite.
              repeat break_let; simpl; left; congruence.
  - repeat find_rewrite; rewrite_update; eauto.
Qed.
Hint Resolve cur_request_timeouts_related_recv_invariant.

(* TODO(ryan) move to handlerlemmas *)
Lemma init_state_preset_definition :
  forall h p succs st,
    init_state_preset h p succs = st ->
    ptr st = make_pointer h /\
    pred st = p /\
    succ_list st = succs /\
    known st = make_pointer h /\
    joined st = true /\
    rectify_with st = None /\
    cur_request st = None /\
    delayed_queries st = nil.
Proof.
  unfold init_state_preset; intros.
  repeat find_reverse_rewrite; tauto.
Qed.

Lemma cur_request_timeouts_related_init :
  forall gst,
    initial_st gst ->
    all_nodes_cur_request_timeouts_related gst.
Proof.
  unfold initial_st.
  autounfold; intros; break_and.
  pose proof (start_handler_init_state_preset h (nodes gst)).
  pose proof succ_list_len_lower_bound.
  forwards. omega. concludes.
  find_copy_apply_hyp_hyp; break_and.
  constructor 1.
  - intros; repeat find_rewrite.
    simpl; intuition congruence.
  - match goal with
    | H : sigma gst h = Some ?stdef |- _ =>
      let Heq := fresh in
      assert (Heq: stdef = st) by congruence;
        apply init_state_preset_definition in Heq;
        tauto
    end.
Qed.
Hint Resolve cur_request_timeouts_related_init.

Lemma cur_request_timeouts_related_start :
  chord_start_invariant all_nodes_cur_request_timeouts_related.
Proof.
  do 2 autounfold; intros.
  destruct (addr_eq_dec h0 h).
  - subst.
    autorewrite with core in *.
    find_apply_lem_hyp open_pi; expand_def.
    handler_def;
      repeat find_rewrite;
      repeat handler_simpl.
    econstructor 2; eauto.
    + simpl; tauto.
  - repeat find_rewrite; rewrite_update.
    assert (In h0 (nodes gst))
      by in_crush.
    eauto.
Qed.
Hint Resolve cur_request_timeouts_related_start.

Lemma cur_request_timeouts_related_fail :
  chord_fail_invariant all_nodes_cur_request_timeouts_related.
Proof.
  do 2 autounfold; intros.
  destruct (addr_eq_dec h0 h);
    repeat find_rewrite; eauto with datatypes.
Qed.
Hint Resolve cur_request_timeouts_related_fail.

Lemma cur_request_timeouts_related_tick :
  chord_tick_invariant all_nodes_cur_request_timeouts_related.
Proof.
  do 2 autounfold; intros.
  repeat find_rewrite.
  destruct_update; rewrite_update; eauto with datatypes.
  assert (cur_request_timeouts_ok' (cur_request st) (timeouts gst h0))
    by auto.
  apply cur_request_timeouts_ok'_sound.
  repeat (handler_def || handler_simpl);
    repeat find_rewrite;
    inv_prop cur_request_timeouts_ok';
    try (unfold option_map in *; break_match; congruence || find_injection);
    eauto.
  - constructor; eauto; intros; in_crush.
    eapply at_most_one_request_timeout'_cons_neq; auto.
    eapply at_most_one_request_timeout'_cons; eauto.
    intros; in_crush.
    eauto using in_remove.
  - constructor; eauto; intros.
    in_crush; [congruence|eauto using in_remove].
  - constructor; eauto; intros.
    in_crush; eauto using remove_preserve.
  - constructor; eauto; intros.
    in_crush; [congruence|eauto using in_remove].
  - constructor; eauto; intros.
    in_crush; eauto using remove_preserve.
Qed.
Hint Resolve cur_request_timeouts_related_tick.

Lemma cur_request_timeouts_related_keepalive :
  chord_keepalive_invariant all_nodes_cur_request_timeouts_related.
Proof.
  do 2 autounfold; intros.
  repeat find_rewrite.
  destruct_update; rewrite_update; eauto with datatypes.
  assert (cur_request_timeouts_ok' (cur_request st) (timeouts gst h0))
    by auto.
  apply cur_request_timeouts_ok'_sound.
  repeat (handler_def || handler_simpl).
  inv_prop cur_request_timeouts_ok';
    subst; constructor; intros; in_crush;
      congruence || eauto using in_remove, remove_preserve.
Qed.
Hint Resolve cur_request_timeouts_related_keepalive.

Lemma cur_request_timeouts_related_rectify :
  chord_rectify_invariant all_nodes_cur_request_timeouts_related.
Proof.
  do 2 autounfold; intros.
  repeat find_rewrite.
  destruct_update; rewrite_update; eauto with datatypes.
  assert (cur_request_timeouts_ok' (cur_request st) (timeouts gst h0))
    by auto.
  apply cur_request_timeouts_ok'_sound.
  repeat (handler_def || handler_simpl);
    inv_prop cur_request_timeouts_ok';
    subst; constructor; intros; in_crush;
      congruence || eauto using in_remove, remove_preserve;
      unfold option_map in *; break_match; try congruence;
        repeat find_injection;
        eauto.
  erewrite timeouts_in_None.
  simpl.
  eapply at_most_one_request_timeout'_cons.
  intros; in_crush.
  eauto using in_remove.
  unfold clear_rectify_with.
  repeat find_rewrite; auto.
Qed.
Hint Resolve cur_request_timeouts_related_rectify.

Lemma make_request_query_request :
  forall h st q dstp m,
    make_request h st q = Some (dstp, m) ->
    query_request q m.
Proof.
  unfold make_request, option_map.
  intros; repeat break_match;
    solve [congruence | find_injection; eauto].
Qed.
Hint Resolve make_request_query_request.

Lemma start_query_cur_requests_timeouts_ok' :
  forall ts h st q st' ms nts cts,
    cur_request_timeouts_ok' (cur_request st) ts ->
    start_query h st q = (st', ms, nts, cts) ->
    cur_request_timeouts_ok' (cur_request st')
                             (nts ++ remove_all timeout_eq_dec cts ts).
Proof.
  intros.
  handler_def.
  repeat (handler_def || handler_simpl).
  - invcs_prop cur_request_timeouts_ok';
      repeat handler_simpl; eauto with datatypes.
    + erewrite timeouts_in_None; eauto with datatypes.
    + constructor; eauto with datatypes.
      erewrite timeouts_in_Some by eauto.
      eapply at_most_one_request_timeout'_swap; eauto.
  - invcs_prop cur_request_timeouts_ok'.
      repeat handler_simpl; eauto with datatypes.
    + erewrite timeouts_in_None; eauto with datatypes.
    + constructor; eauto with datatypes.
      erewrite timeouts_in_Some by eauto.
      eauto using at_most_one_request_timeout'_remove_drops_all.
Qed.

Lemma cur_request_timeouts_related_request :
  chord_request_invariant all_nodes_cur_request_timeouts_related.
Proof.
  autounfold; intros; subst.
  destruct (addr_eq_dec h0 h); subst.
  - repeat find_rewrite.
    + assert (cur_request_timeouts_ok (cur_request st) (timeouts gst h))
        by auto.
      assert (at_most_one_request_timeout' (timeouts gst h)).
      {
        inv_prop cur_request_timeouts_ok; [|eauto].
        unfold at_most_one_request_timeout'; intros.
        repeat find_rewrite.
        exfalso; unfold not in *; eauto with datatypes.
      }
      apply cur_request_timeouts_ok'_sound.
      repeat (handler_def || handler_simpl || rewrite_update);
        try solve [constructor;
                   intros;
                   rewrite remove_comm;
                   assert (In (Request (addr_of x) req) (timeouts gst h))
                     by (inv_prop cur_request_timeouts_ok; congruence);
                   intro;
                   rewrite remove_comm in *;
                   do 2 find_apply_lem_hyp in_remove;
                   eapply at_most_one_request_timeout'_remove_drops_all; eauto].
      * unfold hd_error in *; break_match; simpl in *; try congruence.
        find_injection.
        constructor; eauto with datatypes.
        eapply at_most_one_request_timeout'_cons.
        intros; intro.
        find_apply_lem_hyp in_remove.
        eapply at_most_one_request_timeout'_remove_drops_all; eauto.
      * invcs_prop cur_request_timeouts_ok; try congruence.
        assert (Request (addr_of dstp) req0 = Request dst req)
          by eauto.
        congruence.
      * find_rewrite.
        inv_prop cur_request_timeouts_ok; try congruence.
        repeat find_rewrite.
        constructor.
        intros; intro.
        find_apply_lem_hyp in_remove.
        intuition eauto.
  - repeat find_rewrite; rewrite_update.
    assert (In h0 (nodes gst))
      by in_crush.
    eauto.
Qed.
Hint Resolve cur_request_timeouts_related_request.

Lemma cur_request_timeouts_related_input :
  chord_input_invariant all_nodes_cur_request_timeouts_related.
Proof.
  do 2 autounfold; intros.
  repeat find_rewrite; eauto.
Qed.
Hint Resolve cur_request_timeouts_related_input.

Lemma cur_request_timeouts_related_output :
  chord_output_invariant all_nodes_cur_request_timeouts_related.
Proof.
  do 2 autounfold; intros.
  repeat find_rewrite; eauto.
Qed.
Hint Resolve cur_request_timeouts_related_output.

Lemma cur_request_timeouts_related_invariant :
  forall gst,
    reachable_st gst ->
    all_nodes_cur_request_timeouts_related gst.
Proof.
  apply chord_net_invariant; eauto.
Qed.

Lemma cur_request_timeouts_related_invariant_elim :
  forall gst,
    reachable_st gst ->
    forall h st,
      In h (nodes gst) ->
      sigma gst h = Some st ->
      cur_request_timeouts_ok (cur_request st) (timeouts gst h).
Proof.
  firstorder using cur_request_timeouts_related_invariant.
Qed.
Hint Resolve cur_request_timeouts_related_invariant_elim.

Definition no_requests (chan : list payload) : Prop :=
  forall m,
    In m chan ->
    ~ request_payload m.

Definition no_responses (chan : list payload) : Prop :=
  forall m,
    In m chan ->
    ~ response_payload m.

Inductive query_message_ok
  (src : addr)
  : addr ->
    option (pointer * query * payload) ->
    list (addr * payload) ->
    list payload ->
    list payload ->
    Prop :=
| CInone :
    forall dst outbound inbound dqs,
      no_responses inbound ->
      no_requests outbound ->
      (forall m, ~ In (src, m) dqs) ->
      query_message_ok src dst None dqs outbound inbound
| CIother :
    forall dst dstp q req dqs outbound inbound,
      dst <> (addr_of dstp) ->
      no_responses inbound ->
      no_requests outbound ->
      (forall m, ~ In (src, m) dqs) ->
      query_request q req ->
      query_message_ok src dst (Some (dstp, q, req)) dqs outbound inbound
| CIreq :
    forall outbound inbound dqs dstp q req,
      In req outbound ->
      (forall xs ys, outbound = xs ++ req :: ys -> no_requests (xs ++ ys)) ->
      no_responses inbound ->
      (forall m, ~ In (src, m) dqs) ->
      query_request q req ->
      query_message_ok src (addr_of dstp) (Some (dstp, q, req)) dqs outbound inbound
| CIres :
    forall outbound inbound res dqs dstp q req,
      request_response_pair req res ->
      In res inbound ->
      (forall xs ys, inbound = xs ++ res :: ys -> no_responses (xs ++ ys)) ->
      no_requests outbound ->
      (forall m, ~ In (src, m) dqs) ->
      query_request q req ->
      query_message_ok src (addr_of dstp) (Some (dstp, q, req)) dqs outbound inbound
| CIdelayed :
    forall outbound inbound dqs dstp q req,
      In (src, req) dqs ->
      is_safe req = false ->
      (forall xs ys req', dqs = xs ++ (src, req) :: ys -> ~ In (src, req') (xs ++ ys)) ->
      no_responses inbound ->
      no_requests outbound ->
      query_request q req ->
      query_message_ok src (addr_of dstp) (Some (dstp, q, req)) dqs outbound inbound.

(* handles failed nodes accurately *)
Inductive query_message_ok'
  (src : addr)
  : addr ->
    option (pointer * query * payload) ->
    option (list (addr * payload)) ->
    list addr ->
    list addr ->
    list payload ->
    list payload ->
    Prop :=
| QMLive :
    forall dst outbound inbound active failed dqs cr,
      In dst active ->
      ~ In dst failed ->
      query_message_ok src dst cr dqs outbound inbound ->
      query_message_ok' src dst cr (Some dqs) active failed outbound inbound
| QMFailedRes :
    forall outbound inbound res dqs dstp q active failed req,
      In (addr_of dstp) active ->
      In (addr_of dstp) failed ->
      request_response_pair req res ->
      In res inbound ->
      (forall xs ys, inbound = xs ++ res :: ys -> no_responses (xs ++ ys)) ->
      no_requests outbound ->
      (forall m, ~ In (src, m) dqs) ->
      query_request q req ->
      query_message_ok' src (addr_of dstp) (Some (dstp, q, req)) (Some dqs) active failed outbound inbound
| QMFailedNothing :
    forall dst outbound inbound active failed cr dqs,
      In dst active ->
      In dst failed ->
      no_responses inbound ->
      (forall dstp q m,
          cr = Some (dstp, q, m) ->
          query_request q m) ->
      query_message_ok' src dst cr (Some dqs) active failed outbound inbound
| QMNotStarted :
    forall dst cr active failed,
      ~ In dst active ->
      ~ client_addr dst ->
      (forall dstp q m,
          cr = Some (dstp, q, m) ->
          query_request q m /\
          addr_of dstp <> dst) ->
      query_message_ok' src dst cr None active failed [] []
| QMClient :
    forall dst cr active failed outbound inbound,
      client_addr dst ->
      (forall p, In p inbound -> client_payload p) ->
      (forall p, In p outbound -> p = Busy \/ response_payload p) ->
      query_message_ok' src dst cr None active failed outbound inbound.

Definition unique {A : Type} (P : A -> Prop) (l : list A) (a : A) : Prop :=
  P a /\
  forall xs ys,
    l = xs ++ a :: ys ->
    forall b,
      In b (xs ++ ys) ->
      ~ P b.

Lemma no_responses_unique :
  forall l res,
    response_payload res ->
    (forall xs ys, l = xs ++ res :: ys -> no_responses (xs ++ ys)) ->
    unique response_payload l res.
Proof.
  unfold unique, no_responses.
  intros.
  eauto.
Qed.

Lemma unique_no_responses :
  forall l res,
    unique response_payload l res ->
    (forall xs ys, l = xs ++ res :: ys -> no_responses (xs ++ ys)).
Proof.
  unfold unique, no_responses.
  intros.
  intuition eauto.
Qed.

Lemma no_requests_unique :
  forall l res,
    request_payload res ->
    (forall xs ys, l = xs ++ res :: ys -> no_requests (xs ++ ys)) ->
    unique request_payload l res.
Proof.
  unfold unique, no_requests.
  intros.
  eauto.
Qed.

Lemma unique_no_requests :
  forall l res,
    unique request_payload l res ->
    (forall xs ys, l = xs ++ res :: ys -> no_requests (xs ++ ys)).
Proof.
  unfold unique, no_requests.
  intros.
  intuition eauto.
Qed.

Lemma unique_cons :
  forall {A : Type} (P : A -> Prop) l u x,
    unique P l u ->
    ~ P x ->
    unique P (x :: l) u.
Proof.
  unfold unique.
  intros.
  intuition.
  destruct xs.
  - simpl in *; find_injection; tauto.
  - simpl in *; find_injection.
    break_or_hyp; eauto.
Qed.

Lemma unique_cons_add :
  forall {A : Type} (P : A -> Prop) l x,
    (forall y, In y l -> ~ P y) ->
    P x ->
    unique P (x :: l) x.
Proof.
  unfold unique.
  intros.
  intuition.
  destruct xs.
  - simpl in *; find_injection; eauto.
  - simpl in *; find_injection.
    break_or_hyp; subst; find_eapply_prop False; in_crush.
Qed.

Lemma unique_app :
  forall {A : Type} (P : A -> Prop) xs ys x,
    unique P xs x ->
    (forall y, In y ys -> ~ P y) ->
    unique P (ys ++ xs) x.
Proof.
  induction ys; intros.
  - assumption.
  - simpl.
    apply unique_cons; in_crush; eauto.
Qed.

Lemma unique_perm :
  forall {A : Type} (P : A -> Prop) xs xs' x,
    unique P xs x ->
    Permutation.Permutation xs xs' ->
    unique P xs' x.
Proof.
  intros.
  unfold unique in *.
  break_and; split.
  intuition.
  intros.
  assert (In x xs)
    by eauto using Permutation.Permutation_in, Permutation.Permutation_sym.
  find_copy_apply_lem_hyp in_split; expand_def.
  assert (In b (x0 ++ x1)).
  eauto using Permutation.Permutation_in, Permutation.Permutation_sym, Permutation.Permutation_app_inv.
  eauto.
Qed.

Lemma unique_app_comm :
  forall {A : Type} (P : A -> Prop) xs ys x,
    unique P (xs ++ ys) x ->
    unique P (ys ++ xs) x.
Proof.
  intros.
  eapply unique_perm;
    eauto using Permutation.Permutation_app_comm, Permutation.Permutation_refl.
Qed.

Lemma unique_app_r :
  forall {A : Type} (P : A -> Prop) xs ys x,
    unique P xs x ->
    (forall y, In y ys -> ~ P y) ->
    unique P (xs ++ ys) x.
Proof.
  intros.
  apply unique_app_comm.
  apply unique_app; auto.
Qed.

Lemma unique_app_none :
  forall {A : Type} (P : A -> Prop) xs ys x,
    unique P xs x ->
    (forall y, In y ys -> ~ P y) ->
    unique P (ys ++ xs) x.
Proof.
  induction ys; intros.
  - assumption.
  - simpl.
    apply unique_cons; in_crush; eauto.
Qed.


Lemma initial_nodes_not_failed :
  forall gst,
    initial_st gst ->
    forall h,
      ~ In h (failed_nodes gst).
Proof.
  intros.
  inv_prop initial_st; break_and.
  repeat find_rewrite; auto.
Qed.
Hint Resolve initial_nodes_not_failed.

Lemma initial_st_timeouts_Tick :
  forall gst,
    initial_st gst ->
    forall h,
      In h (nodes gst) ->
      timeouts gst h = [Tick].
Proof.
  intros; inv_prop initial_st; break_and.
  repeat match goal with
         | H: _ |- _ =>
           specialize (H h)
         end.
  destruct (In_dec addr_eq_dec h (nodes gst)).
  - destruct (start_handler h (nodes gst)) as [[?st ?ms] ?nts] eqn:?.
    assert (timeouts gst h = nts)
      by match goal with
         | H: _ |- _ => eapply H; eauto
         end.
    rewrite start_handler_init_state_preset in *;
      try congruence.
    pose proof succ_list_len_lower_bound; omega.
  - congruence.
Qed.
Hint Resolve initial_st_timeouts_Tick.

Lemma initial_st_cur_request_dqs_empty :
  forall gst,
    initial_st gst ->
    forall h st,
      sigma gst h = Some st ->
      cur_request st = None /\
      delayed_queries st = [].
Proof.
  intros; inv_prop initial_st; break_and.
  repeat match goal with
         | H: _ |- _ =>
           specialize (H h)
         end.
  destruct (In_dec addr_eq_dec h (nodes gst)).
  - destruct (start_handler h (nodes gst)) as [[st__h ?ms] ?nts] eqn:?.
    assert (sigma gst h = Some st__h)
      by match goal with
         | H: _ |- _ => eapply H; eauto
         end.
    repeat find_rewrite || find_injection.
    rewrite start_handler_init_state_preset in *.
    + find_injection; split; reflexivity.
    + pose proof succ_list_len_lower_bound; omega.
  - find_apply_hyp_hyp; congruence.
Qed.

Lemma initial_st_cur_request_None :
  forall gst,
    initial_st gst ->
    forall h st,
      sigma gst h = Some st ->
      cur_request st = None.
Proof.
  intros.
  eapply initial_st_cur_request_dqs_empty; eauto.
Qed.
Hint Resolve initial_st_cur_request_None.

Lemma initial_st_delayed_queries_empty :
  forall gst,
    initial_st gst ->
    forall h st,
      sigma gst h = Some st ->
      delayed_queries st = [].
Proof.
  intros.
  eapply initial_st_cur_request_dqs_empty; eauto.
Qed.
Hint Resolve initial_st_delayed_queries_empty.

Lemma initial_st_channels_empty :
  forall gst,
    initial_st gst ->
    forall src dst,
      channel gst src dst = [].
Proof.
  intros; inv_prop initial_st; break_and.
  unfold channel.
  repeat find_rewrite.
  reflexivity.
Qed.
Hint Resolve initial_st_channels_empty.

Lemma msgs_eq_channels_eq :
  forall gst gst',
    msgs gst = msgs gst' ->
    forall a b,
      channel gst a b = channel gst' a b.
Proof.
  unfold channel; congruence.
Qed.

Lemma channel_msgs_cons :
  forall gst' gst src dst new,
    msgs gst' = send src (dst, new) :: msgs gst ->
    channel gst' src dst = new :: channel gst src dst.
Proof.
  unfold channel.
  intros.
  repeat find_rewrite.
  simpl.
  repeat match goal with
         | |- context[addr_eq_dec ?x ?y] =>
           destruct (addr_eq_dec x y);
             simpl;
             try congruence
         end.
Qed.

Lemma channel_msgs_unchanged :
  forall ms gst' gst src dst h,
    msgs gst' = map (send h) ms ++ msgs gst ->
    (src <> h \/ forall d m, In (d, m) ms -> d <> dst) ->
    channel gst' src dst = channel gst src dst.
Proof.
  intros.
  unfold channel.
  remember (msgs gst) as l.
  remember (msgs gst') as l'.
  clear Heql Heql' gst gst'.
  generalizeEverythingElse ms.
  induction ms; intros.
  - simpl in *; congruence.
  - repeat find_rewrite.
    simpl in *.
    destruct (addr_eq_dec h src), (addr_eq_dec (fst a) dst).
    + destruct a; subst; simpl in *.
      exfalso; intuition eauto.
    + simpl; intuition eauto.
    + simpl; intuition eauto.
    + simpl; intuition eauto.
Qed.

Lemma channel_msgs_remove_unchanged :
  forall gst' gst xs ys m src dst,
    msgs gst' = xs ++ ys ->
    msgs gst = xs ++ m :: ys ->
    fst m <> src \/ fst (snd m) <> dst ->
    channel gst' src dst = channel gst src dst.
Proof.
  intros.
  unfold channel.
  repeat find_rewrite.
  repeat rewrite filterMap_app.
  f_equal.
  simpl.
  destruct (addr_eq_dec (fst m) src), (addr_eq_dec (fst (snd m)) dst);
    intuition congruence || auto.
Qed.

Lemma channel_msgs_remove_send_unchanged :
  forall gst gst' xs ys m src dst,
    msgs gst = xs ++ m :: ys ->
    forall h ms,
      msgs gst' = map (send h) ms ++ xs ++ ys ->
      fst m <> src \/ fst (snd m) <> dst ->
      h <> src \/ (forall s p, In (s, p) ms -> s <> dst) ->
      channel gst' src dst = channel gst src dst.
Proof.
  intros.
  unfold channel.
  repeat find_rewrite.
  repeat rewrite filterMap_app.
  match goal with
  | |- ?xs ++ ?rest = _ =>
    assert (xs = nil)
  end.
  {
    eapply filterMap_all_None.
    intros.
    find_apply_lem_hyp in_map_iff.
    break_exists_name pk; destruct pk; break_and.
    unfold send in *; subst.
    simpl in *.
    destruct (addr_eq_dec h src), (addr_eq_dec a dst); simpl; auto.
    subst; break_or_hyp; try congruence.
    find_apply_hyp_hyp; congruence.
  }
  repeat find_rewrite.
  simpl ([] ++ _).
  f_equal; auto.
  simpl.
  destruct (addr_eq_dec (fst m) src), (addr_eq_dec (fst (snd m)) dst);
    simpl; auto.
  intuition congruence.
Qed.

Lemma uniq_list_eq :
  forall A (A_eq_dec : forall (x y : A), {x = y} + {x <> y}) P l (a b : A),
    In a l ->
    In b l ->
    P a ->
    P b ->
    (forall xs ys, l = xs ++ a :: ys -> forall z, P z -> ~ In z (xs ++ ys)) ->
    a = b.
Proof.
  intros.
  repeat find_apply_lem_hyp in_split; expand_def.
  do 2 find_insterU.
  forwards; eauto. concludes.
  find_insterU.
  destruct (A_eq_dec a b); auto.
  exfalso.
  find_eapply_prop In; try find_eapply_prop (P b).
  eauto using in_middle_reduce, app_cons_in.
Qed.

Lemma splits_uniq_eq :
  forall A (P : A -> Prop) l xs ys xs' ys' a,
    l = xs ++ a :: ys ->
    l = xs' ++ a :: ys' ->
    P a ->
    (forall z, P z -> ~ In z (xs ++ ys)) ->
    xs = xs' /\ ys = ys'.
Proof.
  intros.
  copy_eapply_prop_hyp P P; eauto.
  generalizeEverythingElse l.
  induction l; intros.
  - exfalso; eapply app_cons_not_nil; eauto.
  - destruct xs eqn:?, xs' eqn:?.
    + simpl in *; split; congruence.
    + simpl in *.
      repeat find_injection.
      exfalso; eauto using app_cons_in.
    + simpl in *.
      exfalso.
      repeat find_injection.
      eauto using app_cons_in.
    + simpl in *.
      repeat find_injection.
      cut (l0 = l1 /\ ys = ys'); [intuition congruence|].
      eapply IHl; eauto.
      intuition.
      match goal with
      | H: _ |- _ =>
        specialize (H z); eapply H; eauto
      end.
Qed.

Ltac channel_crush :=
  repeat match goal with
         | a: msg |- _ => destruct a; simpl in *; subst
         | a: _ * _ |- _ => destruct a; simpl in *; subst
         | H: _ /\ _ |- _ => destruct H
         | H: _ \/ _ |- _ => destruct H
         | H: In _ (_ ++ _) |- _ => apply in_app_or in H
         | H: In _ (map _ _) |- _ =>
           apply in_map_iff in H; destruct H
         | H: In _ (filterMap _ _) |- _ =>
           apply In_filterMap in H; destruct H
         | H: context[addr_eq_dec ?x ?y] |- _ =>
           destruct (addr_eq_dec x y); simpl in H; try congruence
         | H: _ = _ |- _ => progress injc H
         | |- _ => progress subst_max
         | |- _ => tauto
         end.

Theorem channel_msgs_app_in :
  forall gst' gst h src dst m ms,
    msgs gst' = (map (send h) ms) ++ msgs gst ->
    In m (channel gst' src dst) ->
    In m (channel gst src dst) \/
    h = src /\
    In (dst, m) ms.
Proof.
  unfold channel.
  intros; find_rewrite.
  rewrite filterMap_app in *.
  find_apply_lem_hyp in_app_or; break_or_hyp;
    solve [channel_crush | tauto].
Qed.

Lemma handle_delayed_query_dst_in_dqs :
  forall h st l dst p,
    In (dst, p) (concat (map (handle_delayed_query h st) l)) ->
    exists r,
      request_response_pair r p /\
      In (dst, r) l.
Proof.
  intros.
  find_apply_lem_hyp in_concat; expand_def; in_crush.
  unfold handle_delayed_query, handle_query_req in *.
  repeat break_match; repeat handler_simpl;
    try solve [intuition eauto
              |eexists; split; eauto; constructor].
Qed.

Lemma handle_query_res_sends_no_responses :
  forall src dst st q p st' ms nts cts h m,
    handle_query_res src dst st q p = (st', ms, nts, cts) ->
    In (h, m) ms ->
    ~ response_payload m.
Proof.
  intuition.
  repeat handler_def || handler_simpl;
    inv_prop response_payload.
Qed.

Lemma handle_msg_dqs_change_queue_for_reqs :
  forall src dst st p st' ms nts cts,
    handle_msg src dst st p = (st', ms, nts, cts) ->
    delayed_queries st' <> delayed_queries st ->
    delayed_queries st' = dedup send_eq_dec ((src, p) :: delayed_queries st) /\
    request_payload p /\
    is_safe p = false.
Proof.
  intros.
  repeat (handler_def || handler_simpl); repeat split;
    solve [eauto
          |apply is_request_same_as_request_payload; eauto
          |destruct p; simpl in *; congruence].
Qed.

Lemma handle_msg_dqs_change_queue :
  forall src dst st p st' ms nts cts,
    handle_msg src dst st p = (st', ms, nts, cts) ->
    delayed_queries st' <> delayed_queries st ->
    delayed_queries st' = dedup send_eq_dec ((src, p) :: delayed_queries st).
Proof.
  intros.
  eapply handle_msg_dqs_change_queue_for_reqs; eauto.
Qed.

Lemma in_dqs_preserved_by_handle_msg :
  forall src dst st p st' ms nts cts,
    handle_msg src dst st p = (st', ms, nts, cts) ->
    forall x,
      In x (delayed_queries st) ->
      In x (delayed_queries st').
Proof.
  intros.
  destruct (list_eq_dec send_eq_dec
                        (delayed_queries st)
                        (delayed_queries st')).
  - congruence.
  - find_apply_lem_hyp handle_msg_dqs_change_queue; auto.
    repeat find_rewrite.
    apply dedup_In.
    in_crush.
Qed.

Ltac chan2msg :=
  repeat match goal with
         | |- In _ (channel _ _ _) =>
           apply in_msgs_in_channel
         | H: In _ (channel _ _ _) |- _ =>
           apply in_channel_in_msgs in H
         end.

Ltac inv_option_map :=
  repeat match goal with
         | H: option_map _ _ = Some _ |- _ =>
           apply option_map_Some in H; expand_def
         | H: option_map _ _ = None |- _ =>
           apply option_map_None in H
         | H: Some _ = option_map _ _ |- _ =>
           symmetry in H
         | H: None = option_map _ _ |- _ =>
           symmetry in H
         end.

Lemma channel_app :
  forall gst gst' src dst ms,
    msgs gst' = map (send src) ms ++ msgs gst ->
    channel gst' src dst = filterMap (fun m => if addr_eq_dec (fst m) dst
                                            then Some (snd m)
                                            else None) ms
                               ++ channel gst src dst.
Proof.
  unfold channel.
  intros until 0.
  generalize (msgs gst').
  generalize (msgs gst).
  clear gst gst'.
  induction ms; intros.
  - simpl in *; congruence.
  - repeat find_rewrite.
    rewrite filterMap_app.
    f_equal.
    unfold send in *.
    simpl in *.
    replace (ssrbool.is_left (addr_eq_dec src src)) with true in *.
    simpl.
    destruct (addr_eq_dec (fst a) dst).
    + simpl.
      f_equal.
      erewrite IHms;
        [|symmetry; eapply app_nil_r].
      simpl.
      rewrite app_nil_r; auto.
    + simpl.
      erewrite IHms;
        [|symmetry; eapply app_nil_r].
      simpl.
      rewrite app_nil_r; auto.
    + unfold ssrbool.is_left; break_if; try congruence.
Qed.

Lemma handle_msg_preserves_cur_request_None :
  forall src dst st p st' ms nts cts,
    handle_msg src dst st p = (st', ms, nts, cts) ->
    cur_request st = None ->
    cur_request st' = None.
Proof.
  intros.
  repeat handler_def || handler_simpl.
Qed.
Hint Resolve handle_msg_preserves_cur_request_None.

Lemma do_delayed_queries_preserves_cur_request_None :
  forall h st st' ms nts cts,
    do_delayed_queries h st = (st', ms, nts, cts) ->
    cur_request st = None ->
    cur_request st' = None.
Proof.
  intros.
  repeat handler_def || handler_simpl.
Qed.
Hint Resolve do_delayed_queries_preserves_cur_request_None.

Lemma handle_msg_sets_cur_request_when_sending_request :
  forall src dst st p st' ms nts cts,
    handle_msg src dst st p = (st', ms, nts, cts) ->
    forall h m,
      In (h, m) ms ->
      request_payload m ->
      exists dstp q m,
        cur_request st' = Some (dstp, q, m) /\
        addr_of dstp = h /\
        query_request q m.
Proof.
  intros.
  repeat handler_def || handler_simpl; inv_prop request_payload;
    try solve [repeat eexists; eauto
              |find_apply_lem_hyp handle_query_req_only_sends_responses; exfalso; eauto].
Qed.

Lemma responses_from_only_one_node :
  forall gst,
    (forall src dst st__src,
        sigma gst src = Some st__src ->
        query_message_ok' src dst (cur_request st__src)
                          (option_map delayed_queries (sigma gst dst)) (nodes gst) (failed_nodes gst)
                          (channel gst src dst) (channel gst dst src)) ->
    forall src dst dstp st q m res,
      sigma gst src = Some st ->
      cur_request st = Some (dstp, q, m) ->
      response_payload res ->
      In res (channel gst dst src) ->
      dst = addr_of dstp.
Proof.
  intros.
  find_copy_apply_lem_hyp in_split; expand_def.
  assert (query_message_ok' src dst (cur_request st)
                            (option_map delayed_queries (sigma gst dst)) (nodes gst) (failed_nodes gst)
                            (channel gst src dst) (channel gst dst src))
    by eauto.
  inv_prop query_message_ok'.
  - repeat find_rewrite; inv_prop query_message_ok; try congruence.
    exfalso; find_eapply_prop no_responses; eauto.
  - congruence.
  - exfalso; find_eapply_prop no_responses; eauto.
  - repeat find_reverse_rewrite; in_crush.
  - assert (client_payload res0) by eauto; inv_prop client_payload; inv_prop response_payload.
Qed.

Lemma unique_eq :
  forall A (P : A -> Prop) l x y,
    unique P l y ->
    (forall (a b : A), {a = b} + {a <> b}) ->
    P x ->
    In x l ->
    In y l ->
    x = y.
Proof.
  unfold unique; intuition.
  find_apply_lem_hyp in_split; expand_def.
  match goal with
  | H: _ |- _ =>
    do 2 insterU H;
      conclude H reflexivity;
      specialize (H x)
  end.
  in_crush; exfalso; in_crush.
Qed.

Lemma unique_from_src :
  forall src req dqs,
    (forall xs ys req',
        dqs = xs ++ (src, req) :: ys ->
        ~ In (src, req') (xs ++ ys)) ->
    unique (fun (m : addr * payload) => fst m = src) dqs (src, req).
Proof.
  unfold unique; intros; intuition eauto.
  destruct b; simpl in *; subst.
  find_eapply_prop In; eauto.
Qed.
Hint Resolve unique_from_src.

Lemma from_src_unique :
  forall src req dqs,
    unique (fun (m : addr * payload) => fst m = src) dqs (src, req) ->
    (forall xs ys req',
        dqs = xs ++ (src, req) :: ys ->
        ~ In (src, req') (xs ++ ys)).
Proof.
  unfold unique; intuition eauto.
Qed.
Hint Resolve from_src_unique.

Lemma delayed_query_means_channels_empty :
  forall gst src dst st__src st,
    sigma gst src = Some st__src ->
    sigma gst dst = Some st ->
    query_message_ok src dst (cur_request st__src) (delayed_queries st)
                     (channel gst src dst) (channel gst dst src) ->
    forall req,
      In (src, req) (delayed_queries st) ->
      exists dstp q m,
        is_safe req = false /\
        cur_request st__src = Some (dstp, q, m) /\
        unique (fun m => fst m = src) (delayed_queries st) (src, req) /\
        query_request q req /\
        addr_of dstp = dst /\
        no_responses (channel gst dst src) /\
        no_requests (channel gst src dst).
Proof.
  intros.
  inv_prop query_message_ok;
    try solve [exfalso; intuition eauto].
  assert (unique (fun m => fst m = src) (delayed_queries st) (src, req0))
    by eauto.
  assert ((src, req) = (src, req0)).
  {
    eapply (unique_eq (addr * payload) (fun m => fst m = src));
      eauto using prod_eq_dec, addr_eq_dec, payload_eq_dec.
  }
  find_injection.
  do 3 eexists; intuition.
Qed.

Lemma filterMap_of_map :
  forall A B C (f : A -> B) (g : B -> option C),
    forall l,
      filterMap g (map f l) = filterMap (fun b => g (f b)) l.
Proof.
  induction l.
  simpl; auto.
  simpl; repeat find_rewrite; auto.
Qed.

Theorem channel_after_recv_src_dst :
  forall gst gst' src dst p ms xs ys,
    msgs gst = xs ++ (src, (dst, p)) :: ys ->
    msgs gst' = map (send dst) ms ++ xs ++ ys ->
    exists xs' ys',
      channel gst src dst = xs' ++ p :: ys' /\
      channel gst' src dst =
      filterMap (fun m =>
                   if (addr_eq_dec src dst)
                   then if (addr_eq_dec (fst m) src)
                        then Some (snd m)
                        else None
                   else None)
                ms ++ xs' ++ ys'.
Proof.
  intros.
  unfold channel.
  repeat find_rewrite.
  rewrite !filterMap_app.
  exists (filterMap
       (fun m : addr * (addr * payload) =>
          if
            (ssrbool.is_left (addr_eq_dec (fst m) src) &&
         ssrbool.is_left (addr_eq_dec (fst (snd m)) dst))%bool
       then Some (snd (snd m))
       else None) xs).
  exists (filterMap
       (fun m : addr * (addr * payload) =>
          if
            (ssrbool.is_left (addr_eq_dec (fst m) src) &&
         ssrbool.is_left (addr_eq_dec (fst (snd m)) dst))%bool
       then Some (snd (snd m))
       else None) ys).
  split.
  - f_equal; eauto.
    simpl.
    repeat destruct (addr_eq_dec _ _); simpl; try congruence.
  - f_equal.
    rewrite filterMap_of_map.
    eapply filterMap_ext; intros [a b].
    repeat destruct (addr_eq_dec _ _); simpl in *; congruence.
Qed.

Theorem channel_after_recv_not_src_dst :
  forall gst gst' src dst p ms xs ys,
    msgs gst = xs ++ (src, (dst, p)) :: ys ->
    msgs gst' = map (send dst) ms ++ xs ++ ys ->
    forall from to,
      (from, to) <> (src, dst) ->
      channel gst' from to =
      filterMap (fun m =>
                   if (addr_eq_dec dst from)
                   then if (addr_eq_dec (fst m) to)
                        then Some (snd m)
                        else None
                   else None)
                ms ++ channel gst from to.
Proof.
  intros.
  unfold channel.
  repeat find_rewrite.
  rewrite !filterMap_app.
  f_equal.
  - rewrite filterMap_of_map; simpl.
    eapply filterMap_ext; intros [a b].
    repeat destruct (addr_eq_dec _ _); simpl in *; congruence.
  - f_equal; eauto.
    simpl.
    do 2 destruct (addr_eq_dec _ _); simpl; congruence.
Qed.


Theorem channel_after_recv_to_not_dst :
  forall gst gst' src dst p ms xs ys,
    msgs gst = xs ++ (src, (dst, p)) :: ys ->
    msgs gst' = map (send dst) ms ++ xs ++ ys ->
    forall to,
      to <> dst ->
      channel gst' dst to =
      filterMap (fun m =>
                    if (addr_eq_dec (fst m) to)
                    then Some (snd m)
                    else None)
                ms ++ channel gst dst to.
Proof.
  intros.
  unfold channel.
  repeat find_rewrite.
  rewrite !filterMap_app.
  f_equal.
  - rewrite filterMap_of_map.
    eapply filterMap_ext.
    simpl; intros.
    destruct (addr_eq_dec dst dst); try congruence.
    destruct (addr_eq_dec (fst x) to); simpl; congruence.
  - f_equal.
    simpl.
    destruct (addr_eq_dec dst to); try congruence.
    rewrite Bool.andb_false_r; reflexivity.
Qed.

Theorem channel_after_recv_unrelated :
  forall gst gst' src dst p ms xs ys,
    msgs gst = xs ++ (src, (dst, p)) :: ys ->
    msgs gst' = map (send dst) ms ++ xs ++ ys ->
    forall from to,
      from <> dst ->
      from <> src ->
      channel gst' from to = channel gst from to.
Proof.
  intros.
  unfold channel.
  repeat find_rewrite.
  rewrite !filterMap_app.
  rewrite filterMap_all_None; simpl; [|f_equal].
  - destruct (addr_eq_dec src from), (addr_eq_dec dst to); simpl in *; try congruence.
  - intro.
    rewrite in_map_iff.
    unfold send; intros; expand_def; simpl.
    repeat destruct (addr_eq_dec _ _);
      simpl in *; try congruence.
Qed.

Lemma handle_msg_res_only_if_req :
  forall src dst st p st' ms nts cts,
    handle_msg src dst st p = (st', ms, nts, cts) ->
    forall h res,
      In (h, res) ms ->
      response_payload res ->
      request_response_pair p res /\
      h = src.
Proof.
  intros.
  handler_def.
  - in_crush; find_injection; try constructor.
  - handler_def.
  - handler_def;
      in_crush; inv_prop response_payload; congruence.
  - repeat handler_def || handler_simpl; inv_prop response_payload.
  - unfold handle_query_req in *; break_match;
      in_crush; find_injection; solve [constructor | eauto].
Qed.

Lemma handle_delayed_queries_res_only_if_req :
  forall dst st st' ms nts cts,
    do_delayed_queries dst st = (st', ms, nts, cts) ->
    forall h res,
      In (h, res) ms ->
      response_payload res ->
      exists req,
        In (h, req) (delayed_queries st) /\
        request_response_pair req res.
Proof.
  intros.
  handler_def.
  find_apply_lem_hyp in_concat; expand_def.
  in_crush.
  destruct x0; simpl in *.
  exists p.
  unfold handle_query_req in *; break_match;
    in_crush; find_injection; solve [constructor | eauto].
Qed.

Lemma handle_msg_only_changes_delayed_queries_when_busy :
  forall src dst st p st' ms nts cts,
    handle_msg src dst st p = (st', ms, nts, cts) ->
    delayed_queries st' <> delayed_queries st ->
    exists x,
      cur_request st' = Some x.
Proof.
  intros.
  repeat handler_def || handler_simpl.
Qed.


Lemma handle_msg_only_appends_incoming_req_to_delayed_queries_when_busy :
  forall src dst st p st' ms nts cts,
    handle_msg src dst st p = (st', ms, nts, cts) ->
    delayed_queries st' = delayed_queries st \/
    delayed_queries st' = dedup (send_eq_dec) (delayed_queries st) \/
    delayed_queries st' = (src, p) :: dedup (send_eq_dec) (delayed_queries st) /\
    request_payload p /\
    is_safe p = false /\
    exists x, cur_request st' = Some x.
Proof.
  intros.
  repeat handler_def || handler_simpl; repeat break_match; intuition eauto;
  right; right;
    split; eauto;
      intuition eauto;
      solve [eapply is_request_same_as_request_payload; auto
            |destruct p; simpl; congruence].
Qed.

Lemma recv_handler_res_only_if_req :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    forall h res,
      In (h, res) ms ->
      response_payload res ->
      exists req,
        request_response_pair req res /\
        (p = req /\
         h = src \/
         In (h, req) (delayed_queries st)).
Proof.
  intros.
  handler_def; in_crush.
  - destruct (list_eq_dec send_eq_dec (delayed_queries st) (delayed_queries x)).
    + find_eapply_lem_hyp handle_delayed_queries_res_only_if_req; eauto; expand_def.
      repeat find_rewrite; eauto.
    + find_apply_lem_hyp handle_msg_only_changes_delayed_queries_when_busy; try congruence.
      expand_def.
      handler_def.
      congruence.
  - find_eapply_lem_hyp handle_msg_res_only_if_req; intuition eauto.
Qed.

Lemma no_requests_app :
  forall xs ys,
    no_requests xs ->
    no_requests ys ->
    no_requests (xs ++ ys).
Proof.
  unfold no_requests.
  in_crush; eauto.
Qed.

Lemma no_responses_cons :
  forall p l,
    ~ response_payload p ->
    no_responses l ->
    no_responses (p :: l).
Proof.
  unfold no_responses.
  in_crush; eauto.
Qed.

Lemma no_responses_app :
  forall xs ys,
    no_responses xs ->
    no_responses ys ->
    no_responses (xs ++ ys).
Proof.
  unfold no_responses.
  in_crush; eauto.
Qed.

Lemma unique_triv :
  forall {A} (P : A -> Prop) l,
    length l < 2 ->
    forall x, P x -> unique P l x.
Proof.
  unfold unique; intros.
  split; auto.
  intros.
  find_copy_apply_lem_hyp (f_equal (@length A)).
  destruct xs, ys; simpl in *.
  - tauto.
  - omega.
  - rewrite app_length in *; simpl in *; omega.
  - rewrite app_length in *; simpl in *; omega.
Qed.

Lemma app_no_requests :
  forall xs ys,
    no_requests (xs ++ ys) ->
    no_requests xs /\
    no_requests ys.
Proof.
Admitted.

Lemma cons_no_requests :
  forall x xs,
    no_requests (x :: xs) ->
    ~ request_payload x /\
    no_requests xs.
Proof.
Admitted.

Lemma channel_after_recv_from_not_dst :
  forall gst gst' from to src dst p ms xs ys,
    msgs gst = xs ++ (src, (dst, p)) :: ys ->
    msgs gst' = map (send dst) ms ++ xs ++ ys ->
    dst <> from ->
    forall x,
      In x (channel gst' from to) ->
      In x (channel gst from to).
Proof.
  intros.
  destruct (addr_eq_dec from src); subst.
  - unfold channel in *; find_apply_lem_hyp In_filterMap; expand_def; repeat break_match; simpl in *; try congruence.
    destruct (addr_eq_dec _ _), (addr_eq_dec _ _); simpl in *; try congruence.
    destruct x0 as [? [? ?]]; simpl in *; find_injection.
    repeat find_rewrite; in_crush.
    + unfold send in *; congruence.
    + eapply filterMap_In; [|eapply in_or_app; left; eauto].
      simpl; repeat destruct (addr_eq_dec _ _); simpl; try congruence.
    + eapply filterMap_In; [|eapply in_or_app; right; simpl; right; eauto].
      simpl; repeat destruct (addr_eq_dec _ _); simpl; try congruence.
  - erewrite <- channel_after_recv_unrelated; eauto.
Qed.

Lemma in_concat :
  forall A l (x : A) xs,
    In x xs ->
    In xs l ->
    In x (concat l).
Proof.
  induction l; intros.
  - in_crush.
  - simpl in *.
    in_crush.
    right; eauto.
Qed.

Lemma do_delayed_queries_responds :
  forall h st st' ms nts cts,
    cur_request st = None ->
    do_delayed_queries h st = (st', ms, nts, cts) ->
    forall src req,
      In (src, req) (delayed_queries st) ->
      is_safe req = false ->
      request_payload req ->
      exists res,
        In (src, res) ms /\
        request_response_pair req res.
Proof.
  intros.
  handler_def; try congruence.
  destruct (handle_query_req st src req) eqn:?.
  - unfold handle_query_req in *; break_match; inv_prop request_payload; simpl in *; try congruence.
  - find_copy_eapply_lem_hyp real_requests_get_response_handle_query_req; expand_def; eauto.
    eexists; split.
    eapply in_concat; eauto.
    eapply in_map_iff.
    eexists; eauto.
    split; eauto.
    unfold handle_delayed_query; auto.
    auto.
    destruct req; simpl in *; congruence.
Qed.

Lemma unique_cons_remove :
  forall A (P : A -> Prop) l x a,
    unique P (x :: l) a ->
    unique P l a.
Proof.
  unfold unique.
  intros; break_and; split; auto.
  intros.
  assert (In b ((x :: xs) ++ ys)) by in_crush.
  find_eapply_prop not; eauto.
  repeat find_rewrite; auto.
Qed.

Lemma unique_dedup :
  forall A (P : A -> Prop) A_eq_dec l a,
    unique P l a ->
    unique P (dedup A_eq_dec l) a.
Proof.
  induction l; eauto.
  intros.
  simpl; break_match.
  - eapply IHl.
    eapply unique_cons_remove; eauto.
  - assert (unique P (dedup A_eq_dec l) a0).
    eapply IHl; eapply unique_cons_remove; eauto.
    unfold unique in *; expand_def; auto.
    split; auto.
    induction xs; intros; simpl in *.
    + find_injection.
      assert (In b ([] ++ l))
        by eauto using in_dedup_was_in.
      find_eapply_prop (a0 :: l);
        [|eauto]; eauto.
    + break_or_hyp; subst.
      * destruct (A_eq_dec b a0).
        -- subst.
           find_injection.
           exfalso; find_eapply_prop (~ In a0 l).
           eapply in_dedup_was_in.
           replace (dedup _ l) with (xs ++ a0 :: ys) by eauto.
           in_crush.
        -- find_injection.
           assert (In a0 (b :: l)).
           simpl; right.
           eapply in_dedup_was_in.
           replace (dedup _ l) with (xs ++ a0 :: ys) by eauto.
           in_crush.
           find_copy_apply_lem_hyp in_split; expand_def.
           eapply H2; eauto.
           destruct x;
             repeat (simpl in * || find_injection || find_rewrite);
             try solve [congruence | in_crush].
      * find_injection.
        eauto.
Qed.

Lemma filterMap_sumbool_filter :
  forall A P (f : forall x:A, {P x} + {~ P x}) l,
    filterMap (fun x => if f x then Some x else None) l = filter (fun x => if f x then true else false) l.
Proof.
  induction l.
  - simpl; auto.
  - simpl; destruct (f a); eauto.
    f_equal; eauto.
Qed.

Lemma filterMap_sumbool_map_filter :
  forall A B P (f : forall x:A, {P x} + {~ P x}) (g : A -> B) l,
    filterMap (fun x => if f x then Some (g x) else None) l = map g (filter (fun x => if f x then true else false) l).
Proof.
  induction l.
  - simpl; auto.
  - simpl; destruct (f a); eauto.
    simpl; congruence.
Qed.

Lemma filter_concat :
  forall A (f : A -> bool) l,
    filter f (concat l) = concat (map (filter f) l).
Proof.
  induction l; simpl; eauto.
  rewrite <- IHl.
  rewrite filter_app; auto.
Qed.

Lemma all_nil_concat :
  forall A (l : list (list A)),
    (forall xs, In xs l -> xs = []) ->
    concat l = [].
Proof.
  induction l; auto.
  simpl; intros.
  replace a with (@nil A); auto.
  symmetry; auto.
Qed.

Lemma no_elements_nil :
  forall A (l : list A),
    (forall x, ~ In x l) ->
    l = [].
Proof.
  destruct l; eauto.
  intros.
  exfalso; find_eapply_prop not; in_crush.
Qed.

Lemma do_delayed_queries_singleton :
  forall src dst req st,
    unique (fun x => fst x = src) (delayed_queries st) (src, req) ->
    In (src, req) (delayed_queries st) ->
    (forall src' req',
        In (src', req') (delayed_queries st) ->
        request_payload req' /\ is_safe req' = false) ->
    cur_request st = None ->
    forall ms st' nts cts,
      do_delayed_queries dst st = (st', ms, nts, cts) ->
      exists res,
        filter (fun x => if addr_eq_dec (fst x) src then true else false) ms = [(src, res)].
Proof.
  intros.
  repeat handler_def || handler_simpl.
  find_apply_lem_hyp in_split; expand_def.
  rewrite filter_concat.
  repeat find_rewrite; rewrite !map_app; simpl.
  remember (handle_query_req st src req) as sends; symmetry in Heqsends.
  assert (request_payload req /\ is_safe req = false) by eauto; break_and.
  find_copy_eapply_lem_hyp (handle_query_req_gives_response st src req); eauto.
  find_copy_eapply_lem_hyp real_requests_get_response_handle_query_req; try solve [eauto | destruct req; simpl in *; congruence].
  break_exists_exists; break_and; break_exists.
  repeat find_rewrite || find_injection || handler_simpl.
  destruct (addr_eq_dec src src); try congruence.
  assert (forall dqs l,
             dqs = x0 \/ dqs = x ->
             In l (map (filter (fun x1 => if addr_eq_dec (fst x1) src then true else false))
                       (map (handle_delayed_query dst st) dqs)) ->
             l = []).
  {
    intros.
    find_apply_lem_hyp in_map_iff; break_exists; break_and.
    find_apply_lem_hyp in_map_iff; break_exists; break_and.
    subst.
    eapply no_elements_nil; intros; intro.
    find_apply_lem_hyp filter_In; break_and.
    break_match; try congruence.
    assert (exists p, fst p = src /\ In p (x ++ x0)).
    {
      unfold handle_delayed_query in *; break_let; subst.
      assert (request_payload p /\ is_safe p = false)
        by (find_eapply_prop and; in_crush; eauto).
      break_and.
      find_copy_eapply_lem_hyp (handle_query_req_gives_response st a p); eauto.
      break_exists; break_and.
      find_rewrite.
      simpl in *; intuition; simpl in *; subst;
        exists (a, p); intuition.
    }
    break_exists; break_and.
    unfold unique in *; break_and.
    find_eapply_prop not; eauto.
  }
  repeat rewrite concat_app; simpl.
  change [(src, x2)] with ([] ++ (src, x2) :: []).
  f_equal; [|f_equal]; eauto using all_nil_concat.
Qed.

Lemma concat_in :
  forall A l (x : A),
    In x (concat l) ->
    exists xs,
      In xs l /\
      In x xs.
Proof.
  induction l; simpl in *.
  - intros; tauto.
  - in_crush.
    + exists a; eauto.
    + find_apply_hyp_hyp.
      break_exists_exists.
      tauto.
Qed.

Lemma query_message_ok_delayed_queries_all_requests :
  forall gst,
    (forall src dst st__src,
        sigma gst src = Some st__src ->
        query_message_ok' src dst (cur_request st__src) (option_map delayed_queries (sigma gst dst))
                          (nodes gst) (failed_nodes gst)
                          (channel gst src dst) (channel gst dst src)) ->
    forall h st,
      sigma gst h = Some st ->
      forall src req,
        In (src, req) (delayed_queries st) ->
        request_payload req /\
        is_safe req = false.
Proof.
Admitted.

Lemma split_of_app_right :
  forall A (l l' : list A) xs a ys,
    l ++ l' = xs ++ a :: ys ->
    In a l' ->
    exists xs',
      xs = l ++ xs' /\
      l' = xs' ++ a :: ys.
Proof.
Admitted.

Lemma split_of_app_left :
  forall A (l l' : list A) xs a ys,
    l ++ l' = xs ++ a :: ys ->
    In a l ->
    exists ys',
      ys = ys' ++ l' /\
      l = xs ++ a :: ys'.
Proof.
Admitted.

Lemma unique_singleton :
  forall A (P : A -> Prop) x,
    P x ->
    unique P [x] x.
Proof.
  unfold unique; intuition eauto.
  match goal with
  | H: _ = _ |- _ => symmetry in H
  end.
  find_apply_lem_hyp app_cons_singleton_inv.
  break_and; subst; in_crush.
Qed.

Lemma recv_responses_unique :
  forall src dst req res st st' sends nts cts,
    request_payload req ->
    recv_handler src dst st req = (st', sends, nts, cts) ->
    (forall req, ~ In (src, req) (delayed_queries st)) ->
    In (src, res) sends ->
    response_payload res ->
    unique (fun p => fst p = src /\ response_payload (snd p)) sends (src, res).
Proof.
  intros.
  handler_def.
  in_crush.
  - exfalso.
    find_copy_eapply_lem_hyp handle_delayed_queries_res_only_if_req; eauto.
    expand_def.
    destruct (list_eq_dec send_eq_dec (delayed_queries x) (delayed_queries st)).
    + repeat find_rewrite; eauto.
    + find_eapply_lem_hyp handle_msg_only_changes_delayed_queries_when_busy; eauto.
      find_apply_lem_hyp do_delayed_queries_definition; expand_def; congruence.
  - eapply unique_app.
    + repeat handler_def || handler_simpl;
        try solve [inv_prop response_payload
                  |eapply unique_singleton; eauto].
      find_copy_apply_lem_hyp handle_query_req_only_sends_responses.
      pose proof (handle_query_req_gives_response st src req).
      forwards.
      inv_prop request_payload; simpl; try congruence.
      concludes.
      concludes.
      break_exists; repeat find_rewrite.
      replace (src, x) with (src, res0).
      eapply unique_singleton; eauto.
      eapply in_singleton_eq; eauto.
    + intuition.
      destruct y.
      simpl in *; subst.
      copy_eapply_lem_prop_hyp handle_delayed_queries_res_only_if_req do_delayed_queries; eauto.
      expand_def.
      destruct (list_eq_dec send_eq_dec (delayed_queries x) (delayed_queries st)).
      * repeat find_rewrite; eauto.
      * find_copy_eapply_lem_hyp handle_msg_dqs_change_queue; eauto.
        find_copy_eapply_lem_hyp handle_msg_only_changes_delayed_queries_when_busy; eauto.
        break_exists.
        repeat find_rewrite.
        simpl in *; break_match; eauto.
        simpl in *; intuition eauto using in_dedup_was_in.
        find_injection.
        repeat handler_def; eauto;
          simpl in *; congruence.
Qed.

Lemma filterMap_split_inv :
  forall A B (f : A -> option B) l b xs ys,
    filterMap f l = xs ++ b :: ys ->
    exists xs' a ys',
      l = xs' ++ a :: ys' /\
      filterMap f xs' = xs /\
      f a = Some b /\
      filterMap f ys' = ys.
Proof.
  induction l; eauto.
  - intros; in_crush.
    destruct xs; simpl in *; congruence.
  - intros; simpl in *.
    break_match.
    + destruct xs; simpl in *; find_injection.
      * exists nil.
        repeat eexists; intuition eauto.
      * find_apply_hyp_hyp; expand_def.
        exists (a::x), x0, x1.
        intuition eauto.
        simpl; repeat find_rewrite; auto.
    + find_apply_hyp_hyp.
      expand_def.
      exists (a::x), x0, x1.
      intuition eauto.
      simpl; repeat find_rewrite; auto.
Qed.

Lemma filterMap_sends_unique :
  forall (P : payload -> Prop) dst ms m,
    unique (fun p => fst p = dst /\ P (snd p)) ms (dst, m) ->
    unique P (filterMap (fun m => if addr_eq_dec (fst m) dst then Some (snd m) else None) ms) m.
Proof.
  unfold unique; intuition eauto.
  intros.
  find_apply_lem_hyp filterMap_split_inv; expand_def.
  break_match; try congruence.
  destruct x0; simpl in *; find_injection.
  find_eapply_prop False; eauto.
  channel_crush; in_crush; eauto.
  eauto.
Qed.

Lemma unique_remove :
  forall A (P : A -> Prop) xs x ys u,
    unique P (xs ++ x :: ys) u ->
    unique P (xs ++ ys) u.
Proof.
  intros.
  find_apply_lem_hyp (@unique_app_comm A).
  simpl in *.
  find_apply_lem_hyp (@unique_cons_remove A).
  eauto using unique_app_comm.
Qed.

Theorem query_message_ok'_recv_dst_recv :
  forall gst gst' src h st p xs ys st' ms nts cts,
    reachable_st gst ->
    step_dynamic gst gst' ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    msgs gst = xs ++ (src, (h, p)) :: ys ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst') ->
    sigma gst h = Some st ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' =
    update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (timeouts gst h)) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = map (send h) ms ++ xs ++ ys ->
    trace gst' = trace gst ++ [e_recv (src, (h, p))] ->
    (forall src dst st__src,
        sigma gst src = Some st__src ->
        query_message_ok' src dst (cur_request st__src) (option_map delayed_queries (sigma gst dst))
                          (nodes gst) (failed_nodes gst)
                          (channel gst src dst) (channel gst dst src)) ->
    (forall (src : addr) (st__src : data),
        sigma gst src = Some st__src ->
        h <> src ->
        query_message_ok' src h (cur_request st__src)
                          (option_map delayed_queries (sigma gst h)) (nodes gst) (failed_nodes gst)
                          (channel gst src h) (channel gst h src)) ->
    (forall (src : addr) (st__src : data),
        sigma gst' src = Some st__src ->
        h <> src ->
        query_message_ok' src h (cur_request st__src)
                          (option_map delayed_queries (sigma gst' h)) (nodes gst') (failed_nodes gst')
                          (channel gst' src h) (channel gst' h src)).
Proof.
  autounfold; intros.
  repeat find_rewrite || rewrite_update.
  simpl.
  eapply QMLive; eauto.
  match goal with
  | H: _ |- _ => pose proof H as ?; specialize (H src0 st__src); repeat conclude H eassumption
  end.
  inv_prop query_message_ok'; try tauto.
  erewrite channel_after_recv_to_not_dst with (dst := h) by eauto.
  inv_prop query_message_ok.
  - constructor.
    + apply no_responses_app; auto.
      unfold no_responses; intros.
      channel_crush.
      destruct (response_payload_dec m); auto.
      find_copy_eapply_lem_hyp recv_handler_res_only_if_req; try eassumption.
      expand_def.
      * exfalso.
        eapply_prop no_requests; simpl; eauto.
      * exfalso; find_eapply_prop delayed_queries; eauto.
    + destruct (addr_eq_dec src0 src).
      * pose proof (channel_after_recv_src_dst gst gst' src h p ms xs ys).
        repeat (concludes; eauto); expand_def.
        repeat find_rewrite.
        find_apply_lem_hyp app_no_requests; break_and.
        find_apply_lem_hyp cons_no_requests; break_and.
        repeat apply no_requests_app; auto.
        unfold no_requests; intros.
        channel_crush.
      * erewrite channel_after_recv_unrelated; eauto.
    + handler_def.
      assert (delayed_queries x3 = delayed_queries x \/ delayed_queries x3 = [])
        by (find_eapply_lem_hyp do_delayed_queries_definition; expand_def; eauto).
      find_eapply_lem_hyp handle_msg_only_appends_incoming_req_to_delayed_queries_when_busy;
        expand_def; repeat find_rewrite; eauto.
      * in_crush.
        find_apply_lem_hyp in_dedup_was_in; eauto.
      * in_crush.
        -- find_injection.
           eapply_prop no_requests; chan2msg; try eassumption.
           repeat find_rewrite; in_crush.
        -- find_apply_lem_hyp in_dedup_was_in; eauto.
  - eapply CIother; eauto.
    + apply no_responses_app; auto.
      unfold no_responses; intros.
      channel_crush.
      destruct (response_payload_dec m); auto.
      find_copy_eapply_lem_hyp recv_handler_res_only_if_req; try eassumption.
      expand_def.
      * exfalso.
        eapply_prop no_requests; simpl; eauto.
      * exfalso; find_eapply_prop delayed_queries; eauto.
    + destruct (addr_eq_dec src0 src).
      * pose proof (channel_after_recv_src_dst gst gst' src h p ms xs ys).
        repeat (concludes; eauto); expand_def.
        repeat find_rewrite.
        find_apply_lem_hyp app_no_requests; break_and.
        find_apply_lem_hyp cons_no_requests; break_and.
        repeat apply no_requests_app; auto.
        unfold no_requests; intros.
        channel_crush.
      * erewrite channel_after_recv_unrelated; eauto.
    + handler_def.
      assert (delayed_queries x3 = delayed_queries x \/ delayed_queries x3 = [])
        by (find_eapply_lem_hyp do_delayed_queries_definition; expand_def; eauto).
      find_eapply_lem_hyp handle_msg_only_appends_incoming_req_to_delayed_queries_when_busy;
        expand_def; repeat find_rewrite; eauto.
      * in_crush.
        find_apply_lem_hyp in_dedup_was_in; eauto.
      * in_crush.
        -- find_injection.
           eapply_prop no_requests; chan2msg; try eassumption.
           repeat find_rewrite; in_crush.
        -- find_apply_lem_hyp in_dedup_was_in; eauto.
  - destruct (send_eq_dec (src, p) (src0, req)); try find_injection.
    + find_copy_apply_lem_hyp requests_get_response_or_queued; eauto.
      expand_def.
      * eapply CIdelayed; eauto.
        -- inv_prop query_request; simpl; congruence.
        -- intros.
           handler_def.
           find_eapply_lem_hyp do_delayed_queries_definition; expand_def.
           destruct (list_eq_dec send_eq_dec (delayed_queries x) (delayed_queries st)).
           ++ exfalso; find_eapply_prop delayed_queries; repeat find_rewrite; eauto.
           ++ find_eapply_lem_hyp handle_msg_dqs_change_queue; eauto.
              repeat find_rewrite.
              replace (dedup send_eq_dec ((src0, req) :: delayed_queries st)) with ((src0, req) :: dedup send_eq_dec (delayed_queries st)) in *.
              replace xs0 with (@nil (addr * payload)) in *.
              simpl in *; find_injection; intuition eauto using in_dedup_was_in.
              destruct xs0; try tauto.
              simpl in *; find_injection.
              exfalso; find_eapply_prop delayed_queries.
              eapply in_dedup_was_in with (x := (src0, req)).
              eauto.
              simpl; break_match; eauto.
              exfalso; find_eapply_prop delayed_queries; eauto.
        -- handler_def.
           eapply no_responses_app; eauto.
           unfold no_responses; intuition.
           channel_crush.
           ++ find_apply_lem_hyp do_delayed_queries_definition; expand_def; congruence.
           ++ repeat handler_def || handler_simpl; inv_prop response_payload.
        -- unfold no_requests; intros.
           find_eapply_lem_hyp channel_after_recv_src_dst; eauto.
           expand_def.
           assert (no_requests (x ++ x0)) by eauto.
           repeat find_rewrite.
           find_apply_lem_hyp in_app_or; break_or_hyp.
           ++ find_eapply_lem_hyp In_filterMap; expand_def.
              repeat break_match; congruence.
           ++ eapply_prop no_requests; eauto.
      * eapply CIres; eauto.
        -- eapply in_or_app; left.
           eapply filterMap_In; eauto.
           simpl; break_match; congruence.
        -- intros.
           find_apply_lem_hyp split_of_app_left; expand_def.
           rewrite app_assoc.
           eapply no_responses_app; eauto.
           assert (unique response_payload (filterMap (fun m => if addr_eq_dec (fst m) src0 then Some (snd m) else None) ms) x).
           {
             eapply filterMap_sends_unique; eauto.
             eauto using recv_responses_unique.
           }
           unfold unique, no_responses in *; break_and; eauto.
           eapply filterMap_In; eauto; simpl.
           destruct (addr_eq_dec src0 src0); congruence.
        -- find_copy_eapply_lem_hyp channel_after_recv_src_dst; eauto.
           expand_def.
           repeat find_rewrite.
           eapply no_requests_app; eauto.
           unfold no_requests; intuition.
           channel_crush.
        -- handler_def.
           find_apply_lem_hyp do_delayed_queries_definition; expand_def; simpl; auto.
           repeat handler_def || handler_simpl;
             intuition;
             repeat find_rewrite || find_injection;
             try inv_prop request_response_pair.
    + eapply CIreq.
      * chan2msg; repeat find_rewrite.
        in_crush; congruence.
      * destruct (addr_eq_dec src0 src);
          [destruct (payload_eq_dec p req)|];
          try congruence.
        -- assert (unique request_payload (channel gst src (addr_of dstp)) req)
             by (unfold unique, no_requests in *; repeat find_rewrite; intuition eauto).
           find_eapply_lem_hyp channel_after_recv_src_dst; eauto.
           assert (unique request_payload (channel gst' src0 (addr_of dstp)) req).
           {
             repeat find_rewrite.
             destruct (addr_eq_dec src (addr_of dstp)); try congruence.
             rewrite filterMap_all_None in * by auto.
             expand_def; simpl in *.
             repeat find_rewrite; eapply unique_remove; eauto.
           }
           unfold unique, no_requests in *; intuition eauto.
        -- erewrite channel_after_recv_unrelated; eauto.
      * unfold no_responses in *; intros; in_crush; eauto.
        find_copy_apply_lem_hyp In_filterMap; expand_def; break_match; try congruence.
        destruct x eqn:?; simpl in *; find_injection.
        find_eapply_lem_hyp recv_handler_res_only_if_req; eauto; expand_def; eauto.
        assert (unique request_payload (channel gst src (addr_of dstp)) req) by (unfold unique; eauto).
        assert (x = req).
        eapply unique_eq; eauto using payload_eq_dec.
        congruence.
      * handler_def.
        intuition.
        find_copy_eapply_lem_hyp do_delayed_queries_definition; expand_def.
        destruct (list_eq_dec send_eq_dec (delayed_queries x) (delayed_queries st)).
        ++ exfalso; find_eapply_prop delayed_queries; repeat find_rewrite; eauto.
        ++ copy_eapply_lem_prop_hyp handle_msg_dqs_change_queue_for_reqs handle_msg; eauto.
           expand_def; repeat find_rewrite.
           find_eapply_lem_hyp in_dedup_was_in.
           simpl in *; break_or_hyp; try eauto.
           find_injection.
           assert (m <> req) by congruence.
           assert (In m (channel gst src0 (addr_of dstp))) by (chan2msg; eauto).
           break_match; eauto.
           eapply_lem_prop_hyp in_split req; expand_def.
           find_eapply_prop no_requests; try eassumption.
           repeat find_rewrite.
           in_crush.
      * eauto.
  - eapply CIres; eauto; try solve [in_crush].
    + intros.
      handler_def.
      rewrite filterMap_app in *.
      assert (filterMap (fun m => if addr_eq_dec (fst m) src0 then Some (snd m) else None) x4 = []).
      {
        eapply filterMap_all_None; intros.
        find_apply_lem_hyp do_delayed_queries_definition; expand_def.
        find_apply_lem_hyp concat_in; expand_def.
        in_crush.
        destruct x4 as (src', req').
        assert (request_payload req' /\
                is_safe req' = false).
        {
          destruct (list_eq_dec send_eq_dec (delayed_queries x) (delayed_queries st)).
          repeat find_rewrite; eauto.
          eapply query_message_ok_delayed_queries_all_requests with (h := (addr_of dstp)); eauto.
          find_apply_lem_hyp handle_msg_dqs_change_queue_for_reqs; eauto; expand_def.
          repeat find_rewrite.
          find_apply_lem_hyp in_dedup_was_in; eauto.
          simpl in *; break_or_hyp; [find_injection|].
          eauto.
          repeat find_rewrite; eauto.
          eapply query_message_ok_delayed_queries_all_requests with (h := (addr_of dstp)); eauto.
        }
        break_and.
        unfold handle_delayed_query in *.
        find_eapply_lem_hyp (handle_query_req_gives_response x src' req'); eauto.
        expand_def; repeat find_rewrite.
        simpl in *; intuition subst.
        simpl; break_match; auto; subst.
        exfalso.
        destruct (list_eq_dec send_eq_dec (delayed_queries x) (delayed_queries st)).
        * find_eapply_prop delayed_queries; repeat find_rewrite; eauto.
        * find_apply_lem_hyp handle_msg_dqs_change_queue_for_reqs; eauto; expand_def.
          repeat find_rewrite.
          find_apply_lem_hyp in_dedup_was_in; eauto.
          simpl in *; break_or_hyp; eauto.
          find_injection.
          find_eapply_prop no_requests; eauto.
      }
      assert (no_responses (filterMap (fun m : addr * ChordSemantics.payload => if addr_eq_dec (fst m) src0 then Some (snd m) else None) x0)).
      {
        unfold no_responses; intuition.
        channel_crush.
        find_eapply_lem_hyp handle_msg_res_only_if_req; eauto.
        break_and.
        eapply_prop no_requests; channel_crush; eauto.
      }
      repeat find_rewrite; simpl in *.
      find_copy_eapply_lem_hyp split_of_app_right; eauto.
      expand_def.
      rewrite <- app_assoc in *.
      eapply no_responses_app; eauto.
    + unfold no_requests; intros.
      find_eapply_lem_hyp channel_after_recv_from_not_dst; eauto.
    + handler_def.
      find_apply_lem_hyp do_delayed_queries_definition; expand_def; simpl; auto.
      destruct (list_eq_dec send_eq_dec
                            (delayed_queries x)
                            (delayed_queries st)).
      * repeat find_rewrite; eauto.
      * find_copy_apply_lem_hyp handle_msg_dqs_change_queue_for_reqs; eauto.
        break_and.
        repeat find_rewrite.
        destruct (addr_eq_dec src0 src); subst.
        -- exfalso; eapply_prop no_requests; chan2msg; eauto.
        -- simpl; break_match;
             simpl; intuition; try congruence;
               eauto using in_dedup_was_in.
  - find_copy_eapply_lem_hyp recv_handler_definition_existential; expand_def.
    assert (In (src0, req) (delayed_queries x))
      by eauto using in_dqs_preserved_by_handle_msg.
    assert (unique (fun p => fst p = src0) (delayed_queries st) (src0, req))
      by eauto.
    find_copy_apply_lem_hyp do_delayed_queries_definition; expand_def.
    + simpl in *.
      eapply CIdelayed; eauto.
      * cut (unique (fun p => fst p = src0) (delayed_queries x) (src0, req));
          [eauto|].
        destruct (list_eq_dec send_eq_dec
                              (delayed_queries x)
                              (delayed_queries st)).
        -- congruence.
        -- find_copy_apply_lem_hyp handle_msg_dqs_change_queue_for_reqs; eauto.
           break_and.
           repeat find_rewrite.
           destruct (addr_eq_dec src0 src); subst.
           ++ exfalso; eapply_prop no_requests; chan2msg; eauto.
           ++ eapply unique_dedup.
              eapply unique_cons; simpl; auto.
      * unfold no_responses; intros.
        channel_crush; eauto.
        intro.
        eapply_lem_prop_hyp handle_msg_res_only_if_req handle_msg; eauto.
        expand_def.
        eapply_prop no_requests; chan2msg; repeat find_rewrite; in_crush; eauto.
      * unfold no_requests; intros.
        find_eapply_prop no_requests.
        eapply channel_after_recv_from_not_dst; eauto.
    + find_copy_eapply_lem_hyp (do_delayed_queries_responds (addr_of dstp)); eauto.
      expand_def.
      eapply CIres; eauto.
      * eapply in_or_app; left.
        eapply filterMap_In;
          [|eapply in_or_app; left; eauto].
        simpl; break_match; congruence.
      * eapply unique_no_responses.
        eapply unique_app_r;
          [|eapply_prop no_responses].
        rewrite filterMap_app.
        eapply unique_app_r.
        -- assert (unique (fun x4 : addr * payload => fst x4 = src0) (delayed_queries st) (src0, req) /\
                   forall (src' : addr) (req' : payload), In (src', req') (delayed_queries st) -> request_payload req' /\ is_safe req' = false).
           {
             split; eauto.
             eapply query_message_ok_delayed_queries_all_requests; eauto.
           }
           assert (unique (fun x4 : addr * payload => fst x4 = src0) (delayed_queries x) (src0, req) /\
                   forall (src' : addr) (req' : payload), In (src', req') (delayed_queries x) -> request_payload req' /\ is_safe req' = false).
           {
             destruct (list_eq_dec send_eq_dec
                                   (delayed_queries x)
                                   (delayed_queries st)).
             - repeat find_rewrite; eauto.
             - find_copy_apply_lem_hyp handle_msg_dqs_change_queue_for_reqs; eauto; break_and.
               repeat find_rewrite.
               destruct (addr_eq_dec src0 src); subst; split;
                 try solve [exfalso; eapply_prop no_requests; chan2msg; eauto].
               ++ eapply unique_dedup.
                  eapply unique_cons; simpl; auto.
               ++ intros.
                  find_apply_lem_hyp in_dedup_was_in.
                  simpl in *; break_or_hyp; eauto.
                  find_injection; auto.
           }
           break_and.
           copy_eapply_lem_prop_hyp do_delayed_queries_singleton do_delayed_queries; try eassumption.
           break_exists.
           rewrite filterMap_sumbool_map_filter; eauto.
           repeat find_rewrite.
           unfold unique; intuition eauto.
           simpl in *.
           find_apply_lem_hyp split_eq_singleton; break_and; subst.
           in_crush.
        -- intuition.
           channel_crush.
           find_eapply_lem_hyp handle_msg_res_only_if_req; eauto.
           break_and; subst.
           eapply_prop no_requests; chan2msg; repeat find_rewrite; eauto.
      * unfold no_requests in *.
        intros; chan2msg.
        repeat find_rewrite.
        channel_crush.
        -- find_eapply_prop request_payload.
           chan2msg; repeat find_rewrite; in_crush.
        -- find_eapply_prop request_payload.
           chan2msg; repeat find_rewrite; in_crush.
Qed.

Lemma cur_request_targets_in_nodes :
  forall gst h st dstp q m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dstp, q, m) ->
    In (addr_of dstp) (nodes gst).
Proof.
  intros.
  destruct q.
  - admit.
  - find_eapply_lem_hyp stabilize_target_joined; eauto.
    expand_def.
    eauto.
  - find_eapply_lem_hyp stabilize2_target_joined; eauto.
    expand_def.
    eauto.
  - admit.
  - find_eapply_lem_hyp join2_unreachable; eauto; intuition.
Admitted.

Lemma do_delayed_queries_only_responds :
  forall h st st' ms nts cts dst m,
    do_delayed_queries h st = (st', ms, nts, cts) ->
    In (dst, m) ms ->
    response_payload m.
Proof.
  intros.
  repeat handler_def || handler_simpl.
Qed.

Lemma notify_means_dst_is_in_succs :
  forall src h st p st' ms nts cts dst,
    recv_handler src h st p = (st', ms, nts, cts) ->
    In (dst, Notify) ms ->
    exists dstp tl,
      addr_of dstp = dst /\
      succ_list st' = dstp :: tl.
Proof.
  intros.
  handler_def.
  in_crush.
  - find_eapply_lem_hyp do_delayed_queries_only_responds; eauto.
    inv_prop response_payload.
  - destruct SUCC_LIST_LEN eqn:?; [pose proof succ_list_len_lower_bound; omega|].
    repeat handler_def || handler_simpl; unfold make_succs, chop_succs; repeat find_rewrite;
      try solve [unfold handle_query_req in *; break_match; in_crush; congruence];
      eexists; eexists; simpl; split;
        try match goal with
        | |- _ :: _ = _ :: _ => eauto
        end; eauto.
Qed.

Lemma request_sent_by_recv :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    forall dst req,
      In (dst, req) ms ->
      request_payload req ->
      exists dstp q m,
        cur_request st = Some (dstp, q, m) /\
        addr_of dstp = src /\
        ((q = Stabilize /\
         exists pred succs,
           p = GotPredAndSuccs (Some pred) succs /\
           ptr_between (ptr st) pred (make_pointer (addr_of dstp)) /\
           dst = addr_of pred /\
           req = GetSuccList /\
           cur_request st' = Some (pred, Stabilize2 pred, req)) \/
        (exists k srv,
            q = Join k /\
            addr_of srv = addr_of dstp /\
            p = GotBestPredecessor srv /\
            dst = addr_of srv /\
            req = GetSuccList /\
            cur_request st' = Some (srv, Join k, req)) \/
        (exists k srv,
            q = Join k /\
            addr_of srv <> addr_of dstp /\
            p = GotBestPredecessor srv /\
            dst = addr_of srv /\
            req = GetBestPredecessor (ptr st) /\
            cur_request st' = Some (srv, Join k, req))).
Proof.
  intros.
  match goal with
  | |- ?G => set (P := G); cut (P \/ False); [tauto|]
  end.
  repeat handler_def || handler_simpl || in_crush;
    try solve [inv_prop request_payload];
    left; unfold P; repeat find_rewrite.
  - do 3 eexists; intuition eauto.
    intuition (repeat (eauto || eexists)).
  - do 3 eexists; intuition eauto.
    right; left.
    intuition (repeat (eauto || eexists)).
  - do 3 eexists; intuition eauto.
    right; right.
    intuition (repeat (eauto || eexists)).
Qed.

Lemma contains_request_dec :
  forall l,
    (exists m, In m l /\ request_payload m) \/ (forall m, In m l -> ~ request_payload m).
Proof.
  induction l; eauto.
  - simpl.
    destruct (is_request a) eqn:?.
    + left.
      exists a; split; eauto.
      eapply is_request_same_as_request_payload; eauto.
    + intuition.
      * left.
        break_exists_exists; intuition.
      * right; intros.
        break_or_hyp; eauto.
        find_apply_lem_hyp is_request_same_as_request_payload.
        congruence.
Qed.

Lemma contains_request_to_dec :
  forall (dst : addr) l,
    (exists m, In (dst, m) l /\ request_payload m) \/ (forall m, In (dst, m) l -> ~ request_payload m).
Proof.
  induction l; eauto.
  - simpl.
    destruct a as (dst', m').
    destruct (addr_eq_dec dst' dst), (is_request m') eqn:?.
    + subst.
      left.
      exists m'; split; eauto.
      eapply is_request_same_as_request_payload; eauto.
    + intuition.
      * left.
        break_exists_exists; intuition.
      * right; intros.
        break_or_hyp; eauto.
        find_apply_lem_hyp is_request_same_as_request_payload.
        congruence.
    + intuition.
      * left.
        break_exists_exists; intuition.
      * right; intros.
        break_or_hyp; eauto.
        congruence.
    + intuition.
      * left.
        break_exists_exists; intuition.
      * right; intros.
        break_or_hyp; eauto.
        congruence.
Qed.

Lemma is_response_from_dec :
  forall (h : addr) m src,
    (response_payload m /\ h = src) \/ (~ response_payload m \/ h <> src).
Proof.
  intros.
  destruct (response_payload_dec m), (addr_eq_dec h src); eauto.
Qed.

Lemma recv_handler_query_request_cur_request :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    (forall dstp q m,
        cur_request st = Some (dstp, q, m) ->
        query_request q m) ->
    forall dstp' q' m',
        cur_request st' = Some (dstp', q', m') ->
        query_request q' m'.
Proof.
  intros.
  repeat handler_def || handler_simpl.
Qed.

Lemma recv_handler_not_response_from_dst_preserves_cur_request :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    forall dstp q m,
      cur_request st = Some (dstp, q, m) ->
      ~ query_response q p \/ src <> addr_of dstp ->
      cur_request st' = cur_request st.
Proof.
  intros.
  repeat handler_def || handler_simpl;
    repeat find_rewrite || find_injection;
    try solve [exfalso; find_eapply_prop query_response; eauto].
Qed.

Lemma recv_handler_not_response_from_dst_sends_no_requests :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    forall dstp q m,
      cur_request st = Some (dstp, q, m) ->
      ~ query_response q p \/ src <> addr_of dstp ->
      forall s pp,
        In (s, pp) ms ->
        ~ request_payload pp.
Proof.
  intros.
  repeat handler_def || handler_simpl;
    repeat find_rewrite || find_injection || break_or_hyp;
    try solve [exfalso; find_eapply_prop query_response; eauto
              |inv_prop request_payload
              |tauto].
Qed.

Lemma recv_handler_cr_None_sends_no_requests :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    cur_request st = None ->
    forall s pp,
      In (s, pp) ms ->
      ~ request_payload pp.
Proof.
  intros.
  repeat handler_def || handler_simpl;
    in_crush; eauto using handle_delayed_query_only_sends_responses;
      find_injection; inv_prop request_payload. 
Qed.

Lemma recv_handler_cr_after_None_sends_no_requests :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    cur_request st' = None ->
    forall s pp,
      In (s, pp) ms ->
      ~ request_payload pp.
Proof.
  intros.
  repeat handler_def || handler_simpl;
    in_crush; eauto using handle_delayed_query_only_sends_responses;
      find_injection; inv_prop request_payload. 
Qed.

Lemma recv_cur_request_None_preserved :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    cur_request st = None ->
    cur_request st' = None.
Proof.
  intros.
  repeat handler_def || handler_simpl.
Qed.

Lemma recv_cr_None_empties_dqs :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    cur_request st' = None ->
    delayed_queries st' = [].
Proof.
  intros.
  repeat handler_def || handler_simpl.
Qed.

Lemma recv_res_new_req_in_channel :
  forall h st p st' ms nts cts dstp q m,
    recv_handler (addr_of dstp) h st p = (st', ms, nts, cts) ->
    cur_request st = Some (dstp, q, m) ->
    request_response_pair m p ->
    query_request q m ->
    forall dstp' q' m',
      cur_request st' = Some (dstp', q', m') ->
      In (addr_of dstp', m') ms.
Proof.
  intros.
  repeat handler_def || handler_simpl;
    try solve [inv_prop request_response_pair
              |inv_prop request_response_pair; simpl in *; congruence].
  - left; f_equal; congruence.
  - repeat find_rewrite || find_injection.
    find_eapply_prop query_response.
    inv_prop query_request; inv_prop request_response_pair; constructor.
Qed.

Lemma recv_res_new_req_unique :
  forall h st p st' ms nts cts dstp q m,
    recv_handler (addr_of dstp) h st p = (st', ms, nts, cts) ->
    cur_request st = Some (dstp, q, m) ->
    query_response q p ->
    query_request q m ->
    forall dstp' q' m',
      cur_request st' = Some (dstp', q', m') ->
      unique (fun s => fst s = addr_of dstp' /\ request_payload (snd s)) ms (addr_of dstp', m').
Proof.
  intros.
  repeat handler_def || handler_simpl;
    try solve [inv_prop query_response; inv_prop query_request
              |inv_prop query_response; inv_prop query_request; simpl in *; congruence
              |find_eapply_lem_hyp is_request_same_as_request_payload; congruence
              |eauto using unique_triv].
  eapply unique_triv; simpl; auto.
Qed.

Lemma recv_no_responses :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    forall dst m,
      In (dst, m) ms ->
      dst <> src \/ ~ request_payload p ->
      (cur_request st' <> None \/ forall req, ~ In (dst, req) (delayed_queries st)) ->
      ~ response_payload m.
Proof.
  intros.
  repeat handler_def || handler_simpl;
    try solve [inv_prop request_response_pair
              |inv_prop request_response_pair; simpl in *; congruence
              |find_eapply_lem_hyp is_request_same_as_request_payload; congruence
              |eauto using unique_triv
              |in_crush; find_injection; inv_prop response_payload; eauto];
    repeat match goal with
           | H: In _ (_ ++ _) |- _ => in_crush
           | H: In (dst, m) (concat (map _ _)) |- _ =>
             eapply handle_delayed_query_dst_in_dqs in H; expand_def; solve [eauto]
           | H: (_, _) = (_, _) |- _ => injc H
           | H: response_payload Notify |- _ => injc H
           | H: In (dst, m) (handle_query_req _ _ _) |- _ =>
             solve [unfold handle_query_req in H; break_match; in_crush; find_injection; auto]
           | |- _ => eauto
           end;
    inv_prop response_payload.
Qed.

Theorem query_message_ok_recv_src_distinct_recv_same :
  forall gst gst' src h st p xs ys st' ms nts cts,
    reachable_st gst ->
    step_dynamic gst gst' ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    msgs gst = xs ++ (src, (h, p)) :: ys ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst') ->
    sigma gst h = Some st ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' =
    update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (timeouts gst h)) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = map (send h) ms ++ xs ++ ys ->
    trace gst' = trace gst ++ [e_recv (src, (h, p))] ->
    (forall (dst : addr) (st__src : data),
        sigma gst h = Some st__src ->
        query_message_ok' h dst (cur_request st__src)
                          (option_map delayed_queries (sigma gst dst))
                          (nodes gst') (failed_nodes gst')
                          (channel gst h dst) (channel gst dst h)) ->
    forall (dst : addr) (st__src' st__dst st__dst' : data),
      h <> dst ->
      src = dst ->
      sigma gst' h = Some st__src' ->
      sigma gst dst = Some st__dst ->
      sigma gst' dst = Some st__dst' ->
      query_message_ok h dst (cur_request st) (delayed_queries st__dst) (channel gst h dst) (channel gst dst h) ->
      ~ In dst (failed_nodes gst') ->
      query_message_ok h dst (cur_request st__src')
                       (delayed_queries st__dst')
                       (channel gst' h dst) (channel gst' dst h).
Proof.
  intros.
  assert (st__dst' = st__dst)
    by (repeat find_rewrite; rewrite_update; congruence); subst.
  subst.
  find_copy_eapply_lem_hyp channel_after_recv_src_dst; eauto; expand_def.
  repeat find_rewrite.
  destruct (addr_eq_dec dst h); try congruence; simpl.
  rewrite filterMap_all_None in * by eauto; simpl in *.
  erewrite channel_after_recv_not_src_dst by eauto.
  inv_prop query_message_ok.
  - find_copy_apply_lem_hyp recv_cur_request_None_preserved; eauto.
    repeat find_rewrite || rewrite_update || find_injection.
    match goal with
    | H: None = _ |- _ => rewrite <- H
    end.
    destruct (addr_eq_dec h h); try congruence.
    replace (cur_request st) with (@None (pointer * query * payload)) by congruence.
    eapply CInone; eauto.
    + unfold no_responses; intros; eapply_prop no_responses; in_crush.
    + eapply no_requests_app; auto.
      unfold no_requests; intros.
      channel_crush.
      eauto using recv_handler_cr_None_sends_no_requests.
  - repeat find_rewrite || find_injection || rewrite_update.
    find_copy_eapply_lem_hyp recv_msg_not_right_response_preserves_cur_request; eauto.
    replace (cur_request _) with (Some (dstp, q, req)) by congruence.
    eapply CIother; eauto.
    + unfold no_responses; intros; eapply_prop no_responses; in_crush.
    + eapply no_requests_app; eauto.
      unfold no_requests; intros.
      channel_crush.
      eauto using recv_handler_not_response_from_dst_sends_no_requests.
    + intro.
      eapply_prop no_responses; eauto.
  - find_copy_eapply_lem_hyp recv_msg_not_right_response_preserves_cur_request; eauto.
    repeat find_rewrite || rewrite_update || find_injection || handler_simpl.
    replace (cur_request _) with (Some (dstp, q, req)) by congruence.
    eapply CIreq; eauto.
    + in_crush.
    + eapply unique_no_requests.
      eapply unique_app; eauto using no_requests_unique.
      intros.
      destruct (addr_eq_dec h h); try congruence.
      channel_crush; eapply recv_handler_not_response_from_dst_sends_no_requests; eauto.
      left; intuition.
      eapply_prop no_responses; eauto.
    + unfold no_responses; intros; eapply_prop no_responses; in_crush.
    + intro.
      eapply_prop no_responses; eauto.
  - destruct (payload_eq_dec p res0); subst.
    + simpl in *.
      repeat find_rewrite || rewrite_update || find_injection || handler_simpl.
      destruct (cur_request st__src') as [[[? ?]]|] eqn:?.
      * destruct (addr_eq_dec (addr_of dstp) (addr_of p)).
        -- repeat find_rewrite.
           eapply CIreq; eauto.
           ++ assert (In (addr_of p, p0) ms).
              {
                match goal with
                | H: context[recv_handler] |- _ =>
                  replace (addr_of p) with (addr_of dstp) in H by eauto
                end.
                eapply recv_res_new_req_in_channel; eauto.
              }
              eapply in_or_app; left.
              eapply filterMap_In; eauto; simpl.
              destruct (addr_eq_dec _ _); try congruence.
              destruct (addr_eq_dec _ _); try congruence.
           ++ eapply unique_no_requests.
              eapply unique_app_r; eauto.
              destruct (addr_eq_dec _ _); try congruence.
              eapply filterMap_sends_unique; eauto.
              match goal with
              | H: context[recv_handler] |- _ =>
                replace (addr_of p) with (addr_of dstp) in H by eauto
              end.
              eapply recv_res_new_req_unique; eauto.
              eauto.
              inv_prop request_response_pair; inv_prop query_request; constructor.
           ++ eapply recv_handler_query_request_cur_request; eauto.
              intros; congruence.
        -- eapply CIother; eauto.
           ++ eapply no_requests_app; eauto.
              unfold no_requests; intros.
              clear H23.
              channel_crush.
              intro.
              find_copy_eapply_lem_hyp request_sent_by_recv; eauto; expand_def;
                repeat find_rewrite || find_injection; try congruence.
           ++ eapply recv_handler_query_request_cur_request; eauto.
              intros; congruence.
      * eapply CInone; eauto.
        -- eapply no_requests_app; eauto.
           unfold no_requests; intros.
           clear H23.
           channel_crush.
           intro.
           find_copy_eapply_lem_hyp request_sent_by_recv; eauto; expand_def; congruence.
    + assert (~ query_response q p).
      {
        intro; find_eapply_prop not.
        eapply unique_eq; eauto using no_responses_unique, payload_eq_dec.
      }
      find_copy_eapply_lem_hyp recv_msg_not_right_response_preserves_cur_request; eauto.
      repeat find_rewrite || rewrite_update || find_injection || handler_simpl.
      replace (cur_request _) with (Some (dstp, q, req)) by congruence.
      eapply CIres; eauto.
      * in_crush.
      * eapply unique_no_responses.
        eapply unique_remove; eauto using no_responses_unique.
      * eapply no_requests_app; eauto.
        destruct (addr_eq_dec h h); try congruence.
        unfold no_requests; intros.
        channel_crush; eapply recv_handler_not_response_from_dst_sends_no_requests; eauto.
  - assert (~ query_response q p)
      by (intro; eapply_prop no_responses; eauto).
    find_copy_eapply_lem_hyp recv_msg_not_right_response_preserves_cur_request; eauto.
    repeat find_rewrite || rewrite_update || find_injection || handler_simpl.
    replace (cur_request _) with (Some (dstp, q, req)) by congruence.
    eapply CIdelayed; eauto.
    + unfold no_responses; intros; eapply_prop no_responses; in_crush.
    + eapply no_requests_app; eauto.
      destruct (addr_eq_dec h h); try congruence.
      unfold no_requests; intros.
      channel_crush; eapply recv_handler_not_response_from_dst_sends_no_requests; eauto.
Qed.

Lemma recv_cur_request_changes :
  forall src h st p st' ms nts cts dstp q m dstp' q' m',
    recv_handler src h st p = (st', ms, nts, cts) ->
    cur_request st = Some (dstp, q, m) ->
    cur_request st' = Some (dstp', q', m') ->
    dstp <> dstp' ->
    addr_of dstp = src /\ query_response q p.
Proof.
  intros.
  repeat handler_def || handler_simpl;
    solve [repeat find_rewrite || find_injection; split; eauto; constructor].
Qed.

Theorem query_message_ok_recv_src_distinct_recv_other :
  forall gst gst' src h st p xs ys st' ms nts cts,
    reachable_st gst ->
    step_dynamic gst gst' ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    msgs gst = xs ++ (src, (h, p)) :: ys ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst') ->
    sigma gst h = Some st ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' =
    update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (timeouts gst h)) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = map (send h) ms ++ xs ++ ys ->
    trace gst' = trace gst ++ [e_recv (src, (h, p))] ->
    (forall (dst : addr) (st__src : data),
        sigma gst h = Some st__src ->
        query_message_ok' h dst (cur_request st__src)
                          (option_map delayed_queries (sigma gst dst))
                          (nodes gst') (failed_nodes gst')
                          (channel gst h dst) (channel gst dst h)) ->
    forall (dst : addr) (st__src' st__dst st__dst' : data),
      h <> dst ->
      src <> dst ->
      sigma gst' h = Some st__src' ->
      sigma gst dst = Some st__dst ->
      sigma gst' dst = Some st__dst' ->
      query_message_ok h dst (cur_request st) (delayed_queries st__dst) (channel gst h dst) (channel gst dst h) ->
      ~ In dst (failed_nodes gst') ->
      query_message_ok h dst (cur_request st__src')
                       (delayed_queries st__dst')
                       (channel gst' h dst) (channel gst' dst h).
Proof.
  intros.
  assert (st__dst' = st__dst)
    by (repeat find_rewrite; rewrite_update; congruence); subst.
  erewrite channel_after_recv_not_src_dst; eauto.
  erewrite (channel_after_recv_unrelated gst gst') by eauto.
  repeat find_rewrite || rewrite_update || find_injection.
  assert (query_message_ok' h src (cur_request st)
                            (option_map delayed_queries (sigma gst src))
                            (nodes gst) (failed_nodes gst)
                            (channel gst h src) (channel gst src h))
    by eauto.
  break_match; try congruence.
  inv_prop query_message_ok.
  - find_copy_apply_lem_hyp recv_cur_request_None_preserved; eauto.
    repeat find_rewrite || rewrite_update || find_injection.
    match goal with
    | H: None = _ |- _ => rewrite <- H
    end.
    destruct (addr_eq_dec h h); try congruence.
    replace (cur_request st) with (@None (pointer * query * payload)) by congruence.
    eapply CInone; eauto.
    + eapply no_requests_app; auto.
      unfold no_requests; intros.
      channel_crush.
      eauto using recv_handler_cr_None_sends_no_requests.
  - destruct (cur_request st__src') as [[[? ?] ?]|] eqn:?.
    + destruct (addr_eq_dec dst (addr_of p0)); subst.
      * find_copy_eapply_lem_hyp recv_cur_request_changes; eauto.
        break_and; subst.
        assert (request_response_pair req p).
        {
          inv_prop query_message_ok'; repeat find_rewrite || find_injection;
                try congruence.
          - assert (~ no_responses (channel gst (addr_of dstp) h)).
                 {
                   intro; eapply_prop no_responses.
                   chan2msg.
                   repeat find_rewrite.
                   in_crush.
                   eauto.
                 }
                 inv_prop (query_message_ok h (addr_of dstp));
                   try solve [exfalso; eapply_prop not; eauto
                             |congruence].
                 assert (req = req0) by congruence; subst.
                 assert (p = res0).
                 eapply unique_eq; eauto using no_responses_unique, payload_eq_dec.
                 chan2msg; repeat find_rewrite; in_crush.
                 subst; eauto.
          - assert (req = req0) by congruence; subst.
                 assert (p = res0).
                 eapply unique_eq; eauto using no_responses_unique, payload_eq_dec.
                 chan2msg; repeat find_rewrite; in_crush.
          - assert (~ no_responses (channel gst (addr_of dstp) h)).
                 {
                   intro; eapply_prop no_responses.
                   chan2msg.
                   repeat find_rewrite.
                   in_crush.
                   eauto.
                 }
                 exfalso; eauto.
          - assert (In p []).
                 replace [] with (channel gst (addr_of dstp) h) by congruence.
                 chan2msg; repeat find_rewrite; in_crush; intuition eauto.
                 simpl in *; tauto.
          - assert (client_payload p).
                 find_eapply_prop client_payload; chan2msg; eauto.
                 inv_prop client_payload; inv_prop query_response.
        }
        assert (query_request q0 p1).
        {
          eapply recv_handler_query_request_cur_request; eauto.
          congruence.
        }
        assert (In (addr_of p0, p1) ms)
          by eauto using recv_res_new_req_in_channel.
        eapply CIreq; eauto.
        ++ in_crush; left.
           eapply filterMap_In; eauto.
           simpl; break_match; try congruence.
        ++ eapply unique_no_requests.
           eapply unique_app_r; eauto using no_requests_unique.
           eapply filterMap_sends_unique.
           match goal with
           | H: recv_handler ?src _ _ _  = _ |- _ =>
             eapply recv_res_new_req_unique in H; eauto
           end.
      * eapply CIother; eauto.
        -- eapply no_requests_app; auto.
           unfold no_requests; intros.
           channel_crush.
           intro.
           find_eapply_lem_hyp request_sent_by_recv; eauto.
           expand_def; congruence.
        -- eapply recv_handler_query_request_cur_request; eauto.
           congruence.
    + eapply CInone; eauto.
      eapply no_requests_app; eauto.
      unfold no_requests; intros.
      channel_crush.
      eauto using recv_handler_cr_after_None_sends_no_requests.
  - replace (cur_request st__src') with (Some (dstp, q, req))
      by (repeat find_rewrite; symmetry; eauto using recv_msg_not_right_response_from_dst_preserves_cur_request).
    eapply CIreq; eauto; try solve [in_crush].
    eapply unique_no_requests.
    eapply unique_app; eauto using no_requests_unique.
    intros.
    channel_crush; eapply recv_handler_not_response_from_dst_sends_no_requests; eauto.
  - replace (cur_request st__src') with (Some (dstp, q, req))
      by (repeat find_rewrite; symmetry; eauto using recv_msg_not_right_response_from_dst_preserves_cur_request).
    eapply CIres; eauto; try solve [in_crush].
    eapply no_requests_app; eauto.
    unfold no_requests; intros.
    channel_crush; eapply recv_handler_not_response_from_dst_sends_no_requests; eauto.
  - replace (cur_request st__src') with (Some (dstp, q, req))
      by (repeat find_rewrite; symmetry; eauto using recv_msg_not_right_response_from_dst_preserves_cur_request).
    eapply CIdelayed; eauto; try solve [in_crush].
    eapply no_requests_app; eauto.
    unfold no_requests; intros.
    channel_crush; eapply recv_handler_not_response_from_dst_sends_no_requests; eauto.
Qed.

Theorem query_message_ok_recv_src_distinct_recv :
  forall gst gst' src h st p xs ys st' ms nts cts,
    reachable_st gst ->
    step_dynamic gst gst' ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    msgs gst = xs ++ (src, (h, p)) :: ys ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst') ->
    sigma gst h = Some st ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' =
    update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (timeouts gst h)) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = map (send h) ms ++ xs ++ ys ->
    trace gst' = trace gst ++ [e_recv (src, (h, p))] ->
    (forall (dst : addr) (st__src : data),
        sigma gst h = Some st__src ->
        query_message_ok' h dst (cur_request st__src)
                          (option_map delayed_queries (sigma gst dst))
                          (nodes gst') (failed_nodes gst')
                          (channel gst h dst) (channel gst dst h)) ->
    forall (dst : addr) (st__src' st__dst st__dst' : data),
      h <> dst ->
      sigma gst' h = Some st__src' ->
      sigma gst dst = Some st__dst ->
      sigma gst' dst = Some st__dst' ->
      query_message_ok h dst (cur_request st) (delayed_queries st__dst) (channel gst h dst) (channel gst dst h) ->
      ~ In dst (failed_nodes gst') ->
      query_message_ok h dst (cur_request st__src')
                       (delayed_queries st__dst')
                       (channel gst' h dst) (channel gst' dst h).
Proof.
  intros.
  destruct (addr_eq_dec src dst);
    eauto using query_message_ok_recv_src_distinct_recv_same, query_message_ok_recv_src_distinct_recv_other.
Qed.

Lemma recv_requests_only_to_tgt :
  forall st src h p st' ms nts cts dstp q m,
    recv_handler src h st p = (st', ms, nts, cts) ->
    cur_request st' = Some (dstp, q, m) ->
    forall a,
      a <> addr_of dstp ->
      no_requests (filterMap (fun m => if addr_eq_dec (fst m) a then Some (snd m) else None) ms).
Proof.
  unfold no_requests; intros; channel_crush.
  repeat handler_def || handler_simpl || in_crush || inv_prop request_payload.
Qed.

Lemma recv_cr_none_no_requests :
  forall st src h p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    cur_request st' = None ->
    forall a,
      no_requests (filterMap (fun m => if addr_eq_dec (fst m) a then Some (snd m) else None) ms).
Proof.
  unfold no_requests; intros; channel_crush.
  repeat handler_def || handler_simpl || in_crush || inv_prop request_payload.
Qed.

Lemma handle_query_req_busy_only_sends_busy :
  forall src st msg st' ms nts cts,
    handle_query_req_busy src st msg = (st', ms, nts, cts) ->
    forall dst m,
      In (dst, m) ms ->
      m = Busy.
Proof.
  intros.
  handler_def; in_crush; congruence.
Qed.

Lemma do_delayed_queries_no_sends :
  forall h st st' ms nts cts,
    do_delayed_queries h st = (st', ms, nts, cts) ->
    cur_request st' <> None ->
    ms = [].
Proof.
  intros.
  repeat handler_def || handler_simpl.
Qed.

Lemma in_dqs_preserved_if_cr_not_None :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    cur_request st' <> None ->
    forall x,
      In x (delayed_queries st) ->
      In x (delayed_queries st').
Proof.
  intros.
  handler_def.
  assert (In x (delayed_queries x0))
    by eauto using in_dqs_preserved_by_handle_msg.
  clear H.
  repeat handler_def || handler_simpl.
Qed.

Lemma recv_cr_changes_sends_request :
  forall src dst st p st' ms nts cts dstp q m,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    cur_request st' = Some (dstp, q, m) ->
    cur_request st' <> cur_request st ->
    exists req,
      request_payload req /\
      In (addr_of dstp, req) ms.
Proof.
  intros.
  repeat handler_def || handler_simpl.
  exists GetSuccList; intuition eauto.
  left.
  f_equal; congruence.
Qed.

Theorem query_message_ok_recv_src_self_recv :
  forall gst gst' src h st p xs ys st' ms nts cts,
    reachable_st gst ->
    step_dynamic gst gst' ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    msgs gst = xs ++ (src, (h, p)) :: ys ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst') ->
    sigma gst h = Some st ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' =
    update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (timeouts gst h)) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = map (send h) ms ++ xs ++ ys ->
    trace gst' = trace gst ++ [e_recv (src, (h, p))] ->
    query_message_ok h h (cur_request st) (delayed_queries st) (channel gst h h) (channel gst h h) ->
    (forall (dst : addr) (st__src : data),
        sigma gst h = Some st__src ->
        query_message_ok' h dst (cur_request st__src)
                          (option_map delayed_queries (sigma gst dst)) (nodes gst) (failed_nodes gst)
                          (channel gst h dst) (channel gst dst h)) ->
    (forall (dst : addr) (st__src' st__dst' : data),
        sigma gst' h = Some st__src' ->
        ~ In h (failed_nodes gst') ->
        query_message_ok h h (cur_request st__src')
                          (delayed_queries st__src')
                          (channel gst' h h) (channel gst' h h)).
Proof.
  intros.
  inv_prop query_message_ok.
  - find_copy_apply_lem_hyp recv_cur_request_None_preserved; eauto.
    repeat find_rewrite || rewrite_update || find_injection.
    match goal with
    | H: None = _ |- _ => rewrite <- H
    end.
    find_copy_eapply_lem_hyp channel_after_recv_src_dst; eauto; expand_def.
    eapply CInone.
    + unfold no_responses; intuition.
      break_match.
      * subst; repeat find_rewrite.
        find_apply_lem_hyp in_app_or; break_or_hyp.
        -- channel_crush.
           find_eapply_lem_hyp recv_handler_res_only_if_req; eauto.
           expand_def.
           eapply_prop no_requests; eauto.
           find_eapply_prop delayed_queries; eauto.
        -- eapply_prop no_responses; try eassumption; in_crush.
      * rewrite filterMap_all_None in * by eauto; simpl in *.
        assert ((h, h) <> (src, h)) by congruence.
        find_eapply_lem_hyp channel_after_recv_not_src_dst; eauto.
        repeat find_rewrite.
        channel_crush.
        -- find_eapply_lem_hyp recv_handler_res_only_if_req; eauto.
           expand_def.
           find_eapply_prop delayed_queries; eauto.
        -- eapply_prop no_responses; eauto.
    + unfold no_requests; intuition.
      assert (forall to m, In (to, m) ms -> ~ request_payload m).
      {
        intuition.
        find_eapply_lem_hyp request_sent_by_recv; eauto.
        expand_def; try congruence.
      }
      chan2msg; repeat find_rewrite; unfold send in *; in_crush;
        try find_injection; eauto.
      eapply_prop no_requests; chan2msg; repeat find_rewrite; eauto; in_crush.
      eapply_prop no_requests; chan2msg; repeat find_rewrite; eauto; in_crush.
    + find_copy_apply_lem_hyp recv_cr_None_empties_dqs; eauto.
      find_rewrite; eauto.
      congruence.
  - destruct (contains_request_to_dec h ms);
      [|destruct (cur_request st__src') as [[[? ?] ?]|] eqn:?].
    + expand_def.
      find_copy_eapply_lem_hyp request_sent_by_recv; eauto.
      break_exists; break_and.
      assert (exists dstp q,
                 addr_of dstp = h /\
                 cur_request st' = Some (dstp, q, x)).
      {
        expand_def; eauto.
      }
      break_exists; break_and; repeat find_rewrite || rewrite_update || find_injection.
      pose proof (H13 (addr_of x0) st ltac:(auto)).
      eapply CIreq.
      * chan2msg; repeat find_rewrite; in_crush.
      * eapply unique_no_requests.
        erewrite channel_after_recv_not_src_dst; eauto.
        eapply unique_app_r; eauto using no_requests_unique.
        destruct (addr_eq_dec _ _); try congruence.
        eapply filterMap_sends_unique.
        match goal with
        | H: recv_handler ?src _ _ _  = _ |- _ =>
          eapply recv_res_new_req_unique in H; eauto
        end.
        expand_def; find_injection; constructor.
      * unfold no_responses; intros.
        chan2msg; repeat find_rewrite.
        find_apply_lem_hyp in_app_or; break_or_hyp.
        -- eapply recv_no_responses; eauto.
           channel_crush.
        -- eapply_prop no_responses; chan2msg; repeat find_rewrite; in_crush.
      * find_eapply_lem_hyp recv_handler_definition_existential; break_exists; break_and.
        find_copy_apply_lem_hyp do_delayed_queries_definition; break_or_hyp; break_exists; break_and;
          repeat handler_simpl.
        intros.
        destruct (list_eq_dec send_eq_dec (delayed_queries x5) (delayed_queries st)).
        -- repeat find_rewrite; eauto.
        -- find_eapply_lem_hyp handle_msg_dqs_change_queue_for_reqs; eauto; break_exists; break_and.
           repeat find_rewrite.
           find_eapply_lem_hyp in_dedup_was_in.
           simpl in *; break_or_hyp; eauto.
           find_injection; eauto.
      * expand_def; repeat handler_simpl.
    + repeat find_rewrite || rewrite_update || handler_simpl.
      eapply CIother.
      * intro; subst.
        assert (cur_request st__src' <> cur_request st).
        {
          intro; repeat find_rewrite || rewrite_update || handler_simpl.
        }
        repeat find_rewrite || rewrite_update || handler_simpl.
        find_eapply_lem_hyp recv_cr_changes_sends_request; eauto; expand_def.
        eauto.
      * unfold no_responses; intros.
        chan2msg; intros; repeat find_rewrite.
        find_apply_lem_hyp in_app_or; break_or_hyp.
        -- intro.
           channel_crush.
           find_eapply_lem_hyp recv_handler_res_only_if_req; eauto; expand_def.
           eapply_prop no_requests; eauto.
           find_eapply_prop delayed_queries; eauto.
        -- eapply_prop no_responses; chan2msg; repeat find_rewrite; in_crush.
      * unfold no_requests; intros.
        chan2msg; intros; repeat find_rewrite.
        find_apply_lem_hyp in_app_or; break_or_hyp.
        -- intro; channel_crush.
           find_copy_eapply_lem_hyp request_sent_by_recv; eauto; expand_def.
        -- eapply_prop no_requests; chan2msg; repeat find_rewrite; in_crush.
      * handler_def.
        replace (delayed_queries x3) with (delayed_queries x).
        destruct (list_eq_dec send_eq_dec (delayed_queries x) (delayed_queries st)).
        -- repeat find_rewrite; eauto.
        -- find_eapply_lem_hyp handle_msg_dqs_change_queue_for_reqs; eauto.
           break_and.
           intros; repeat find_rewrite.
           intro.
           find_apply_lem_hyp in_dedup_was_in; in_crush; eauto.
           find_injection.
           eapply_prop no_requests; eauto.
        -- match goal with H: context[handle_msg] |- _ => clear H end.
           handler_def; simpl in *; congruence.
      * find_eapply_lem_hyp recv_handler_query_request_cur_request; eauto.
        intros; congruence.
    + eapply CInone.
      * unfold no_responses; intros; chan2msg.
        repeat find_rewrite.
        find_eapply_lem_hyp in_app_or; break_or_hyp.
        -- in_crush.
           unfold send in *; find_injection.
           eapply recv_no_responses; eauto.
           destruct (addr_eq_dec h src); eauto.
           subst; right.
           eapply_prop no_requests.
           chan2msg; eauto.
        -- eapply_prop no_responses.
           chan2msg.
           repeat find_rewrite.
           in_crush.
      * unfold no_requests; intros.
        chan2msg.
        repeat find_rewrite.
        find_eapply_lem_hyp in_app_or; break_or_hyp.
        -- assert (cur_request st' = None)
             by repeat find_rewrite || rewrite_update || handler_simpl.
           channel_crush.
           intro.
           find_copy_eapply_lem_hyp request_sent_by_recv; eauto.
           expand_def; congruence.
        -- eapply_prop no_requests; eauto.
           chan2msg.
           repeat find_rewrite.
           in_crush.
      * intros; intro.
        handler_def.
        repeat find_rewrite || rewrite_update || handler_simpl.
        find_apply_lem_hyp do_delayed_queries_definition; expand_def.
        congruence.
  - repeat find_rewrite || find_injection || rewrite_update.
    destruct (send_eq_dec (src, p) (addr_of dstp, req)).
    + find_injection.
      handler_def.
      find_copy_eapply_lem_hyp channel_after_recv_src_dst; eauto.
      destruct (payload_eq_dec req Ping); subst.
      * repeat handler_def; simpl in *; repeat handler_simpl.
        unfold send in *.
        repeat find_rewrite || find_injection.
        eapply CIres; try constructor; eauto.
        -- repeat find_reverse_rewrite. chan2msg; repeat find_rewrite; in_crush.
        -- eapply unique_no_responses.
           destruct (addr_eq_dec _ _); try congruence.
           eapply unique_cons_add.
           intros.
           find_eapply_prop no_responses; in_crush.
           constructor.
        -- destruct (addr_eq_dec _ _); try congruence.
           unfold no_requests; intros; in_crush;
             solve [inv_prop request_payload
                   |find_eapply_prop no_requests; eauto; in_crush].
      * handler_def; try solve [congruence | inv_prop query_request].
        -- assert (cur_request st = cur_request x3).
           {
             repeat handler_def || handler_simpl.
           }
           repeat find_reverse_rewrite.
           assert (delayed_queries x3 = (addr_of dstp, req) :: dedup send_eq_dec (delayed_queries st)).
           {
             repeat handler_def || handler_simpl.
             - break_match; try eauto.
               repeat find_rewrite; simpl; in_crush.
             - break_match;
                 repeat find_rewrite; simpl; in_crush;
                   exfalso; eauto.
           }
           eapply CIdelayed; eauto.
           ++ repeat find_rewrite.
              simpl; break_match; eauto using dedup_In; in_crush.
           ++ destruct req; simpl in *; congruence.
           ++ intros.
              repeat find_rewrite.
              assert (xs0 = nil).
              {
                destruct xs0; auto.
                simpl in *; find_injection.
                assert (In (addr_of dstp, req) (delayed_queries st)).
                eapply in_dedup_was_in with (A_eq_dec := send_eq_dec).
                repeat find_rewrite; in_crush.
                exfalso; find_eapply_prop delayed_queries; eauto.
              }
              subst; simpl in *; find_injection.
              intro.
              find_eapply_prop delayed_queries; eauto using in_dedup_was_in.
           ++ repeat find_rewrite.
              eapply no_responses_app.
              ** destruct (addr_eq_dec (addr_of dstp) (addr_of dstp)); try congruence.
                 find_copy_eapply_lem_hyp do_delayed_queries_no_sends; eauto.
                 repeat find_rewrite; simpl.
                 unfold no_responses; intros; channel_crush;
                   find_eapply_lem_hyp handle_query_req_busy_only_sends_busy; eauto; subst; intro; inv_prop response_payload.
              ** unfold no_responses; intros.
                 find_eapply_prop no_responses.
                 in_crush.
           ++ repeat find_rewrite.
              eapply no_requests_app; eauto.
              destruct (addr_eq_dec (addr_of dstp) (addr_of dstp)); try congruence.
              find_copy_eapply_lem_hyp do_delayed_queries_no_sends; eauto.
              repeat find_rewrite; simpl.
              unfold no_requests; intros; channel_crush;
                find_eapply_lem_hyp handle_query_req_busy_only_sends_busy; eauto; subst;
                  intro; inv_prop request_payload.
        -- destruct req; simpl in *; try solve [congruence | inv_prop query_request].
    + assert (cur_request st = cur_request st__src').
      {
        symmetry; eapply recv_handler_not_response_from_dst_preserves_cur_request; intuition eauto.
        destruct (addr_eq_dec src (addr_of dstp)); try eauto.
        subst.
        left; intros.
        find_eapply_prop no_responses.
        chan2msg.
        repeat find_rewrite.
        in_crush.
        eauto.
      }
      assert (addr_of dstp <> src \/ ~ request_payload p).
      {
        destruct (addr_eq_dec (addr_of dstp) src); eauto.
        subst; right; intuition.
        cut (p = req); [intro; subst; eauto|].
        eapply unique_eq.
        eapply no_requests_unique; eauto.
        eapply payload_eq_dec.
        eauto.
        chan2msg; eauto.
        chan2msg; eauto.
      }
      repeat find_reverse_rewrite.
      eapply CIreq.
      -- chan2msg; repeat find_rewrite.
         in_crush;
         find_injection;
         exfalso; eauto.
      -- eapply unique_no_requests.
         destruct (addr_eq_dec (addr_of dstp) src); subst.
         ++ find_eapply_lem_hyp channel_after_recv_src_dst; eauto.
            break_exists; break_and.
            repeat find_rewrite.
            eapply unique_app; eauto using no_requests_unique, unique_remove.
            intros.
            find_apply_lem_hyp In_filterMap.
            break_exists; break_and.
            repeat break_match; try congruence.
            destruct x1; repeat handler_simpl.
            eapply recv_handler_not_response_from_dst_sends_no_requests; eauto.
            repeat find_rewrite; eauto.
            left.
            intro.
            eapply_prop no_responses.
            instantiate (1:=p).
            eauto.
            eauto.
         ++ erewrite channel_after_recv_not_src_dst; eauto.
            eapply unique_app; eauto using no_requests_unique.
            intros.
            channel_crush;
              eapply recv_handler_not_response_from_dst_sends_no_requests; eauto.
      -- unfold no_responses; intros; chan2msg; repeat find_rewrite.
         find_apply_lem_hyp in_app_or.
         break_or_hyp.
         ++ find_apply_lem_hyp in_map_iff; break_exists; break_and; unfold send in *.
            find_injection.
            eapply recv_no_responses; eauto.
         ++ find_eapply_prop no_responses; chan2msg; repeat find_rewrite; in_crush.
      -- find_eapply_lem_hyp recv_handler_definition_existential; break_exists; break_and.
         repeat handler_simpl.
         assert (x3 = x); subst.
         {
           match goal with H:context[handle_msg] |- _ => clear H end.
           repeat handler_def || handler_simpl.
         }
         destruct (list_eq_dec send_eq_dec (delayed_queries x) (delayed_queries st)).
         repeat find_reverse_rewrite; auto.
         find_eapply_lem_hyp handle_msg_dqs_change_queue_for_reqs; eauto.
         break_and.
         intuition.
         repeat find_rewrite.
         find_apply_lem_hyp in_dedup_was_in; in_crush; try find_injection; eauto.
      -- eauto.
  - destruct (send_eq_dec (src, p) (addr_of dstp, res0)).
    + repeat find_rewrite || find_injection || rewrite_update.
      find_copy_eapply_lem_hyp channel_after_recv_src_dst; eauto.
      assert (no_responses (channel gst' (addr_of dstp) (addr_of dstp))).
      {
        unfold no_responses; intros.
        expand_def.
        repeat find_rewrite; channel_crush;
          try solve [eapply recv_no_responses; eauto
                    |find_eapply_prop no_responses; eauto; in_crush].
      }
      expand_def.
      assert (no_requests (x ++ x0)).
      {
        repeat find_rewrite.
        eapply no_requests_app.
        eapply (app_no_requests x (res0::x0)); eauto.
        eapply cons_no_requests.
        eapply (app_no_requests x (res0::x0)); eauto.
      }
      destruct (cur_request st__src') as [[[? ?] ?]|] eqn:?.
      * destruct (addr_eq_dec (addr_of dstp) (addr_of p)).
        -- repeat find_rewrite.
           eapply CIreq; auto.
           ++ expand_def.
              destruct (addr_eq_dec _ _); try congruence.
              repeat find_rewrite.
              eapply in_or_app; left.
              repeat find_reverse_rewrite.
              find_eapply_lem_hyp recv_res_new_req_in_channel; eauto.
              eapply filterMap_In; eauto.
              simpl; destruct (addr_eq_dec _ _); try congruence.
           ++ eapply unique_no_requests.
              expand_def.
              destruct (addr_eq_dec _ _); try congruence.
              repeat find_rewrite.
              eapply unique_app_r.
              eapply filterMap_sends_unique.
              match goal with
              | H: recv_handler ?src _ _ _  = _ |- _ =>
                replace src with (addr_of dstp) in H;
                  eapply recv_res_new_req_unique in H; eauto
              end.
              inv_prop request_response_pair; inv_prop query_request; constructor.
              intros.
              eapply_prop no_requests.
              in_crush.
           ++ handler_def.
              intros.
              find_eapply_lem_hyp handle_msg_only_appends_incoming_req_to_delayed_queries_when_busy; eauto; expand_def; eauto;
                handler_def; repeat find_rewrite; simpl in *; eauto;
                  intuition eauto using in_dedup_was_in. 
           ++ eapply recv_handler_query_request_cur_request; eauto.
              intros.
              repeat find_rewrite || find_injection; eauto.
        -- eapply CIother; eauto.
           ++ expand_def; repeat find_rewrite.
              destruct (addr_eq_dec _ _); try congruence.
              eapply no_requests_app; auto.
              eapply recv_requests_only_to_tgt; eauto.
           ++ handler_def.
              intros.
              find_eapply_lem_hyp handle_msg_only_appends_incoming_req_to_delayed_queries_when_busy; eauto; expand_def; eauto;
                handler_def; repeat find_rewrite; simpl in *; eauto;
                  intuition eauto using in_dedup_was_in. 
           ++ eapply recv_handler_query_request_cur_request; eauto.
              intros.
              repeat find_rewrite || find_injection; eauto.
      * eapply CInone; eauto.
        -- expand_def.
           repeat find_rewrite.
           destruct (addr_eq_dec _ _) in *; try congruence.
           eapply no_requests_app; auto.
           eapply recv_cr_none_no_requests; eauto.
        -- erewrite recv_cr_None_empties_dqs by eauto.
           eauto.
    + assert (~ query_response q p \/ src <> addr_of dstp).
      {
        repeat find_rewrite || rewrite_update || find_injection.
        destruct (addr_eq_dec src (addr_of dstp)).
        - subst; left.
          intro.
          cut (p = res0); [intro; subst; eauto|].
          eapply unique_eq; eauto using no_responses_unique, payload_eq_dec.
        - auto. 
      }
      assert (cur_request st = cur_request st__src').
      {
        repeat find_rewrite || rewrite_update || find_injection.
        symmetry.
        eapply recv_handler_not_response_from_dst_preserves_cur_request; eauto.
      }
      repeat find_reverse_rewrite.
      assert (unique response_payload (channel gst' (addr_of dstp) (addr_of dstp)) res0).
      {
        destruct (addr_eq_dec src (addr_of dstp)); subst.
        - break_or_hyp; try congruence.
          find_eapply_lem_hyp channel_after_recv_src_dst; eauto.
          expand_def; repeat find_rewrite.
          eapply unique_app.
          eauto using unique_remove, no_responses_unique.
          intros.
          channel_crush; eapply recv_no_responses; eauto.
        - erewrite channel_after_recv_not_src_dst; try eassumption || congruence.
          eapply unique_app; eauto using no_responses_unique.
          intros.
          channel_crush; eapply recv_no_responses; eauto.
      }
      eapply CIres; eauto.
      * chan2msg; repeat find_rewrite; in_crush;
          find_injection; exfalso; auto.
      * eapply unique_no_responses; eauto.
      * unfold no_requests; intros; chan2msg.
        repeat find_rewrite.
        find_eapply_lem_hyp in_app_or; break_or_hyp; eauto.
        -- find_apply_lem_hyp in_map_iff; break_exists; break_and.
           unfold send in *; find_injection.
           eapply recv_handler_not_response_from_dst_sends_no_requests; eauto.
           repeat find_rewrite; eauto.
        -- find_eapply_prop no_requests.
           chan2msg.
           repeat find_rewrite.
           in_crush.
      * match goal with
        | H: context[query_response] |- _ => clear H
        end.
        handler_def.
        find_apply_lem_hyp do_delayed_queries_definition; expand_def;
          repeat find_rewrite || find_injection || rewrite_update;
          eauto.
        destruct (list_eq_dec send_eq_dec (delayed_queries st__src') (delayed_queries st)).
        -- repeat find_rewrite; eauto.
        -- find_eapply_lem_hyp handle_msg_dqs_change_queue_for_reqs; eauto; expand_def.
           intuition.
           repeat find_rewrite.
           find_eapply_lem_hyp in_dedup_was_in.
           in_crush; eauto.
           find_injection.
           eapply_prop no_requests; [|eauto]; eauto.
  - assert (src <> addr_of dstp \/ ~ query_response q p).
    {
      destruct (addr_eq_dec src (addr_of dstp)); eauto; subst.
      right; intro.
      find_eapply_prop no_responses.
      instantiate (1 := p).
      eauto.
      eauto.
    }
    assert (src <> addr_of dstp \/ ~ request_payload p).
    {
      destruct (addr_eq_dec src (addr_of dstp)); eauto; subst.
      right; intro.
      find_eapply_prop no_requests.
      instantiate (1 := p).
      eauto.
      eauto.
    }
    assert (cur_request st' = cur_request st)
      by eauto using recv_msg_not_right_response_from_dst_preserves_cur_request.
    repeat find_rewrite || rewrite_update || find_injection.
    replace (cur_request st) with (Some (dstp, q, req)) by congruence.
    eapply CIdelayed.
    + eapply in_dqs_preserved_if_cr_not_None; eauto.
    + eauto.
    + eapply from_src_unique.
      find_apply_lem_hyp recv_handler_definition_existential; break_exists; break_and.
      repeat handler_simpl.
      assert (delayed_queries x = delayed_queries x3).
      {
        match goal with H: context[handle_msg] |- _ => clear H end.
        handler_def; eauto; simpl in *; congruence.
      }
      destruct (list_eq_dec send_eq_dec (delayed_queries x) (delayed_queries st)).
      * repeat find_rewrite; eauto.
      * find_eapply_lem_hyp handle_msg_dqs_change_queue_for_reqs; eauto.
        break_and.
        repeat find_rewrite.
        eapply unique_dedup.
        eapply unique_cons; eauto.
        simpl.
        destruct (addr_eq_dec src (addr_of dstp)); auto.
        subst; tauto.
    + unfold no_responses; intros; chan2msg.
      repeat find_rewrite.
      find_apply_lem_hyp in_app_or; break_or_hyp.
      channel_crush; eapply recv_no_responses; eauto.
      find_eapply_prop no_responses; chan2msg; repeat find_rewrite; in_crush.
    + destruct (addr_eq_dec src (addr_of dstp)); subst.
      * find_eapply_lem_hyp channel_after_recv_src_dst; eauto.
        break_exists; break_and.
        repeat find_rewrite.
        eapply no_requests_app.
        unfold no_requests; intros.
        channel_crush; eauto using recv_handler_not_response_from_dst_sends_no_requests.
        find_eapply_lem_hyp app_no_requests; break_and.
        find_eapply_lem_hyp cons_no_requests; break_and.
        eapply no_requests_app; auto.
      * erewrite channel_after_recv_not_src_dst by eauto.
        eapply no_requests_app; auto.
        unfold no_requests; intros.
        channel_crush; eauto using recv_handler_not_response_from_dst_sends_no_requests.
    + eauto using recv_handler_not_response_from_dst_sends_no_requests.
Qed.

Theorem query_message_ok'_recv_src_recv :
  forall gst gst' src h st p xs ys st' ms nts cts,
    reachable_st gst ->
    step_dynamic gst gst' ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    msgs gst = xs ++ (src, (h, p)) :: ys ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst') ->
    sigma gst h = Some st ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' =
    update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (timeouts gst h)) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = map (send h) ms ++ xs ++ ys ->
    trace gst' = trace gst ++ [e_recv (src, (h, p))] ->
    (forall (dst : addr) (st__src : data),
        sigma gst h = Some st__src ->
        query_message_ok' h dst (cur_request st__src)
                          (option_map delayed_queries (sigma gst dst)) (nodes gst) (failed_nodes gst)
                          (channel gst h dst) (channel gst dst h)) ->
    forall (dst : addr) (st__src' : data),
        sigma gst' h = Some st__src' ->
        query_message_ok' h dst (cur_request st__src')
                          (option_map delayed_queries (sigma gst' dst)) (nodes gst') (failed_nodes gst')
                          (channel gst' h dst) (channel gst' dst h).
Proof.
  autounfold; intros.
  assert (reachable_st gst')
    by solve [econstructor; eauto].
  match goal with
  | H: _ |- _ => pose proof H as ?; specialize (H dst st); conclude H eassumption
  end.
  repeat find_rewrite; simpl in *.
  inv_prop query_message_ok'; try tauto; inv_option_map.
  - update_destruct; rewrite_update; subst.
    + simpl.
      eapply QMLive; auto.
      find_injection.
      eapply query_message_ok_recv_src_self_recv with (gst:=gst) (gst':=gst'); eauto;
        try congruence.
      repeat find_rewrite; rewrite_update; auto.
      repeat find_rewrite; rewrite_update; auto.
    + simpl.
      replace (sigma gst dst) with (Some x) by congruence; simpl.
      eapply QMLive; auto.
      eapply query_message_ok_recv_src_distinct_recv with (gst:=gst) (gst':=gst'); eauto;
        try congruence.
      repeat find_rewrite || find_injection.
      repeat find_rewrite; rewrite_update; eauto.
      repeat find_rewrite; rewrite_update; eauto.
      repeat find_rewrite; rewrite_update; eauto.
  - update_destruct;
      try solve [exfalso; subst; eauto].
    rewrite_update; repeat find_rewrite; simpl in *.
    destruct (is_response_from_dec (addr_of dstp) p src).
    + break_and; subst.
      find_eapply_lem_hyp channel_after_recv_src_dst; eauto.
      expand_def.
      destruct (addr_eq_dec (addr_of dstp) h); try congruence.
      rewrite filterMap_all_None in * by auto.
      simpl in *.
      repeat find_rewrite.
      assert (p = res0).
      {
        eapply unique_eq; eauto.
        eapply no_responses_unique; repeat find_rewrite; eauto.
        apply payload_eq_dec.
        repeat find_rewrite; auto.
      }
      subst; eauto.
      eapply QMFailedNothing; eauto.
      find_injection.
      eapply recv_handler_query_request_cur_request; eauto.
      intros.
      repeat find_rewrite || find_injection; eauto.
    + find_injection.
      assert (cur_request st__src' = cur_request st).
      {
        eapply recv_handler_not_response_from_dst_preserves_cur_request; intuition eauto.
      }
      replace (cur_request st__src') with (Some (dstp, q, req)) by congruence.
      eapply QMFailedRes; eauto.
      * chan2msg.
        repeat find_rewrite.
        apply in_or_app; right.
        in_crush;
          solve [eauto
                |find_injection; exfalso; eauto].
      * destruct (addr_eq_dec (addr_of dstp) src);
          try solve [erewrite channel_after_recv_unrelated; eauto].
        subst.
        eapply unique_no_responses.
        find_eapply_lem_hyp no_responses_unique; eauto.
        find_eapply_lem_hyp channel_after_recv_src_dst; eauto.
        expand_def.
        destruct (addr_eq_dec (addr_of dstp) h); try congruence.
        rewrite filterMap_all_None in * by auto.
        simpl in *.
        repeat find_rewrite.
        eapply unique_remove; eauto.
      * unfold no_requests in *; intros; intro.
        chan2msg.
        repeat find_rewrite.
        find_apply_lem_hyp in_app_or; break_or_hyp;
          [|find_apply_lem_hyp in_app_or; break_or_hyp].
        -- find_apply_lem_hyp in_map_iff; break_exists; break_and.
           unfold send in *; find_injection.
           eapply recv_handler_not_response_from_dst_sends_no_requests; intuition eauto.
        -- find_eapply_prop request_payload; eauto.
           chan2msg; repeat find_rewrite; eauto.
           in_crush; eauto.
        -- find_eapply_prop request_payload; eauto.
           chan2msg; repeat find_rewrite; eauto.
           in_crush; eauto.
  - update_destruct;
      try solve [exfalso; subst; eauto].
    rewrite_update; repeat find_rewrite.
    simpl.
    eapply QMFailedNothing; eauto.
    + unfold no_responses in *; intros.
      find_eapply_lem_hyp channel_after_recv_from_not_dst; eauto.
    + repeat find_injection.
      eapply recv_handler_query_request_cur_request; eauto.
  - update_destruct;
      try solve [exfalso; subst; eauto].
    rewrite_update; repeat find_rewrite.
    simpl.
    assert ([] = channel gst' dst h).
    {
      symmetry; eapply no_elements_nil.
      intuition; chan2msg.
      destruct (client_payload_dec x).
      - find_eapply_lem_hyp sent_client_message_means_client_or_in_nodes; eauto.
        repeat find_rewrite; tauto.
      - find_eapply_lem_hyp sent_non_client_message_means_in_nodes; try eassumption.
        repeat find_rewrite; tauto.
    }
    assert ([] = channel gst' h dst).
    {
      symmetry; eapply no_elements_nil.
      intuition; chan2msg.
      find_eapply_lem_hyp non_client_msgs_out_of_net_go_to_clients; eauto.
      repeat find_rewrite; eauto.
    }
    repeat replace (channel _ _ _) with (@nil payload) by congruence.
    eapply QMNotStarted; eauto.
    intros; split.
    + find_injection.
      eapply recv_handler_query_request_cur_request; try eassumption.
      intros.
      find_eapply_prop query_request; eauto.
    + intro; subst.
      find_eapply_prop nodes.
      replace (nodes gst) with (nodes gst') by congruence.
      eapply cur_request_targets_in_nodes; try eassumption.
      repeat find_rewrite; rewrite_update; eauto.
  - repeat find_rewrite || rewrite_update; simpl.
    eapply QMClient; eauto.
    + eauto using channel_after_recv_from_not_dst.
    + intros; chan2msg; repeat find_rewrite; in_crush;
        try solve [find_eapply_prop Busy; chan2msg; repeat find_rewrite; in_crush].
      unfold send in *; find_injection.
      find_copy_apply_lem_hyp recv_handler_definition_existential; eauto; expand_def.
      repeat find_rewrite || find_injection.
      in_crush.
      * find_eapply_lem_hyp do_delayed_queries_only_responds; eauto.
      * assert (request_payload p0 \/ ~ request_payload p0)
          by (destruct p0; intuition eauto; right; intros; inv_prop request_payload).
        break_or_hyp.
        -- find_eapply_lem_hyp handle_msg_sets_cur_request_when_sending_request; eauto.
           expand_def.
           find_copy_apply_lem_hyp cur_request_preserved_by_do_delayed_queries.
           repeat find_rewrite.
           assert (In (addr_of x3) (nodes gst')).
           {
             eapply (cur_request_targets_in_nodes gst' h); eauto.
             repeat find_rewrite; rewrite_update; eauto.
           }
           exfalso; eapply nodes_not_clients; eauto.
        -- destruct p0;
             try solve [eauto
                       |exfalso; find_eapply_prop request_payload; eauto].
           eapply_lem_prop_hyp notify_means_dst_is_in_succs recv_handler; in_crush; eauto.
           expand_def.
           exfalso.
           eapply nodes_not_clients; eauto.
           eapply (successors_in_nodes gst' h st__src'); eauto;
             repeat find_rewrite; try rewrite_update; eauto.
           in_crush.
Qed.

Theorem query_message_ok'_recv_other_recv :
  forall gst gst' src h st p xs ys st' ms nts cts,
    reachable_st gst ->
    step_dynamic gst gst' ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    msgs gst = xs ++ (src, (h, p)) :: ys ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst') ->
    sigma gst h = Some st ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' =
    update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (timeouts gst h)) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = map (send h) ms ++ xs ++ ys ->
    trace gst' = trace gst ++ [e_recv (src, (h, p))] ->
    (forall (src dst : addr) (st__src : data),
        sigma gst src = Some st__src ->
        h <> src ->
        h <> dst ->
        query_message_ok' src dst (cur_request st__src)
                          (option_map delayed_queries (sigma gst dst)) (nodes gst) (failed_nodes gst)
                          (channel gst src dst) (channel gst dst src)) ->
    (forall (src dst : addr) (st__src : data),
        sigma gst' src = Some st__src ->
        h <> src ->
        h <> dst ->
        query_message_ok' src dst (cur_request st__src)
                          (option_map delayed_queries (sigma gst' dst)) (nodes gst') (failed_nodes gst')
                          (channel gst' src dst) (channel gst' dst src)).
Proof.
  autounfold; intros.
  erewrite !(channel_msgs_remove_send_unchanged gst gst') by eauto.
  repeat find_rewrite || rewrite_update; eauto.
Qed.

Theorem query_message_ok'_recv_invariant :
 chord_recv_handler_invariant
   (fun g : global_state =>
    forall (src dst : addr) (st__src : data),
    sigma g src = Some st__src ->
    query_message_ok' src dst (cur_request st__src)
      (option_map delayed_queries (sigma g dst)) (nodes g) (failed_nodes g)
      (channel g src dst) (channel g dst src)).
Proof.
  repeat autounfold; intros.
  destruct (addr_eq_dec h src0); subst;
    [|destruct (addr_eq_dec h dst); subst].
  - eapply query_message_ok'_recv_src_recv; eauto.
  - eapply query_message_ok'_recv_dst_recv; eauto.
  - eapply query_message_ok'_recv_other_recv; eauto.
Qed.

Definition option_bind {A B : Type} (f : A -> option B) (a : option A) : option B :=
  match a with
  | Some a => f a
  | None => None
  end.

Lemma query_message_ok_Busy_invariant :
  forall gst gst' src dst st__src st__dst h ms,
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst dst = Some st__dst ->
    sigma gst src = Some st__src ->
    sigma gst' src = Some st__src ->
    timeouts gst' =
    update addr_eq_dec (timeouts gst) h
           (KeepaliveTick :: remove timeout_eq_dec KeepaliveTick (timeouts gst h)) ->
    msgs gst' = map (send h) ms ++ msgs gst ->
    Forall (fun x => snd x = Busy) ms ->
    query_message_ok src dst (cur_request st__src) (delayed_queries st__dst)
                     (channel gst src dst) (channel gst dst src) ->
    query_message_ok src dst (cur_request st__src) (delayed_queries st__dst)
                     (channel gst' src dst) (channel gst' dst src).
Proof.
  intros.
  rewrite Forall_forall in *.
  inv_prop query_message_ok.
  - constructor; eauto.
    + unfold no_responses.
      intros.
      chan2msg.
      find_rewrite.
      in_crush.
      unfold send in *.
      find_injection.
      * assert (m = Busy)
          by (change m with (snd (src, m)); eauto).
        invcs_prop response_payload; congruence.
      * find_eapply_prop no_responses; eauto.
    + unfold no_requests.
      intros.
      chan2msg.
      repeat find_rewrite.
      in_crush.
      * unfold send in *; find_injection.
        inv_prop request_payload;
          find_apply_hyp_hyp; simpl in *; congruence.
      * find_eapply_prop no_requests; eauto.
  - constructor 2; eauto.
    + unfold no_responses.
      intros.
      chan2msg.
      find_rewrite.
      in_crush.
      unfold send in *.
      find_injection.
      * assert (m = Busy)
          by (change m with (snd (src, m)); eauto).
        invcs_prop response_payload; congruence.
      * find_eapply_prop no_responses; eauto.
    + unfold no_requests.
      intros.
      chan2msg.
      repeat find_rewrite.
      in_crush.
      * unfold send in *; find_injection.
        inv_prop request_payload;
          find_apply_hyp_hyp; simpl in *; congruence.
      * find_eapply_prop no_requests; eauto.
  - constructor 3; eauto.
    + chan2msg; find_rewrite; in_crush.
    + eapply unique_no_requests.
      find_apply_lem_hyp no_requests_unique; eauto.
      destruct (addr_eq_dec src h).
      * subst.
        erewrite channel_app in * by eauto.
        eapply unique_app; eauto.
        intros.
        find_apply_lem_hyp In_filterMap; expand_def.
        break_match; try congruence.
        find_injection.
        replace (snd x) with Busy; [|symmetry; eauto].
        intuition; inv_prop request_payload.
      * erewrite channel_msgs_unchanged; eauto.
    + unfold no_responses.
      intros.
      chan2msg.
      repeat find_rewrite.
      in_crush.
      * unfold send in *; find_injection.
        inv_prop response_payload;
          find_apply_hyp_hyp; simpl in *; congruence.
      * find_eapply_prop no_responses; eauto.
  - econstructor 4; eauto.
    + chan2msg; repeat find_rewrite; in_crush.
    + eapply unique_no_responses.
      find_apply_lem_hyp no_responses_unique; eauto.
      destruct (addr_eq_dec (addr_of dstp) h).
      * subst.
        erewrite channel_app in * by eauto.
        eapply unique_app; eauto.
        intros.
        find_apply_lem_hyp In_filterMap; expand_def.
        break_match; try congruence.
        find_injection.
        replace (snd x) with Busy; [|symmetry; eauto].
        intuition; inv_prop response_payload.
      * erewrite channel_msgs_unchanged; eauto.
    + unfold no_requests.
      intros.
      chan2msg.
      find_rewrite.
      in_crush.
      unfold send in *.
      find_injection.
      * assert (m = Busy)
          by (change m with (snd (addr_of dstp, m)); eauto).
        invcs_prop request_payload; congruence.
      * find_eapply_prop no_requests; eauto.
  - econstructor 5; eauto.
    + unfold no_responses.
      intros.
      chan2msg.
      find_rewrite.
      in_crush.
      unfold send in *.
      find_injection.
      * assert (m = Busy)
          by (change m with (snd (src, m)); eauto).
        invcs_prop response_payload; congruence.
      * find_eapply_prop no_responses; eauto.
    + unfold no_requests.
      intros.
      chan2msg.
      find_rewrite.
      in_crush.
      unfold send in *.
      find_injection.
      * assert (m = Busy)
          by (change m with (snd (addr_of dstp, m)); eauto).
        invcs_prop request_payload; congruence.
      * find_eapply_prop no_requests; eauto.
Qed.

Lemma send_keepalives_Busy_only :
  forall st m,
    In m (send_keepalives st) ->
    snd m = Busy.
Proof.
  unfold send_keepalives.
  intros.
  find_apply_lem_hyp in_map_iff; expand_def.
  reflexivity.
Qed.
Hint Resolve send_keepalives_Busy_only.

Lemma send_keepalives_delayed_only :
  forall st m,
    In m (send_keepalives st) ->
    exists q, In q (delayed_queries st) /\ fst q = fst m.
Proof.
  unfold send_keepalives.
  intros.
  find_apply_lem_hyp in_map_iff; expand_def.
  eauto.
Qed.

Theorem query_message_ok'_keepalive_invariant :
 chord_keepalive_invariant
   (fun g : global_state =>
    forall (src dst : addr) (st__src : data),
      sigma g src = Some st__src ->
      query_message_ok' src dst (cur_request st__src)
      (option_map delayed_queries (sigma g dst)) (nodes g) (failed_nodes g)
      (channel g src dst) (channel g dst src)).
Proof.
  repeat autounfold; intros.
  repeat handler_def || handler_simpl.
  assert (Hst: forall h, sigma gst h = sigma gst' h).
  {
    intros.
    repeat find_rewrite.
    update_destruct; rewrite_update; congruence.
  }
  assert (query_message_ok' src dst (cur_request st__src) (option_map delayed_queries (sigma gst dst))
    (nodes gst) (failed_nodes gst) (channel gst src dst) (channel gst dst src)).
  eapply H12.
  repeat find_rewrite.
  repeat rewrite Hst; auto.
  assert (no_responses (channel gst dst src) ->
          no_responses (channel gst' dst src)).
  {
    unfold no_responses.
    intros.
    chan2msg.
    repeat find_rewrite; in_crush; eauto.
    unfold send in *; find_injection.
    unfold send_keepalives in *.
    in_crush.
    find_injection; inv_prop response_payload.
  }
  assert (no_requests (channel gst src dst) ->
          no_requests (channel gst' src dst)).
  {
    unfold no_requests.
    intros.
    chan2msg.
    repeat find_rewrite; in_crush; eauto.
    unfold send in *; find_injection.
    unfold send_keepalives in *.
    in_crush.
    find_injection; inv_prop request_payload.
  }
  assert (forall p, unique request_payload (channel gst src dst) p ->
               unique request_payload (channel gst' src dst) p).
  {
    intros.
    repeat find_rewrite.
    destruct (addr_eq_dec h src); eauto.
    - subst.
      erewrite channel_app; eauto.
      apply unique_app; auto.
      intros.
      find_apply_lem_hyp In_filterMap.
      break_exists; break_and; break_match; try congruence.
      unfold send_keepalives in *.
      in_crush; intros.
      find_injection; inv_prop request_payload.
    - erewrite (channel_msgs_unchanged _ gst' gst); eauto.
  }
  assert (forall p, unique response_payload (channel gst dst src) p ->
               unique response_payload (channel gst' dst src) p).
  {
    intros.
    repeat find_rewrite.
    destruct (addr_eq_dec h dst); eauto.
    - subst.
      erewrite (channel_app gst gst'); eauto.
      apply unique_app; auto.
      intros.
      find_apply_lem_hyp In_filterMap.
      break_exists; break_and; break_match; try congruence.
      unfold send_keepalives in *.
      in_crush; intros.
      find_injection; inv_prop response_payload.
    - erewrite (channel_msgs_unchanged _ gst' gst); eauto.
  }
  assert (forall src dst p, In p (channel gst src dst) ->
                       In p (channel gst' src dst)).
  {
    intros.
    destruct (addr_eq_dec h src0); eauto; intros.
    - subst.
      erewrite (channel_app gst gst'); eauto.
      in_crush; eauto.
    - erewrite (channel_msgs_unchanged _ gst' gst); eauto.
  }
  inv_prop query_message_ok'.
  -
    find_copy_apply_lem_hyp nodes_have_state; expand_def; auto.
    assert (exists st, sigma gst' dst = Some st); expand_def.
    eapply nodes_have_state; solve [congruence || econstructor; eauto].
    repeat find_rewrite.
    simpl.
    constructor 1; try congruence.
    eapply query_message_ok_Busy_invariant.
    symmetry; eauto.
    all:congruence || eauto.
    apply Forall_forall; eauto.
    replace (delayed_queries x0) with dqs; eauto.
    inv_option_map; repeat find_rewrite || find_injection.
    congruence.
  - unfold option_map in *.
    repeat break_match; try find_injection;
      rewrite Hst in *;
      try assert (d0 = d) by congruence; subst;
       solve [congruence | econstructor; congruence || eauto using unique_no_responses, no_responses_unique].
  - unfold option_map in *.
    repeat break_match; try find_injection;
      rewrite Hst in *;
      try assert (d0 = d) by congruence; subst;
       solve [congruence | econstructor; congruence || eauto using unique_no_responses, no_responses_unique].
  - inv_option_map.
    assert (dst <> h) by (intro; subst; intuition).
    erewrite channel_msgs_unchanged with (src := dst); eauto.
    repeat find_rewrite.
    replace (channel gst dst src) with (@nil payload) by auto.
    assert (channel gst' src dst = channel gst src dst).
    {
      destruct (addr_eq_dec src h).
      - subst.
        erewrite channel_app with (gst := gst) (gst' := gst'); eauto.
        rewrite filterMap_all_None; auto.
        intros.
        break_match; try auto; subst.
        find_apply_lem_hyp send_keepalives_delayed_only; expand_def.
        destruct x0, x; simpl in *; subst.
        find_copy_eapply_lem_hyp delayed_query_sources_active_or_clients; eauto.
        tauto.
      - erewrite channel_msgs_unchanged; eauto.
    }
    congruence.
  - inv_option_map.
    assert (dst <> h)
      by (intro; subst; eapply nodes_not_clients; eauto).
    erewrite channel_msgs_unchanged with (src := dst); eauto.
    repeat find_rewrite || rewrite_update.
    eapply QMClient; eauto.
    intros.
    destruct (addr_eq_dec src h); subst.
    + erewrite channel_app with (dst := dst) (src := h) (gst' := gst') in * |-; eauto.
      in_crush; eauto.
      find_apply_lem_hyp In_filterMap; expand_def; eauto.
      break_match; congruence || find_injection.
      left; eauto.
    + erewrite channel_msgs_unchanged in * by eauto.
      eauto.
Qed.

Lemma delayed_queries_preserved_by_do_rectify :
  forall h st st' ms nts cts eff,
    do_rectify h st = (st', ms, nts, cts, eff) ->
    delayed_queries st = delayed_queries st'.
Proof.
  intros.
  repeat handler_def || handler_simpl.
Qed.

Lemma state_none_not_in_nodes :
  forall gst h,
    reachable_st gst ->
    sigma gst h = None ->
    ~ In h (nodes gst).
Proof.
  intuition.
  find_eapply_lem_hyp nodes_have_state; auto.
  expand_def; congruence.
Qed.

Lemma no_responses_nil :
  no_responses [].
Proof.
  unfold no_responses; in_crush.
Qed.
Hint Resolve no_responses_nil.

Lemma no_requests_nil :
  no_requests [].
Proof.
  unfold no_requests; in_crush.
Qed.
Hint Resolve no_requests_nil.

Theorem query_message_ok'_rectify_invariant :
 chord_rectify_invariant
   (fun g : global_state =>
    forall src dst st__src,
    sigma g src = Some st__src ->
    query_message_ok' src dst (cur_request st__src)
      (option_map delayed_queries (sigma g dst)) (nodes g) (failed_nodes g) (channel g src dst)
      (channel g dst src)).
Proof.
  repeat autounfold; intros.
  destruct (sigma gst src) as [oldst__src|] eqn:?;
    [|repeat find_rewrite; update_destruct; rewrite_update; try congruence].
  remember (sigma gst dst) as oldst__dst.
  assert (query_message_ok' src dst (cur_request oldst__src) (option_map delayed_queries (sigma gst dst))
             (nodes gst) (failed_nodes gst) (channel gst src dst) (channel gst dst src))
    by auto.
  assert (Hst: forall h st,
             sigma gst h = Some st ->
             exists st', sigma gst' h = Some st').
  {
    intros.
    repeat find_rewrite.
    update_destruct; rewrite_update; eexists; eauto.
  }
  assert (Hdq: forall h st st',
             sigma gst h = Some st ->
             sigma gst' h = Some st' ->
             delayed_queries st = delayed_queries st').
  {
    intros.
    find_rewrite.
    update_destruct; rewrite_update; try congruence.
    subst; repeat find_rewrite || find_injection.
    eauto using delayed_queries_preserved_by_do_rectify.
  }
  assert (forall src dst,
             no_responses (channel gst dst src) ->
             no_responses (channel gst' dst src)).
  {
    unfold no_responses.
    intros.
    chan2msg.
    repeat find_rewrite.
    in_crush; eauto.
    repeat handler_def || handler_simpl;
      find_apply_lem_hyp option_map_Some; expand_def;
        inv_prop response_payload.
  }
  destruct (list_eq_dec send_eq_dec ms []).
  - assert (msgs gst = msgs gst').
    {
      repeat find_rewrite.
      reflexivity.
    }
    assert (Hcr: forall h st st',
               sigma gst h = Some st ->
               sigma gst' h = Some st' ->
               cur_request st = cur_request st').
    {
      intros.
      find_rewrite.
      update_destruct; rewrite_update;
        try intuition congruence.
      find_injection.
      repeat handler_def; simpl in *;
        intuition congruence.
    }
    destruct (sigma gst' dst) eqn:?; subst.
    + simpl.
      assert (exists st, sigma gst dst = Some st).
      {
        rewrite H9 in Heqo0.
        update_destruct; rewrite_update; subst;
          eexists; eauto.
      }
      break_exists.
      erewrite <- Hdq by eauto.
      erewrite <- (Hcr src oldst__src) by eauto.
      erewrite <- !(msgs_eq_channels_eq gst gst') by eauto.
      replace (nodes gst') with (nodes gst); eauto.
      replace (failed_nodes gst') with (failed_nodes gst); eauto.
      replace (Some (delayed_queries x)) with (option_map delayed_queries (sigma gst dst)); eauto.
      replace (sigma gst dst) with (Some x).
      reflexivity.
    + match goal with
      | H: _, Hdst: sigma gst' dst = None |- _ => rewrite H in Hdst
      end.
      update_destruct; subst; rewrite_update; try congruence.
      erewrite channel_msgs_unchanged with (dst := src); eauto.
      find_copy_apply_lem_hyp state_none_not_in_nodes; eauto.
      inv_prop query_message_ok';
        repeat inv_option_map;
        try congruence.
      * replace (nodes gst') with (nodes gst) by auto.
        replace (failed_nodes gst') with (failed_nodes gst) by auto.
        assert (Hnomsgs: channel gst' src dst = []).
        {
          assert (~ client_addr src) by eauto.
          destruct (channel gst' src dst) eqn:?; [reflexivity|exfalso].
          assert (In p (channel gst' src dst)) by (rewrite Heql; in_crush).
          assert (~ In dst (nodes gst')) by congruence.
          find_eapply_prop dst.
          eapply non_client_msgs_only_to_live_nodes;
            solve [econstructor; eauto | eauto].
        }
        rewrite Hnomsgs.
        erewrite Hcr in * by eauto.
        constructor; eauto.
      * replace (nodes gst') with (nodes gst) by auto.
        replace (failed_nodes gst') with (failed_nodes gst) by auto.
        constructor; eauto.
        replace (channel gst' src dst) with (channel gst src dst) in *
          by (unfold channel; congruence).
        eauto.
  - repeat handler_def || handler_simpl.
    find_apply_lem_hyp option_map_Some; expand_def.
    destruct (addr_eq_dec src h).
    + subst; repeat find_rewrite || find_injection || rewrite_update.
      simpl.
      destruct (addr_eq_dec (addr_of x1) dst); subst.
      * update_destruct; subst; rewrite_update.
        -- repeat find_rewrite || find_injection || rewrite_update.
           simpl in *.
           constructor; eauto.
           inv_prop query_message_ok'; eauto; try intuition.
           inv_prop query_message_ok.
           eapply CIreq; eauto.
           ++ chan2msg; find_rewrite; in_crush.
           ++ eapply unique_no_requests.
              erewrite channel_msgs_cons; eauto.
              apply unique_cons_add; eauto.
        -- assert (exists st, sigma gst (addr_of x1) = Some st).
           {
             pose proof (pointers_joined gst ltac:(eauto)); eauto.
             inv_prop all_joined_ptrs.
             unfold all_preds_state in *.
             eapply_prop_hyp all_states pred; eauto.
             unfold pointer_joined in *; intuition.
           }
           expand_def; repeat find_rewrite.
           change (send h (addr_of x1, Ping) :: msgs gst)
             with (map (send h) [(addr_of x1, Ping)] ++ msgs gst) in *.
           inv_prop query_message_ok'; eauto.
           ++ eapply QMLive; eauto.
              inv_prop query_message_ok.
              eapply CIreq; auto.
              ** chan2msg; find_rewrite; in_crush.
              ** eapply unique_no_requests.
                 simpl in *.
                 erewrite channel_msgs_cons; eauto.
                 apply unique_cons_add; eauto.
           ++ eapply QMFailedNothing; eauto.
              intros; find_injection.
              constructor.
      * inv_prop query_message_ok'; repeat inv_option_map.
        -- update_destruct; rewrite_update.
           ++ apply QMLive; eauto.
              inv_prop query_message_ok.
              apply CIother; eauto.
              erewrite channel_msgs_unchanged with (h := dst); eauto.
              instantiate (1:=[(addr_of x1, Ping)]); simpl; eauto.
              right.
              intros.
              in_crush; congruence.
              intuition.
              repeat find_rewrite || find_injection.
              eauto.
           ++ repeat find_rewrite.
              apply QMLive; eauto.
              inv_prop query_message_ok.
              apply CIother; eauto.
              erewrite channel_msgs_unchanged with (h := h); eauto.
              instantiate (1:=[(addr_of x1, Ping)]); simpl; eauto.
              right.
              intros.
              in_crush; congruence.
        -- repeat find_rewrite || rewrite_update.
           apply QMFailedNothing; eauto.
           intros; find_injection; eauto.
        -- repeat find_rewrite || rewrite_update.
           change (send h (addr_of x1, Ping) :: msgs gst)
             with (map (send h) [(addr_of x1, Ping)] ++ msgs gst) in *.
           erewrite channel_msgs_unchanged with (dst:=h); eauto.
           erewrite channel_msgs_unchanged with (dst:=dst); eauto.
           replace (channel gst dst h) with (@nil payload) by congruence.
           replace (channel gst h dst) with (@nil payload) by congruence.
           apply QMNotStarted; eauto.
           intros; find_injection; eauto.
           right; intros; in_crush; congruence.
        -- repeat find_rewrite || rewrite_update.
           change (send h (addr_of x1, Ping) :: msgs gst)
             with (map (send h) [(addr_of x1, Ping)] ++ msgs gst) in *.
           erewrite channel_msgs_unchanged with (dst:=h); eauto.
           erewrite channel_msgs_unchanged with (dst:=dst); eauto.
           apply QMClient; eauto.
           right; intros; in_crush; congruence.
    + change (send h ?m :: ?l)
        with (map (send h) [m] ++ l) in *.
      assert (forall m,
                 unique response_payload (channel gst dst src) m ->
                 unique response_payload (channel gst' dst src) m).
      {
        intros.
        destruct (addr_eq_dec (addr_of x1) src).
        destruct (addr_eq_dec h dst).
        subst.
        simpl in *.
        erewrite channel_msgs_cons; eauto.
        apply unique_cons; eauto.
        erewrite channel_msgs_unchanged; eauto.
        erewrite channel_msgs_unchanged; eauto.
        right.
        simpl; intros.
        in_crush.
        congruence.
      }
      erewrite channel_msgs_unchanged; eauto.
      inv_prop query_message_ok'.
      * assert (exists st, sigma gst' dst = Some st).
        {
          eapply nodes_have_state;
            solve [congruence | econstructor; eauto].
        }
        expand_def.
        unfold option_map in *.
        repeat find_rewrite.
        break_match; try congruence.
        apply QMLive; try congruence.
        inv_prop query_message_ok;
          repeat find_rewrite || find_injection || subst || rewrite_update;
          match goal with H: _ = _ |- _ => rewrite <- H end.
        -- econstructor; eauto.
           erewrite <- Hdq; eauto.
        -- econstructor; eauto.
           erewrite <- Hdq; eauto.
        -- solve [econstructor; eauto;
                  try erewrite <- Hdq; eauto].
        -- eapply CIres; eauto using no_responses_unique, unique_no_responses.
           chan2msg.
           repeat find_rewrite; in_crush; auto.
           erewrite <- Hdq; eauto.
        -- econstructor 5; eauto;
             erewrite <- Hdq; eauto.
      * assert (exists st, sigma gst' (addr_of dstp) = Some st).
        {
          eapply nodes_have_state;
            solve [repeat find_rewrite; auto | econstructor; eauto].
        }
        expand_def.
        unfold option_map in *; break_match_hyp; try congruence.
        repeat find_rewrite.
        find_injection.
        erewrite (channel_msgs_unchanged [(addr_of x1, Ping)] gst' gst);
          intuition eauto.
        erewrite <- Hdq by eauto.
        repeat find_rewrite || rewrite_update.
        congruence.
        left; intro; subst; tauto.
      * assert (exists st, sigma gst' dst = Some st).
        {
          eapply nodes_have_state;
            solve [repeat find_rewrite; auto | econstructor; eauto].
        }
        expand_def.
        unfold option_map in *; break_match_hyp; try congruence.
        repeat find_rewrite.
        find_injection.
        erewrite (channel_msgs_unchanged [(addr_of x1, Ping)] gst' gst);
          intuition eauto.
        erewrite <- Hdq by eauto.
        repeat find_rewrite || rewrite_update.
        congruence.
        left; intro; subst; tauto.
      * inv_option_map.
        inv_prop query_message_ok'; try congruence || tauto.
        inv_option_map.
        erewrite channel_msgs_unchanged with (dst := src); eauto.
        repeat find_reverse_rewrite.
        replace (sigma gst' dst) with (@None data).
        eapply QMNotStarted; congruence || eauto.
        -- intros; find_eapply_prop cur_request.
           now repeat find_rewrite || rewrite_update || find_injection.
        -- repeat find_rewrite.
           rewrite_update.
           symmetry; auto.
      * inv_option_map.
        erewrite channel_msgs_unchanged with (dst := src); eauto.
        repeat find_rewrite.
        rewrite_update.
        repeat find_rewrite; simpl.
        eapply QMClient; eauto.
Qed.

Lemma cur_request_not_none_state_preserved_by_tick:
  forall h st,
    chord_tick_pre_post
      (fun g =>
         sigma g h = Some st /\
         cur_request st <> None)
      (fun g =>
         sigma g h = Some st).
Proof.
  unfold chord_tick_invariant, chord_tick_pre_post; intros.
  repeat find_rewrite; update_destruct; subst; break_and.
  - repeat handler_def || handler_simpl || inv_option_map.
  - repeat find_rewrite; rewrite_update; eauto.
Qed.

Lemma delayed_queries_preserved_by_tick:
  forall h dqs,
    chord_tick_pre_post
      (fun g =>
         forall st,
           sigma g h = Some st ->
           delayed_queries st = dqs)
      (fun g =>
         forall st',
           sigma g h = Some st' ->
           delayed_queries st' = dqs).
Proof.
  unfold chord_tick_invariant, chord_tick_pre_post; intros.
  repeat find_rewrite; update_destruct; subst; break_and.
  - repeat find_rewrite; rewrite_update.
    repeat handler_def || handler_simpl.
  - repeat find_rewrite; rewrite_update; eauto.
Qed.

Lemma cur_request_not_none_channels_preserved_by_tick:
  forall gst gst' h st st' ms nts cts eff,
    reachable_st gst ->
    step_dynamic gst gst' ->
    In Tick (timeouts gst h) ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    tick_handler h st = (st', ms, nts, cts, eff) ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' = update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (remove timeout_eq_dec Tick (timeouts gst h))) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = map (send h) ms ++ msgs gst -> trace gst' = trace gst ++ [e_timeout h Tick] ->
    cur_request st <> None ->
    forall src dst,
    channel gst src dst = channel gst' src dst.
Proof.
  intros.
  repeat find_rewrite; subst; break_and.
  unfold channel in *.
  repeat find_rewrite.
  replace ms with (@nil (addr * payload)); auto.
  repeat handler_def || handler_simpl || inv_option_map.
Qed.


Lemma tick_handler_respects_query_request :
  forall h st st' ms nts cts eff,
    tick_handler h st = (st', ms, nts, cts, eff) ->
    (forall dstp q m,
        cur_request st = Some (dstp, q, m) ->
        query_request q m) ->
    forall dstp' q' m',
      cur_request st' = Some (dstp', q', m') ->
      query_request q' m'.
Proof.
  intros.
  repeat handler_def; eauto.
  simpl in *; find_injection.
  inv_option_map; auto.
  simpl in *; congruence.
Qed.

Lemma tick_only_sends_requests :
  forall gst gst' h st st' ms nts cts eff,
    tick_handler h st = (st', ms, nts, cts, eff) ->
    msgs gst' = map (send h) ms ++ msgs gst ->
    forall src dst,
      channel gst' src dst = channel gst src dst \/
      channel gst' src dst = GetPredAndSuccs :: channel gst src dst.
Proof.
  intros.
  pose proof (channel_msgs_unchanged ms gst' gst src dst h ltac:(eauto)).
  repeat handler_def || handler_simpl; inv_option_map.
  destruct (addr_eq_dec src h), (addr_eq_dec dst (addr_of x)); subst; eauto.
  - right.
    erewrite channel_msgs_cons; eauto.
  - left.
    match goal with
    | H: context[send ?h ?m :: ?l] |- _ =>
      replace (send h m :: l) with (map (send h) [m] ++ l) in H
    end.
    erewrite channel_msgs_unchanged; eauto.
    right; intros; in_crush.
    congruence.
    now simpl.
Qed.

Ltac split_tick_channel src dst :=
  match goal with
  | H: step_dynamic ?gst ?gst' |- _ =>
    assert (channel gst' src dst = channel gst src dst \/
            channel gst' src dst = GetPredAndSuccs :: channel gst src dst);
      [eapply tick_only_sends_requests; eauto|]
  end.

Theorem query_message_ok'_tick_invariant :
 chord_tick_invariant
   (fun g : global_state =>
    forall src dst st__src,
    sigma g src = Some st__src ->
    query_message_ok' src dst (cur_request st__src)
      (option_map delayed_queries (sigma g dst)) (nodes g) (failed_nodes g) (channel g src dst)
      (channel g dst src)).
Proof.
  repeat autounfold; intros.
  destruct (sigma gst src) eqn:?;
    [|repeat find_rewrite || rewrite_update; congruence].
  assert (cur_request st <> None -> st' = st).
  {
    intros.
    cut (Some st' = Some st); [congruence|].
    replace (Some st') with (sigma gst' h); [|repeat find_rewrite; rewrite_update; auto].
    eapply cur_request_not_none_state_preserved_by_tick; eauto.
  }
  assert (query_message_ok' src dst (cur_request d) (option_map delayed_queries (sigma gst dst)) (nodes gst) (failed_nodes gst)
                            (channel gst src dst) (channel gst dst src))
    by eauto.
  assert (Hdqs: option_map delayed_queries (sigma gst' dst) = option_map delayed_queries (sigma gst dst)).
  {
    destruct (sigma gst dst) eqn:?, (sigma gst' dst) eqn:?; simpl.
    - f_equal.
      eapply delayed_queries_preserved_by_tick; eauto; intros; congruence.
    - repeat find_rewrite || rewrite_update || update_destruct; congruence.
    - repeat find_rewrite || rewrite_update || update_destruct; congruence.
    - auto.
  }
  rewrite Hdqs.
  inv_prop query_message_ok'; inv_option_map.
  - repeat find_rewrite || find_injection.
    eapply QMLive; eauto.
    destruct (addr_eq_dec src h); subst; rewrite_update.
    + repeat find_injection || find_rewrite || inv_option_map || rewrite_update || simpl in *.
      destruct (cur_request d) eqn:?.
      * assert (st__src = d) by (find_eapply_prop st__src; congruence).
        subst.
        repeat find_reverse_rewrite.
        assert (ms = []).
        {
          repeat handler_def; congruence.
        }
        subst.
        erewrite channel_msgs_unchanged with (dst:=dst); eauto.
        erewrite channel_msgs_unchanged with (dst:=h); eauto.
      * split_tick_channel dst h.
        inv_prop query_message_ok.
        repeat (match goal with
                | H: context[tick_handler ?h ?st] |- _ =>
                  eapply tick_handler_definition in H; repeat destruct H || break_and
                | H:start_query _ _ _ = _ |- _ => apply start_query_definition in H; destruct H
                | H:context [ start_query ?h ?st ?q ]
                  |- _ => destruct (start_query h st q) as [[[? ?] ?] ?] eqn:?
                | H: add_tick _ = _ |- _ => apply add_tick_definition in H; destruct H
                end; repeat break_exists || break_and) || simpl in *;
          inv_option_map; simpl in *;
          try solve [unfold channel in *; repeat find_rewrite; eauto
                    |congruence].
        -- destruct (addr_eq_dec (addr_of x1) dst); subst.
           ++ repeat find_rewrite.
              erewrite channel_msgs_cons; eauto.
              eapply CIreq; try solve [in_crush].
              eapply unique_no_requests, unique_cons_add; eauto.
           ++ repeat find_rewrite.
              match goal with
              | H: context[?l' = send ?h ?p :: ?l] |- _ =>
                change (send h p :: l) with (map (send h) [p] ++ l) in H
              end.
              erewrite channel_msgs_unchanged; eauto.
              eapply CIother; eauto.
              right; intros; in_crush; congruence.
        -- destruct (addr_eq_dec (addr_of x1) dst); subst.
           ++ repeat find_rewrite.
              erewrite channel_msgs_cons; eauto.
              eapply CIreq; try solve [in_crush].
              eapply unique_no_requests, unique_cons_add; eauto.
              eapply no_responses_cons; eauto.
           ++ repeat find_rewrite.
              match goal with
              | H: context[?l' = send ?h ?p :: ?l] |- _ =>
                change (send h p :: l) with (map (send h) [p] ++ l) in H
              end.
              erewrite channel_msgs_unchanged; eauto.
              eapply CIother; eauto.
              eapply no_responses_cons; eauto.
              right; intros; in_crush; congruence.
        -- subst; simpl.
           simpl in *.
           erewrite !(msgs_eq_channels_eq gst' gst) by eauto.
           eapply CInone; eauto.
    + repeat find_rewrite || find_injection.
      erewrite channel_msgs_unchanged; eauto.
      split_tick_channel dst src.
      break_or_hyp; find_rewrite; eauto.
      simpl in *.
      inv_prop query_message_ok;
        [econstructor 1
        |econstructor 2
        |econstructor 3
        |econstructor 4
        |econstructor 5]; eauto using no_responses_cons.
      in_crush.
      eapply unique_no_responses.
      eapply unique_cons; eauto using no_responses_unique.
  - assert (h <> addr_of dstp)
      by (intro; subst; tauto).
    destruct (addr_eq_dec h src).
    + replace (cur_request st__src) with (Some (dstp, q, req)).
      destruct (sigma gst' (addr_of dstp)) eqn:?;
               [|repeat find_rewrite; update_destruct || rewrite_update;
                 update_destruct; rewrite_update; congruence].
      replace (channel gst' (addr_of dstp) src) with (channel gst (addr_of dstp) src)
        by eauto using cur_request_not_none_channels_preserved_by_tick.
      replace (channel gst' src (addr_of dstp)) with (channel gst src (addr_of dstp))
        by eauto using cur_request_not_none_channels_preserved_by_tick.
      replace (nodes gst') with (nodes gst).
      replace (failed_nodes gst') with (failed_nodes gst).
      eapply QMFailedRes; eauto.
      replace st__src with d; eauto.
      repeat find_rewrite || find_injection || rewrite_update.
      symmetry; eauto.
    + repeat find_rewrite || find_injection || rewrite_update.
      replace (cur_request d) with (Some (dstp, q, req)).
      erewrite channel_msgs_unchanged with (src := src); eauto.
      erewrite channel_msgs_unchanged with (src := (addr_of dstp)); eauto.
      eapply QMFailedRes; eauto.
  - eapply QMFailedNothing; congruence || eauto.
    + unfold no_responses; intros.
      chan2msg; repeat find_rewrite; in_crush.
      * unfold send in *; find_injection.
        repeat handler_def || handler_simpl.
      * eapply_prop no_responses; chan2msg; eauto.
    + intros.
      repeat find_rewrite || find_injection || rewrite_update || update_destruct; subst; eauto.
      handler_def; eauto.
      repeat handler_def; simpl in *; inv_option_map;
        repeat find_rewrite || find_injection.
      eauto.
      congruence.
  - assert (forall m, ~ In (dst, m) ms).
    {
      intros.
      repeat handler_def; auto.
      simpl in *.
      inv_option_map.
      intuition; find_injection.
      find_eapply_prop nodes.
      find_eapply_lem_hyp hd_error_in; eauto.
      find_eapply_lem_hyp successors_in_nodes; eauto.
    }
    replace (channel gst' src dst) with (@nil payload).
    replace (channel gst' dst src) with (@nil payload).
    eapply QMNotStarted; try congruence.
    + intros.
      destruct (addr_eq_dec h src);
        repeat find_rewrite || find_injection || rewrite_update || simpl in *; eauto.
      split.
      eapply tick_handler_respects_query_request; eauto; firstorder.
      intro; subst.
      find_eapply_prop nodes.
      replace (nodes gst) with (nodes gst').
      eapply cur_request_targets_in_nodes.
      econstructor 2; eauto.
      repeat find_rewrite.
      rewrite update_same; eauto.
      eauto.
    + symmetry.
      eapply no_elements_nil.
      intuition; chan2msg.
      repeat find_rewrite; in_crush.
      unfold send in *; find_injection.
      eauto.
      eapply in_nil.
      replace [] with (channel gst dst src).
      chan2msg; eauto.
    + symmetry.
      eapply no_elements_nil.
      intuition; chan2msg.
      repeat find_rewrite; in_crush.
      unfold send in *; find_injection.
      eauto.
      eapply in_nil.
      replace [] with (channel gst src dst).
      chan2msg; eauto.
      congruence.
  - eapply QMClient; eauto.
    + intros.
      chan2msg.
      repeat find_rewrite; in_crush.
      unfold send in *; find_injection.
      exfalso; eapply nodes_not_clients; eauto.
    + intros.
      chan2msg.
      repeat find_rewrite; in_crush.
      unfold send in *; find_injection.
      repeat handler_def || handler_simpl.
      inv_option_map.
      exfalso.
      find_eapply_lem_hyp hd_error_in.
      find_eapply_lem_hyp successors_in_nodes; eauto.
      eapply nodes_not_clients; eauto.
Qed.

Theorem dq_res_qmo :
  forall gst gst' src dst req res st__src st__dst st__dst' st__src' l ms,
    query_message_ok' src dst (cur_request st__src)
      (option_map delayed_queries (sigma gst dst)) (nodes gst) (failed_nodes gst) (channel gst src dst)
      (channel gst dst src) ->
    msgs gst' = map (send dst) l ++ ms ->
    In (src, req) (delayed_queries st__dst) ->
    src <> dst ->
    (forall m, In m ms -> In m (msgs gst)) ->
    sigma gst' dst = Some st__dst' ->
    sigma gst dst = Some st__dst ->
    delayed_queries st__dst' = [] ->
    ~ In dst (failed_nodes gst) ->
    ~ In dst (failed_nodes gst') ->
    cur_request st__src = cur_request st__src' ->
    In (src, res) l ->
    (forall xs ys, l = xs ++ (src, res) :: ys ->
              forall z, fst z = src ->
                   response_payload (snd z) ->
                   ~ In z (xs ++ ys)) ->
    request_response_pair req res ->
    query_message_ok src dst (cur_request st__src')
      (delayed_queries st__dst') (channel gst' src dst)
      (channel gst' dst src).
Proof.
  intros.
  inv_prop query_message_ok';
    repeat match goal with
           | H: None = option_map _ _ |- _ =>
             symmetry in H
           | H: Some _ = option_map _ _ |- _ =>
             symmetry in H
           | H: option_map _ _ = None |- _ =>
             apply option_map_None in H
           | H: option_map _ _ = Some _ |- _ =>
             apply option_map_Some in H;
               destruct H; break_and
           | |- _ => tauto
           | |- _ => congruence
           end.
  repeat find_rewrite || find_injection.
  inv_prop query_message_ok;
    match goal with
    | H: forall m, ~ In (src, m) (delayed_queries _) |- _ =>
      exfalso; eapply H; eauto
    | _ => idtac
    end.
  repeat find_reverse_rewrite.
  assert (req = req0).
  {
    cut ((src, req0) = (src, req)); [congruence|].
    eapply uniq_list_eq with (P := fun p => fst p = src); eauto using send_eq_dec.
    intros.
    destruct z; simpl in *; subst.
    eauto.
  }
  subst.
  eapply CIres; eauto.
  - apply in_msgs_in_channel.
    repeat find_rewrite.
    apply in_or_app; left.
    apply in_map_iff.
    exists (src, res0); auto.
  - intros.
    unfold no_responses; intros.
    match goal with
    | H: channel gst' _ _ = _ |- _ => unfold channel in H
    end.
    repeat find_rewrite.
    find_copy_apply_lem_hyp (in_split (src, res0)); expand_def.
    rewrite ?map_app, ?map_cons, ?filterMap_app in *.
    rewrite filterMap_defn in *; break_match; simpl in *;
      repeat match goal with
             | H: context[addr_eq_dec ?x ?x] |- _ =>
               destruct (addr_eq_dec x x); simpl in H; try congruence
             end.
    find_injection.
    autorewrite with list in *.
    match goal with
    | H: (?a ++ p :: ?b) ++ ?more = ?xs ++ p :: ?ys |- _ =>
      rewrite <- app_assoc in H; simpl in H;
        assert (a = xs /\ b ++ more = ys)
    end.
    {
      eapply splits_uniq_eq; eauto.
      intros; intro.
      assert (~ In (src, z) (x0 ++ x1)) by eauto.
      intuition.
      find_false.
      apply in_or_app.
      channel_crush;
        match goal with
        | H: In ?pkt ms,
          H': no_responses ?chan |- _ =>
          exfalso; eapply H'; chan2msg
        end; eauto.
    }
    find_apply_lem_hyp in_app_or.
    intro; channel_crush;
      solve [find_eapply_prop response_payload; eauto with datatypes; eauto
            |find_eapply_prop no_responses; chan2msg; eauto].
  - unfold no_requests; intros.
    find_apply_lem_hyp in_channel_in_msgs.
    repeat find_rewrite.
    find_apply_lem_hyp in_app_or; break_or_hyp.
    + find_apply_lem_hyp in_map_iff; expand_def.
      unfold send in *; congruence.
    + eapply_prop no_requests; eauto.
  - repeat find_rewrite; auto.
Qed.

Lemma recv_handler_response_req_in_dqs_or_input :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    forall host response,
      response_payload response ->
      response <> Busy ->
      In (host, response) ms ->
      exists request,
        request_response_pair request response /\
        (host = src /\
         p = request \/
         In (host, request) (delayed_queries st)).
Proof.
  intros.
  handler_def.
  in_crush.
  - unfold do_delayed_queries in *; break_match; repeat handler_simpl;
      try tauto.
    find_apply_lem_hyp handle_delayed_query_dst_in_dqs.
    expand_def.
    destruct (list_eq_dec send_eq_dec (delayed_queries x) (delayed_queries st)).
    + repeat find_rewrite; eauto.
    + find_eapply_lem_hyp handle_msg_dqs_change_queue; eauto.
      simpl in *; break_if.
      * repeat find_rewrite.
        find_apply_lem_hyp in_dedup_was_in.
        eauto.
      * repeat find_rewrite; simpl in *; break_or_hyp.
        find_injection; eauto.
        find_apply_lem_hyp in_dedup_was_in; eauto.
  - handler_def; simpl in *; try congruence.
    + break_or_hyp; try tauto.
      find_injection.
      eexists; intuition eauto.
      constructor.
    + repeat handler_def || handler_simpl.
    + repeat handler_def || handler_simpl.
    + repeat handler_def || handler_simpl;
        inv_prop response_payload.
    + unfold handle_query_req in *; break_match;
        simpl in *; intuition; find_injection.
      all:eexists; intuition eauto; constructor.
Qed.

Lemma handle_query_timeout_no_responses :
  forall h st dstp q st' ms nts cts,
    handle_query_timeout h st dstp q = (st', ms, nts, cts) ->
    forall dst m,
      In (dst, m) ms ->
      ~ response_payload m.
Proof.
  intros.
  intro.
  repeat handler_def || handler_simpl.
  - find_apply_lem_hyp option_map_Some; expand_def; inv_prop response_payload.
  - inv_prop response_payload.
Qed.

Theorem query_message_ok'_request_invariant_dst_live :
 chord_request_invariant
   (fun g : global_state =>
    forall (src dst : addr) (st__src st__dst : data),
      ~ In dst (failed_nodes g) ->
      sigma g src = Some st__src ->
      sigma g dst = Some st__dst ->
      query_message_ok' src dst (cur_request st__src)
                        (option_map delayed_queries (Some st__dst))
                        (nodes g) (failed_nodes g) (channel g src dst)
                        (channel g dst src)).
Proof.
  repeat autounfold; intros.
  assert (cur_request_timeouts_ok (cur_request st) (timeouts gst h))
    by eauto.
  destruct (addr_eq_dec h src); subst.
  - destruct (sigma gst dst0) eqn:?;
      [|repeat find_rewrite; update_destruct; rewrite_update; congruence].
    replace (failed_nodes gst') with (failed_nodes gst) in H15.
    match goal with
    | H: forall (_ _ : addr), _ |- _ =>
      specialize (H src dst0);
        do 2 insterU H;
        repeat (forward H; eauto; concludes)
    end.
    inv_prop query_message_ok'; try tauto.
    apply QMLive; congruence || auto.
    repeat find_rewrite || find_injection.
    repeat rewrite_update; find_injection.
    update_destruct; repeat rewrite_update.
    simpl.
    inv_prop cur_request_timeouts_ok.
    + exfalso; intuition eauto.
    + assert (Request dst req = Request (addr_of dstp) req0)
        by eauto using at_most_one_request_timeout'_uniqueness.
      repeat find_injection || find_rewrite.
      inv_prop query_message_ok;
        try solve [inv_prop timeout_constraint; tauto].
      destruct (cur_request st__dst) as [[[? ?] ?]|] eqn:?.
      * repeat handler_def || handler_simpl.
        find_eapply_lem_hyp option_map_Some; expand_def.
        destruct (addr_eq_dec (addr_of p) dst0); subst.
        -- eapply CIreq; intros; simpl in *; eauto.
           ++ chan2msg; repeat find_rewrite; in_crush.
           ++ erewrite channel_msgs_cons in * by eauto.
              destruct xs; simpl in *; find_injection; eauto.
              exfalso; eapply_prop no_requests;
                repeat find_rewrite; in_crush.
           ++ erewrite channel_msgs_cons in * by eauto.
              unfold no_responses; intros; simpl in *; break_or_hyp; eauto.
        -- change (send dst0 (addr_of p, GetPredAndSuccs) :: msgs gst)
             with (map (send dst0) [(addr_of p, GetPredAndSuccs)] ++ msgs gst) in *.
           erewrite <- channel_msgs_unchanged in *
             by (simpl; eauto; right; intros; simpl in *; intuition congruence).
           eapply CIother; eauto.
      * handler_def;
          try solve [simpl in *;
                     erewrite !msgs_eq_channels_eq by eauto;
                     eapply CInone; eauto].
        find_copy_apply_lem_hyp cur_request_preserved_by_do_delayed_queries.
        match goal with
        | H: handle_query_timeout _ _ _ _ = (?st, ?ms, _, _),
          H': cur_request _ = _ |- _ =>
          assert (ms = [] \/ exists s, ms = [(s, Notify)])
            by repeat match goal with
                      | H: None = Some _ |- _ => inversion H
                      | H: cur_request (_ _) = _ |- _ => cbv in H
                      | |- _ => handler_def || handler_simpl
                      end
        end.
        unfold do_delayed_queries in *; repeat find_rewrite || find_injection.
        assert (delayed_queries x2 = delayed_queries d)
          by eauto using handle_query_timeout_dqs.
        eapply CInone; eauto.
        -- unfold no_responses; intros.
           find_eapply_lem_hyp channel_msgs_app_in; eauto.
           in_crush;
             try solve [find_eapply_prop no_responses; eauto].
           find_eapply_lem_hyp handle_delayed_query_dst_in_dqs; expand_def;
             repeat find_rewrite; solve [intuition eauto].
           expand_def; simpl in *; intuition; find_injection; inv_prop response_payload.
           find_eapply_lem_hyp handle_delayed_query_dst_in_dqs; expand_def;
             repeat find_rewrite; solve [exfalso; intuition eauto].
        -- unfold no_requests; intros.
           find_eapply_lem_hyp channel_msgs_app_in; eauto.
           in_crush;
             try solve [find_eapply_prop no_requests; eauto];
             try find_eapply_lem_hyp handle_delayed_query_only_sends_responses;
             eauto.
           expand_def; simpl in *; intuition; find_injection; inv_prop request_payload.
    + repeat find_rewrite || find_injection.
      inv_prop timeout_constraint.
      assert (dst <> dst0) by (intro; subst; tauto).
      inv_prop cur_request_timeouts_ok;
        [exfalso; now intuition eauto|].
      repeat find_rewrite.
      inv_prop query_message_ok;
        try solve [inv_prop cur_request_timeouts_ok; try congruence;
                   assert (Request dst req = Request (addr_of dstp0) req1)
                     by eauto using at_most_one_request_timeout'_uniqueness;
                   repeat find_rewrite || find_injection;
                   exfalso; intuition eauto].
      repeat find_reverse_rewrite.
      inv_prop cur_request_timeouts_ok; try congruence.
      assert (Request dst req = Request (addr_of dstp0) req1)
        by eauto using at_most_one_request_timeout'_uniqueness.
      repeat find_rewrite || find_injection.
      repeat handler_def || handler_simpl.
      all:match goal with
      | |- query_message_ok _ _ None _ _ _ => constructor
      | |- _ => idtac
      end;
      repeat match goal with
             | H: ?goal |- ?goal => assumption
             | H: msgs ?gst' = send ?h ?m :: map (send ?h) ?ms ++ msgs ?gst |- _ =>
               change (send h m :: map (send h) ms ++ msgs gst)
                 with ((send h m :: map (send h) ms) ++ msgs gst)
                 in H;
                 rewrite <- map_cons in H
             | H: msgs ?gst' = map (send ?h) ?ms ++ msgs ?gst,
                  H': ?h = ?src -> False
               |- context[channel ?gst' ?src ?dst] =>
               solve [erewrite channel_msgs_unchanged; eauto]
             | |- context[channel ?gst' ?src ?dst] =>
               erewrite channel_app; [|now eauto]
             | |- no_requests (filterMap ?f ?l) =>
               unfold no_requests; intros; find_apply_lem_hyp In_filterMap; expand_def;
                 unfold snd in *; repeat break_match; repeat handler_simpl
             | |- no_requests (_ ++ _) =>
               apply no_requests_app; eauto
             end.
      {
        find_apply_lem_hyp option_map_Some; expand_def.
        find_apply_lem_hyp hd_error_tl_exists; expand_def.
        destruct (addr_eq_dec (addr_of x0) dst0); subst.
        - eapply CIreq; try solve [eauto].
          + erewrite channel_msgs_cons; eauto.
            in_crush.
          + eapply unique_no_requests.
            erewrite channel_msgs_cons; eauto.
            eapply unique_cons_add.
            intros; eauto.
            constructor.
          + erewrite channel_msgs_unchanged.
            eassumption.
            repeat find_rewrite.
            rewrite map_cons.
            simpl.
            f_equal; eauto.
            instantiate (1:=nil); reflexivity.
            left.
            congruence.
        - eapply CIother; eauto.
          + erewrite channel_msgs_unchanged.
            eauto.
            repeat find_rewrite.
            rewrite map_cons; simpl.
            f_equal; eauto.
            instantiate (1:=[]). reflexivity.
            left; congruence.
          + erewrite channel_msgs_unchanged.
            eauto.
            repeat find_rewrite.
            rewrite map_cons; simpl.
            f_equal; eauto.
            instantiate (1:=[]). reflexivity.
            right; simpl; intros.
            break_or_hyp; intuition congruence.
      }
      in_crush.
      * inv_prop request_payload; congruence.
      * find_eapply_lem_hyp handle_delayed_query_only_sends_responses; eauto.
  - repeat find_rewrite.
    destruct (addr_eq_dec h dst0); subst.
    + repeat rewrite_update; repeat find_rewrite || find_injection.
      erewrite (channel_msgs_unchanged ms gst'); eauto.
      invcs_prop cur_request_timeouts_ok;
        [exfalso; intuition eauto|].
      assert (Request dst req = Request (addr_of dstp) req0)
        by eauto using at_most_one_request_timeout'_uniqueness.
      repeat find_rewrite || find_injection.
      match goal with
      | H: forall (_ _ : addr), _ |- _ =>
        specialize (H src dst0);
          do 2 insterU H;
          repeat (forward H; eauto; concludes)
      end.
      inv_prop timeout_constraint.
      assert (no_responses (channel gst dst0 src) ->
              (forall m, ~ In (src, m) (delayed_queries st)) ->
              no_responses (channel gst' dst0 src)).
      {
        unfold no_responses; intros.
        unfold send in *.
        chan2msg.
        repeat find_rewrite.
        in_crush; eauto.
        find_injection.
        handler_def.
        in_crush.
        eapply handle_query_timeout_no_responses; eauto.
        find_apply_lem_hyp handle_query_timeout_dqs.
        handler_def.
        find_apply_lem_hyp handle_delayed_query_dst_in_dqs.
        expand_def.
        repeat find_rewrite.
        eauto.
      }
      assert ((forall m, ~ In (src, m) (delayed_queries st)) ->
              forall m, ~ In (src, m) (delayed_queries st__dst)).
      {
        repeat handler_def; simpl; eauto.
      }
      handler_def; try congruence.
      eapply QMLive; eauto.
      inv_prop query_message_ok'; try tauto.
      inv_prop query_message_ok;
        match goal with
        | |- query_message_ok _ _ None _ _ _ =>
          eapply CInone; auto
        | H: _ <> addr_of ?dst
          |- query_message_ok _ _ (Some (?dst, _, _)) _ _ _ =>
          solve [econstructor; eauto]
        | H: In ?req (channel ?gst ?src (addr_of ?dst)),
             H':query_request _ ?req
          |- query_message_ok _ _ (Some (?dst, _, _)) _ _ _ =>
          eapply CIreq; eauto
        | H: In ?res (channel ?gst (addr_of ?dst) ?src),
             H':request_response_pair _ ?res
          |- query_message_ok _ _ (Some (?dst, _, _)) _ _ _ =>
          eapply CIres; eauto; chan2msg; repeat find_rewrite; eauto with datatypes
        | _ => idtac
        end.
      * find_apply_lem_hyp no_responses_unique; eauto.
        apply unique_no_responses.
        erewrite channel_app; eauto.
        apply unique_app; eauto.
        intros.
        find_apply_lem_hyp In_filterMap; expand_def.
        break_if; try congruence.
        destruct x6.
        in_crush.
        -- repeat find_rewrite || find_injection.
           eapply handle_query_timeout_no_responses; eauto.
        -- find_apply_lem_hyp handle_query_timeout_dqs.
           handler_def;
             find_eapply_lem_hyp handle_delayed_query_dst_in_dqs.
           expand_def.
           repeat find_rewrite || find_injection.
           intuition eauto.
      * erewrite (channel_app gst gst'); eauto.
        find_copy_apply_lem_hyp cur_request_preserved_by_do_delayed_queries.
        find_copy_apply_lem_hyp handle_query_timeout_dqs.
        find_apply_lem_hyp do_delayed_queries_definition; expand_def.
        -- eapply CIdelayed; eauto; try congruence.
           intros.
           repeat find_rewrite; eauto.
           apply no_responses_app.
           autorewrite with list.
           unfold no_responses; intros; find_apply_lem_hyp In_filterMap; expand_def.
           break_match; try congruence.
           destruct x7; simpl in *; find_injection.
           eapply handle_query_timeout_no_responses; eauto.
           eauto.
        -- destruct (handle_delayed_query (addr_of dstp0) x2 (src, req)) eqn:?.
           unfold handle_delayed_query, handle_query_req in * |-; simpl in *.
           inv_prop query_request; try congruence.
           simpl in *; congruence.
           destruct p as [src' p].
           assert (src' = src).
           {
             unfold handle_delayed_query, handle_query_req in *.
             break_match; congruence.
           }
           eapply CIres with (res := p).
           ++ unfold handle_delayed_query, handle_query_req in *.
              break_match; try congruence;
                simpl in *; find_injection;
                  constructor.
           ++ apply in_or_app; left.
              apply filterMap_In with (a:=(src, p)).
              simpl.
              break_match; try congruence.
              in_crush.
              right.
              rewrite <- flat_map_concat_map.
              rewrite in_flat_map.
              eexists; split; eauto.
              repeat find_rewrite. eauto.
              unfold handle_delayed_query; repeat find_rewrite.
              in_crush.
           ++ apply unique_no_responses.
              rewrite !filterMap_app.
              apply unique_app_r; eauto.
              apply unique_app.
              find_copy_apply_lem_hyp in_split; expand_def.
              repeat find_rewrite.
              rewrite ?map_app, ?concat_app, ?filterMap_app.
              apply unique_app.
              simpl.
              rewrite filterMap_app.
              apply unique_app_r.
              unfold handle_delayed_query, handle_query_req in *.
              apply unique_triv;
                repeat break_match || simpl || find_injection;
                solve [omega | congruence | constructor].
              rewrite filterMap_all_None;
              intros; in_crush;
                try solve [exfalso; find_eapply_prop In; in_crush; eauto; left; eauto];
              destruct x8; simpl in *;
              find_copy_eapply_lem_hyp handle_delayed_query_dst_in_dqs; expand_def;
              break_match; try reflexivity; subst;
              exfalso; eapply H36; eauto;
              in_crush; eauto.
              intros; in_crush;
                try solve [exfalso; eapply H36; in_crush; eauto; left; eauto].
              find_apply_lem_hyp In_filterMap; expand_def.
              destruct x8.
              break_match; try congruence; find_injection.
              simpl in *.
              find_copy_eapply_lem_hyp handle_delayed_query_dst_in_dqs; expand_def.
              in_crush; eauto.
              try solve [exfalso; eapply H36; in_crush; eauto; left; eauto].
              intros; in_crush;
                try solve [exfalso; eapply H36; in_crush; eauto; left; eauto].
              find_apply_lem_hyp In_filterMap; expand_def.
              destruct x6; simpl in *.
              eapply handle_query_timeout_no_responses; eauto.
              break_match; try congruence.
           ++ eauto.
           ++ eauto.
           ++ eauto.
    + erewrite (channel_msgs_unchanged ms gst'); eauto.
      erewrite (channel_msgs_unchanged ms gst'); eauto.
      repeat rewrite_update; eauto.
Qed.

Lemma cur_request_in_nodes :
  forall gst,
    reachable_st gst ->
    forall src dst q m st,
      sigma gst src = Some st ->
      cur_request st = Some (dst, q, m) ->
      In (addr_of dst) (nodes gst).
Proof.
Admitted.

Lemma request_timeout_handler_query_request :
  forall src st dst req st' ms nts cts eff,
    request_timeout_handler src st dst req = (st', ms, nts, cts, eff) ->
    forall dstp q m,
      cur_request st' = Some (dstp, q, m) ->
      query_request q m \/ cur_request st' = cur_request st.
Proof.
  intros.
  repeat handler_def || handler_simpl || inv_option_map.
Qed.

Theorem query_message_ok'_request_invariant :
 chord_request_invariant
   (fun g : global_state =>
    forall (src dst : addr) (st__src : data),
    sigma g src = Some st__src ->
    query_message_ok' src dst (cur_request st__src)
      (option_map delayed_queries (sigma g dst)) (nodes g) (failed_nodes g) (channel g src dst)
      (channel g dst src)).
Proof.
  repeat autounfold; intros.
  destruct (sigma gst dst0) eqn:?.
  - destruct (In_dec addr_eq_dec dst0 (failed_nodes gst)).
  + repeat find_rewrite.
    update_destruct; subst; try tauto.
    rewrite_update.
    update_destruct; subst; repeat rewrite_update; repeat find_rewrite || find_injection.
    * assert (query_message_ok' src dst0 (cur_request st) (option_map delayed_queries (sigma gst dst0)) (nodes gst) (failed_nodes gst) (channel gst src dst0) (channel gst dst0 src))
          by eauto.
      inv_prop query_message_ok'; repeat find_rewrite; try tauto.
      -- assert (cur_request_timeouts_ok' (cur_request st) (timeouts gst src))
          by eauto.
        repeat find_reverse_rewrite;  inv_prop cur_request_timeouts_ok'; try congruence.
        assert (Request dst req = Request (addr_of dstp) req0) by eauto.
        find_injection.
        exfalso.
        inv_prop timeout_constraint.
        chan2msg.
        intuition eauto.
      -- inv_prop timeout_constraint.
         repeat find_reverse_rewrite.
         eapply QMFailedNothing; eauto.
         erewrite !(channel_msgs_unchanged _ gst' gst) by eauto.
         eauto.
         intros.
         find_copy_eapply_lem_hyp request_timeout_handler_query_request; eauto.
         break_or_hyp; eauto.
         find_eapply_prop query_request; repeat find_rewrite.
         symmetry; eauto.
      -- inv_option_map; congruence.
      -- inv_option_map; congruence.
    * erewrite !(channel_msgs_unchanged _ gst' gst) by eauto.
      replace (Some d) with (sigma gst dst0) by auto.
      eauto.
  + assert (Hst: exists st, sigma gst' dst0 = Some st).
    {
      repeat find_rewrite.
      update_destruct; repeat rewrite_update; eauto.
    }
    destruct Hst as [st__dst0 Hst].
    rewrite Hst.
    eapply query_message_ok'_request_invariant_dst_live; eauto.
    intros.
    rewrite <- H18.
    eapply H14; eauto.
    congruence.
  - assert (~ In dst0 (nodes gst)).
    {
      intro.
      find_eapply_lem_hyp nodes_have_state; eauto.
      expand_def; congruence.
    }
    repeat find_rewrite.
    update_destruct; rewrite_update; try congruence.
    repeat find_rewrite; simpl.
    update_destruct; subst; rewrite_update.
    + assert (query_message_ok' src dst0 (cur_request st)
          (option_map delayed_queries (sigma gst dst0)) (nodes gst)
          (failed_nodes gst) (channel gst src dst0) (channel gst dst0 src))
        by auto.
      inv_prop query_message_ok'; inv_option_map.
      -- erewrite channel_msgs_unchanged with (src := dst0) by eauto.
         erewrite channel_msgs_unchanged with (src := src); eauto.
         repeat find_reverse_rewrite.
         eapply QMNotStarted; eauto.
         intuition.
         ++ repeat find_rewrite || find_injection; eauto.
            find_copy_eapply_lem_hyp request_timeout_handler_query_request; eauto.
            break_or_hyp; eauto.
            find_eapply_prop query_request; repeat find_rewrite.
            symmetry; eauto.
         ++ subst.
            find_eapply_lem_hyp (cur_request_in_nodes gst'); eauto.
            repeat find_rewrite || find_injection; eauto.
            solve [econstructor; eauto].
            repeat find_rewrite; eauto.
            rewrite update_same; auto.
         ++ right.
            intros.
            find_injection.
            intro; subst.
            assert (~ In dst0 (nodes gst')) by congruence.
            find_eapply_prop client_addr.
            eapply non_client_msgs_out_of_net_go_to_clients with (src := src) (gst := gst');
              try solve [econstructor; eauto | eauto].
            repeat find_rewrite.
            in_crush.
      -- erewrite channel_msgs_unchanged with (src := dst0) by eauto.
         repeat find_reverse_rewrite.
         eapply QMClient; eauto.
         intros.
         erewrite channel_app in * by eauto.
         in_crush; eauto.
         find_apply_lem_hyp In_filterMap.
         expand_def.
         break_match; congruence || find_injection.
         handler_def.
         in_crush.
         ++ repeat handler_def || handler_simpl || inv_option_map.
            ** assert (exists n, In n (succ_list st) /\ client_addr (addr_of n)).
               {
                 exists x1.
                 intuition.
                 repeat find_rewrite.
                 find_apply_lem_hyp hd_error_in.
                 in_crush.
               }
               expand_def; exfalso.
               find_eapply_lem_hyp successors_in_nodes; eauto.
               eapply nodes_not_clients; eauto.
            ** assert (exists n, In n (succ_list st) /\ client_addr (addr_of n)).
               {
                 exists x11.
                 intuition.
                 repeat find_rewrite; in_crush.
               }
               expand_def; exfalso.
               find_eapply_lem_hyp successors_in_nodes; eauto.
               eapply nodes_not_clients; eauto.
         ++ right.
            repeat handler_def || handler_simpl;
            destruct x; simpl in *;
            eapply handle_delayed_query_only_sends_responses; eauto.
    + assert (query_message_ok' src dst0 (cur_request st__src)
          (option_map delayed_queries (sigma gst dst0)) (nodes gst)
          (failed_nodes gst) (channel gst src dst0) (channel gst dst0 src))
        by auto.
      inv_prop query_message_ok'; inv_option_map.
      * erewrite channel_msgs_unchanged with (src := dst0) by eauto.
        erewrite channel_msgs_unchanged with (src := src); eauto.
        repeat find_reverse_rewrite.
        eapply QMNotStarted; eauto.
      * erewrite channel_msgs_unchanged with (src := dst0) by eauto.
        repeat find_reverse_rewrite.
        eapply QMClient; eauto.
        erewrite channel_msgs_unchanged; eauto.
Qed.

Lemma query_message_ok'_unrelated_node :
  forall src dst st__src gst,
    query_message_ok' src dst (cur_request st__src)
      (option_map delayed_queries (sigma gst dst)) (nodes gst) (failed_nodes gst) (channel gst src dst)
      (channel gst dst src) ->
    forall h,
      h <> src ->
      h <> dst ->
      query_message_ok' src dst (cur_request st__src)
        (option_map delayed_queries (sigma gst dst)) (h :: nodes gst) (failed_nodes gst) (channel gst src dst)
        (channel gst dst src).
Proof.
  intros.
  inv_prop query_message_ok'; inv_option_map;
    solve [econstructor; eauto; in_crush].
Qed.

Theorem query_message_ok'_start_invariant :
 chord_start_invariant
   (fun g : global_state =>
    forall (src dst : addr) (st__src : data),
    sigma g src = Some st__src ->
    query_message_ok' src dst (cur_request st__src)
      (option_map delayed_queries (sigma g dst)) (nodes g) (failed_nodes g) (channel g src dst)
      (channel g dst src)).
Proof.
  repeat autounfold; intros.
  assert (forall st, sigma gst h = Some st -> False) by eauto.
  assert (Hdq: forall h st st',
             sigma gst h = Some st ->
             sigma gst' h = Some st' ->
             delayed_queries st = delayed_queries st').
  {
    intros.
    find_rewrite.
    update_destruct; rewrite_update; try congruence.
  }
  assert (forall src dst,
             no_responses (channel gst dst src) ->
             no_responses (channel gst' dst src)).
  {
    unfold no_responses.
    intros.
    chan2msg.
    repeat find_rewrite.
    in_crush; eauto.
    unfold send in *.
    find_injection.
    repeat handler_def || handler_simpl;
      find_apply_lem_hyp option_map_Some; expand_def;
        inv_prop response_payload.
  }
  assert (forall src m, ~ client_addr src -> ~ In m (channel gst src h)).
  {
    intros.
    intro; chan2msg.
    find_eapply_lem_hyp non_client_msgs_out_of_net_go_to_clients; auto.
  }
  assert (forall dst m, ~ In m (channel gst h dst)).
  {
    intuition.
    chan2msg.
    destruct (client_payload_dec m).
    - find_eapply_lem_hyp sent_client_message_means_client_or_in_nodes; eauto.
      tauto.
    - find_apply_lem_hyp sent_non_client_message_means_in_nodes; eauto.
  }
  assert (forall dst, channel gst h dst = []).
  {
    intros.
    destruct (channel gst h dst0) eqn:?; auto.
    exfalso.
    eapply H18.
    erewrite Heql.
    simpl; auto.
  }
  assert (forall src, ~ client_addr src -> channel gst src h = []).
  {
    intros.
    destruct (channel gst src0 h) eqn:?; auto.
    exfalso.
    eapply H17; eauto.
    erewrite Heql.
    simpl; auto.
  }
  rewrite start_handler_with_single_known in *.
  simpl in *; find_injection.
  assert (h <> k) by (intro; subst; tauto).
  destruct (sigma gst' k) eqn:Hstk.
  - destruct (addr_eq_dec src h), (addr_eq_dec dst k); subst.
    + erewrite channel_msgs_cons; [|simpl in *; eauto].
      erewrite channel_msgs_unchanged with (gst':=gst'); eauto.
      rewrite Hstk.
      eapply QMLive; try congruence.
      repeat find_rewrite; in_crush.
      repeat find_rewrite || rewrite_update || find_injection.
      simpl; change k with (addr_of (make_pointer k)).
      eapply CIreq; eauto.
      * in_crush.
      * eapply unique_no_requests.
        eapply unique_cons_add; [|constructor].
        intros.
        intuition eauto.
      * unfold no_responses; intros.
        assert (~ client_addr k) by eauto.
        intuition eauto.
      * intuition.
        find_eapply_lem_hyp delayed_query_sources_active_or_clients; intuition eauto.
    + repeat find_rewrite || find_injection || rewrite_update || simpl || update_destruct.
      * erewrite channel_app; eauto.
        replace (channel gst dst dst) with (@nil payload) by auto.
        autorewrite with list; simpl.
        destruct (addr_eq_dec k dst); try congruence.
        eapply QMLive; try solve [in_crush
                                 |intuition; find_eapply_prop nodes; eauto using in_failed_in_nodes].
        eapply CIother; eauto.
      * erewrite channel_msgs_unchanged with (dst:=h); eauto.
        erewrite channel_app; eauto.
        replace (channel gst h dst) with (@nil payload) by auto.
        autorewrite with list; simpl.
        destruct (addr_eq_dec k dst); try congruence.
        destruct (In_dec addr_eq_dec dst (failed_nodes gst));
          [|destruct (sigma gst dst) eqn:?].
        -- find_copy_apply_lem_hyp in_failed_in_nodes; auto.
           find_copy_apply_lem_hyp nodes_have_state; auto; expand_def.
           assert (~ client_addr dst) by eauto.
           replace (channel gst dst h) with (@nil payload) by (symmetry; eauto).
           find_rewrite; simpl.
           eapply QMFailedNothing; in_crush.
           find_injection; auto.
        -- repeat find_rewrite; simpl.
           assert (~ client_addr dst) by eauto.
           replace (channel gst dst h) with (@nil payload) by (symmetry; eauto).
           eapply QMLive; in_crush; eauto using only_nodes_have_state.
           eapply CIother; in_crush.
           find_eapply_lem_hyp delayed_query_sources_active_or_clients; intuition eauto.
        -- repeat find_rewrite; simpl.
           destruct (client_addr_dec dst).
           ++ eapply QMClient; eauto; in_crush.
              destruct (client_payload_dec p); auto.
              find_eapply_lem_hyp sent_non_client_message_means_in_nodes; eauto.
              exfalso; eapply nodes_not_clients; eauto.
           ++ replace (channel gst dst h) with (@nil payload) by (symmetry; eauto).
              eapply QMNotStarted; eauto.
              in_crush; find_eapply_lem_hyp nodes_have_state; expand_def; congruence.
              intros; find_injection; eauto.
    + repeat find_rewrite || find_injection || rewrite_update || simpl || update_destruct.
      erewrite channel_msgs_unchanged with (src := src); eauto.
      erewrite channel_msgs_unchanged with (src := k); eauto.
      replace (Some (delayed_queries d)) with (option_map delayed_queries (sigma gst k)).
      eapply query_message_ok'_unrelated_node; eauto.
      repeat find_rewrite; reflexivity.
    + repeat find_rewrite || find_injection || rewrite_update || simpl || update_destruct;
        subst.
      * erewrite channel_msgs_unchanged with (src := src); eauto.
        erewrite channel_app with (gst' := gst'); eauto.
        replace (channel gst dst src) with (@nil payload) by auto.
        assert (~ client_addr src) by eauto.
        replace (channel gst src dst) with (@nil payload) by (symmetry; auto).
        autorewrite with list; simpl.
        destruct (addr_eq_dec k src); subst.
        -- repeat find_rewrite || find_injection.
           eapply QMLive; try solve [in_crush].
           intro; find_eapply_lem_hyp in_failed_in_nodes; eauto.
           destruct (cur_request d) as [[[? ?] ?]|] eqn:?.
           ++ assert (query_message_ok' src (addr_of p) (cur_request d)
                        (option_map delayed_queries (sigma gst (addr_of p))) (nodes gst)
                        (failed_nodes gst) (channel gst src (addr_of p)) (channel gst (addr_of p) src))
               by auto.
              repeat find_rewrite.
              assert (query_request q p0 /\ dst <> addr_of p).
              {
                inv_prop query_message_ok'.
                - split; [|intro; subst; tauto].
                  inv_prop query_message_ok; auto.
                - split; [auto|intro; subst; tauto].
                - inv_option_map.
                  split; [eauto| intro; subst; tauto].
                - assert (addr_of p <> addr_of p).
                  find_eapply_prop addr_of; eauto.
                  congruence.
                - inv_option_map.
                  find_eapply_lem_hyp cur_request_in_nodes; eauto.
                  find_copy_apply_lem_hyp nodes_have_state; eauto; expand_def.
                  split; [|now eauto].
                  inv_prop query_message_ok'; inv_option_map; congruence || eauto.
              }
              eapply CIother;
                try solve [unfold no_responses, no_requests; intros; in_crush;
                           try inv_prop response_payload].
           ++ eapply CInone; eauto.
              unfold no_responses; in_crush; inv_prop response_payload.
        -- assert (query_message_ok' src dst (cur_request st__src)
                                     (option_map delayed_queries (sigma gst dst))
                                     (nodes gst) (failed_nodes gst)
                                     (channel gst src dst) (channel gst dst src))
            by eauto.
           destruct (sigma gst dst) eqn:?;
                    try solve [find_eapply_lem_hyp (only_nodes_have_state gst dst); tauto].
           inv_prop query_message_ok'; inv_option_map; try congruence.
           destruct (cur_request st__src) as [[[dstp q] m]|] eqn:?;
           try assert (query_message_ok' src (addr_of dstp) (cur_request st__src) (option_map delayed_queries (sigma gst (addr_of dstp))) (nodes gst) (failed_nodes gst) (channel gst src (addr_of dstp)) (channel gst (addr_of dstp) src)) by eauto.
           ++ eapply QMLive; try solve [in_crush].
              intro.
              find_eapply_lem_hyp in_failed_in_nodes; tauto.
              eapply CIother; eauto.
              intro; subst.
              find_eapply_lem_hyp cur_request_in_nodes; eauto.
              find_eapply_prop query_request; eauto.
           ++ eapply QMLive; try solve [in_crush].
              intro; find_eapply_lem_hyp in_failed_in_nodes; tauto.
              eapply CInone; eauto.
      * erewrite channel_msgs_unchanged with (src := src); eauto.
        erewrite channel_msgs_unchanged with (src := dst); eauto.
        eapply query_message_ok'_unrelated_node; eauto.
  - find_apply_lem_hyp nodes_have_state; eauto; expand_def.
    repeat find_rewrite || rewrite_update.
    congruence.
Qed.

Theorem query_message_ok'_invariant :
  forall gst,
    reachable_st gst ->
    forall src dst st__src,
      sigma gst src = Some st__src ->
      query_message_ok' src dst (cur_request st__src) (option_map delayed_queries (sigma gst dst))
                       (nodes gst) (failed_nodes gst)
                       (channel gst src dst) (channel gst dst src).
Proof.
  intros gst Hreachable; pattern gst; revert Hreachable; revert gst.
  eapply chord_net_invariant.
  - autounfold; intros.
    destruct (sigma gst dst) eqn:?.
    + apply QMLive; auto.
      eapply only_nodes_have_state;
        solve [eauto | constructor; eauto].
      repeat rewrite initial_st_channels_empty by auto.
      erewrite initial_st_cur_request_None by eauto.
      erewrite initial_st_delayed_queries_empty by eauto.
      eapply CInone; unfold no_requests, no_responses; eauto.
    + rewrite !initial_st_channels_empty by auto.
      destruct (client_addr_dec dst).
      * eapply QMClient; in_crush.
      * eapply QMNotStarted; eauto.
        -- intro.
           find_apply_lem_hyp nodes_have_state;
             solve [expand_def; congruence
                   |constructor; auto].
        -- assert (In src (nodes gst)).
           {
             eapply only_nodes_have_state; eauto.
             constructor; eauto.
           }
           inv_prop initial_st; expand_def.
           destruct (start_handler src (nodes gst)) as [[? ?] ?] eqn:?.
           pose proof succ_list_len_lower_bound.
           copy_eapply H9 Heqp; auto; expand_def.
           rewrite start_handler_init_state_preset in *; try omega.
           repeat find_rewrite || find_injection || simpl in *.
           intros; split; eauto.
           congruence.
  - eapply query_message_ok'_start_invariant.
  - repeat (autounfold; intros).
    repeat find_rewrite.
    match goal with
      H: _ |- _ => specialize (H src dst st__src)
    end.
    repeat concludes.
    assert (no_responses (channel gst dst src) ->
            no_responses (channel gst' dst src)).
    {
      unfold no_responses; intros.
      find_eapply_lem_hyp in_channel_in_msgs.
      repeat find_rewrite.
      eauto using in_msgs_in_channel.
    }
    destruct (addr_eq_dec dst h).
    + inv_prop query_message_ok'; try tauto.
      * inv_prop query_message_ok.
        -- eapply QMFailedNothing; simpl; congruence || eauto.
        -- eapply QMFailedNothing; simpl; congruence || eauto.
        -- eapply QMFailedNothing; simpl; congruence || eauto.
        -- eapply QMFailedRes; simpl;
             try erewrite msgs_eq_channels_eq; eauto.
        -- eapply QMFailedNothing; simpl; congruence || eauto.
      * exfalso.
        eapply nodes_not_clients; eauto.
    + repeat erewrite (msgs_eq_channels_eq gst' gst) by eauto.
      inv_prop query_message_ok';
        solve [constructor; simpl; intuition
              |econstructor; eauto with datatypes].
  - eapply query_message_ok'_tick_invariant.
  - eapply query_message_ok'_keepalive_invariant.
  - eapply query_message_ok'_rectify_invariant.
  - eapply query_message_ok'_request_invariant.
  - eapply query_message_ok'_recv_invariant.
  - repeat autounfold; intros.
    assert (In src (nodes gst')).
    {
      eapply only_nodes_have_state; eauto.
      solve [econstructor; eauto].
    }
    assert (h <> src).
    {
      intro; eapply nodes_not_clients; subst; eauto.
    }
    destruct m as [? [? ?]]; simpl in *.
    assert (msgs gst' = map (send h) [(to, i)] ++ msgs gst).
    {
      subst; simpl; congruence.
    }
    destruct (addr_eq_dec h dst).
    + subst h.
      subst; simpl in *.
      specialize (H5 src dst st__src).
      concludes.
      assert (~ In dst (nodes gst)).
      {
        intro.
        eapply nodes_not_clients; eauto.
      }
      destruct (sigma gst dst) eqn:?.
      exfalso; find_eapply_prop In; eauto using only_nodes_have_state.
      unfold send in *; find_injection.
      destruct (addr_eq_dec src to); subst.
      * eapply QMClient; eauto.
        -- erewrite channel_msgs_cons; simpl; eauto.
           intros.
           break_or_hyp; eauto.
           inv_prop query_message_ok'; eauto.
           repeat find_reverse_rewrite; in_crush.
        -- erewrite channel_msgs_unchanged;
             simpl;
             change ((dst, (to, i)) :: msgs gst)
               with (map (send dst) [(to, i)] ++ msgs gst); eauto.
           inv_prop query_message_ok'; eauto || in_crush.
      * erewrite channel_msgs_unchanged;
          simpl;
          change ((dst, (to, i)) :: msgs gst)
            with (map (send dst) [(to, i)] ++ msgs gst); eauto.
        erewrite channel_msgs_unchanged with (dst := src); simpl;
          change (send dst (to, i) :: msgs gst)
            with (map (send dst) [(to, i)] ++ msgs gst);
          eauto.
        right.
        intros; in_crush; find_injection; eauto.
    + erewrite channel_msgs_unchanged;
        simpl;
        change ((dst, (to, i)) :: msgs gst)
          with (map (send dst) [(to, i)] ++ msgs gst); eauto.
      erewrite channel_msgs_unchanged with (dst := src); simpl;
          change (send dst (to, i) :: msgs gst)
            with (map (send dst) [(to, i)] ++ msgs gst);
          eauto.
      in_crush; find_injection; eauto.
  - repeat autounfold; intros.
    assert (h <> src).
    {
      repeat find_rewrite.
      intro; subst.
      eapply nodes_not_clients; try eassumption.
      eapply only_nodes_have_state; eauto.
    }
    destruct (addr_eq_dec h dst).
    + subst.
      specialize (H5 src (fst (snd m)) st__src); eauto.
      forwards.
      repeat find_rewrite; simpl in *; auto.
      concludes.
      inv_prop query_message_ok'; inv_option_map;
        try solve [exfalso; eapply nodes_not_clients; repeat find_rewrite; eauto
                  |tauto].
      simpl; repeat find_rewrite; simpl.
      eapply QMClient; eauto;
        intros; chan2msg; in_crush;
          try find_eapply_prop client_payload;
          try find_eapply_prop or;
          chan2msg;
            repeat find_rewrite; in_crush.
    + erewrite (channel_msgs_remove_unchanged gst' gst);
        try solve [repeat find_rewrite; simpl; eauto].
      erewrite (channel_msgs_remove_unchanged gst' gst);
        try solve [repeat find_rewrite; simpl; eauto];
        eauto.
Qed.
Hint Resolve query_message_ok'_invariant.

Theorem at_most_one_request_timeout_invariant :
  forall gst h,
    reachable_st gst ->
    at_most_one_request_timeout gst h.
Proof.
  intros.
  find_copy_apply_lem_hyp timeout_means_active_inductive.
  destruct (timeouts gst h) eqn:?.
  - unfold at_most_one_request_timeout, at_most_one_request_timeout'.
    intuition. repeat find_rewrite. destruct xs; simpl in *; congruence.
  - match goal with
    | H : timeout_means_active_invariant _ |- _ =>
      specialize (H h t)
    end.
    forwards; [repeat find_rewrite; in_crush|].
    concludes.
    find_copy_apply_lem_hyp nodes_have_state; eauto.
    break_exists.
    find_eapply_lem_hyp cur_request_timeouts_related_invariant_elim; eauto.
    inv_prop cur_request_timeouts_ok; intuition.
Qed.

Theorem query_message_ok_invariant :
  forall gst,
    reachable_st gst ->
    forall src dst st__src st__dst,
      ~ In dst (failed_nodes gst) ->
      sigma gst src = Some st__src ->
      sigma gst dst = Some st__dst ->
      query_message_ok src dst (cur_request st__src) (delayed_queries st__dst)
                       (channel gst src dst) (channel gst dst src).
Proof.
  intros.
  find_eapply_lem_hyp (query_message_ok'_invariant gst ltac:(auto) src dst);
    eauto.
  inv_prop query_message_ok';
    inv_option_map; congruence.
Qed.
Hint Resolve query_message_ok_invariant.

Lemma uniq_res_eq :
  forall l res res',
    response_payload res ->
    response_payload res' ->
    (forall xs ys,
        l = xs ++ res :: ys -> no_responses (xs ++ ys)) ->
    (forall xs ys,
        l = xs ++ res :: ys -> no_responses (xs ++ ys)) ->
    In res l ->
    In res' l ->
    res = res'.
Proof.
  induction l; intros.
  - simpl in *; tauto.
  - simpl in *; repeat break_or_hyp.
    + auto.
    + find_eapply_lem_hyp in_split; expand_def.
      do 2 find_insterU.
      forwards; eauto with datatypes. concludes.
      simpl in *.
      exfalso; eapply_prop no_responses; eauto with datatypes.
    + find_eapply_lem_hyp in_split; expand_def.
      match goal with
      | H: _ |- _ => specialize (H nil); simpl in H; insterU H
      end.
      concludes.
      exfalso; eapply_prop no_responses; eauto with datatypes.
    + assert (~ response_payload a).
      {
        repeat find_eapply_lem_hyp in_split.
        expand_def.
        find_eapply_prop no_responses.
        repeat find_rewrite.
        change (a :: x ++ res0 :: x0) with ((a :: x) ++ res0 :: x0).
        eauto.
        eauto with datatypes.
      }
      eapply IHl; eauto.
      * intros.
        cut (no_responses ((a :: xs) ++ ys)).
        {
          unfold no_responses; intuition eauto with datatypes.
          find_eapply_prop False; simpl in *; eauto with datatypes.
        }
        find_eapply_prop no_responses.
        simpl; congruence.
      * intros.
        cut (no_responses ((a :: xs) ++ ys)).
        {
          unfold no_responses; intuition eauto with datatypes.
          find_eapply_prop False; simpl in *; eauto with datatypes.
        }
        find_eapply_prop no_responses.
        simpl; congruence.
Qed.
Hint Resolve uniq_res_eq.

Theorem requests_get_correct_response :
  forall gst h st dstp q m r,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dstp, q, m) ->
    In r (channel gst (addr_of dstp) h) ->
    query_response q r ->
    request_response_pair m r.
Proof.
  intros.
  pose proof (query_message_ok'_invariant gst ltac:(auto) h (addr_of dstp)).
  assert (exists st, sigma gst (addr_of dstp) = Some st).
  {
    eapply nodes_have_state; eauto.
    find_apply_lem_hyp in_channel_in_msgs.
    assert (~ client_payload r)
      by (intro; inv_prop client_payload; inv_prop query_response).
    eapply sent_non_client_message_means_in_nodes; eauto.
  }
  break_exists_name st__dst.
  find_insterU.
  forwards; eauto. concludes.
  repeat find_rewrite || find_injection.
  assert (~ no_responses (channel gst (addr_of dstp) h)).
  {
    unfold no_responses; intuition.
    find_eapply_prop False; eauto.
  }
  inv_prop query_message_ok';
    try inv_prop query_message_ok;
    try tauto.
  - assert (res0 = r) by eauto.
    congruence.
  - assert (res0 = r) by eauto.
    congruence.
Qed.
Hint Resolve requests_get_correct_response.
