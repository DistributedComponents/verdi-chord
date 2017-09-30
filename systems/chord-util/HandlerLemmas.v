Require Import List.
Import ListNotations.

Require Import Arith.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.

Require Import mathcomp.ssreflect.ssreflect.
Set Bullet Behavior "Strict Subproofs".

Ltac expand_def :=
  repeat (try break_or_hyp; try break_and; try break_exists);
  subst_max;
  try tuple_inversion;
  try (exfalso; tauto).

Ltac smash_handler :=
  match goal with
  | [H : context[?f ?h] |- _] =>
    match type of (f h) with
    | res => destruct (f h) as [[[?st ?ms] ?newts] ?clearedts] eqn:?H
    | _ => fail
    end
  end.

(* -------------------------------- *)
(* General handler characterization *)
(* -------------------------------- *)

Lemma handle_query_req_busy_definition :
  forall src st msg st' ms newts clearedts,
    handle_query_req_busy src st msg = (st', ms, newts, clearedts) ->
    st' = delay_query st src msg /\
    ms = [(src, Busy)] /\
    clearedts = [] /\
    ((delayed_queries st = [] /\ newts = [KeepaliveTick]) \/
     (delayed_queries st <> [] /\ newts = [])).
Proof using.
  unfold handle_query_req_busy.
  intros.
  repeat break_match; tuple_inversion; tauto.
Qed.

Lemma handle_query_res_definition :
  forall src dst st q p st' ms newts clearedts,
    handle_query_res src dst st q p = (st', ms, newts, clearedts) ->
    (request_payload p /\
     st' = delay_query st src p /\
     clearedts = [] /\
     ms = [] /\
     ((delayed_queries st = [] /\
      newts = [KeepaliveTick]) \/
     (delayed_queries st <> [] /\
      newts = []))) \/
    (p = Busy /\
     st' = st /\
     ms = [] /\
     newts = timeouts_in st /\
     clearedts = timeouts_in st) \/
    (exists n,
        q = Rectify n /\
        p = Pong /\
        ((exists pr,
            pred st = Some pr /\
            end_query (handle_rectify st pr n) = (st', ms, newts, clearedts)) \/
         (pred st = None /\
         end_query (update_pred st n, [], [], []) = (st', ms, newts, clearedts)))) \/
    (q = Stabilize /\
     exists new_succ succs,
       p = GotPredAndSuccs new_succ succs /\
       handle_stabilize dst (make_pointer src) st q new_succ succs = (st', ms, newts, clearedts)) \/
    (exists new_succ,
        q = Stabilize2 new_succ /\
        exists succs,
          p = GotSuccList succs /\
          end_query (update_succ_list st (make_succs new_succ succs),
                     [(addr_of new_succ, Notify)], [], []) = (st', ms, newts, clearedts)) \/
    (exists k,
        q = Join k /\
        ((exists bestpred,
            p = GotBestPredecessor bestpred /\
            clearedts = [Request src (GetBestPredecessor (ptr st))] /\
            ((st' = update_query st bestpred (Join k) GetSuccList /\
              addr_of bestpred = src /\
              ms = [(src, GetSuccList)] /\
              newts = [Request src GetSuccList]) \/
             (st' = update_query st bestpred (Join k) (GetBestPredecessor (ptr st)) /\
              addr_of bestpred <> src /\
              ms = [(addr_of bestpred, (GetBestPredecessor (ptr st')))] /\
              newts = [Request (addr_of bestpred) (GetBestPredecessor (ptr st'))]))) \/
         (p = GotSuccList [] /\
          end_query (st, [], [], []) = (st', ms, newts, clearedts)) \/
         (exists new_succ rest,
             p = GotSuccList (new_succ :: rest) /\
             start_query (addr_of new_succ) st (Join2 new_succ) = (st', ms, newts, clearedts)))) \/
    (exists new_succ succs,
        q = Join2 new_succ /\
        p = GotSuccList succs /\
        add_tick (end_query (update_for_join st (make_succs new_succ succs), [], [], [])) = (st', ms, newts, clearedts)) \/
    st' = st /\ ms = [] /\ newts = [] /\ clearedts = [].
Proof using.
  unfold handle_query_res.
  intros.
  repeat break_match; try tuple_inversion; try tauto.
  - do 2 right. left. eexists; intuition eauto.
  - do 2 right. left. eexists; intuition eauto.
  - intuition eauto.
  - intuition eauto.
  - do 5 right. left.
    eexists; split; eauto.
    left.
    eexists; split; eauto.
    repeat split; auto.
    unfold next_msg_for_join; break_if; subst_max.
    + intuition eauto.
    + intuition eauto.
  - do 5 right. left.
    eexists. intuition eauto.
  - repeat find_rewrite.
    do 5 right. left.
    eexists. intuition eauto.
  - do 6 right. left.
    eexists. intuition eauto.
Qed.

Lemma handle_msg_definition :
  forall src dst st p st' ms newts clearedts,
    handle_msg src dst st p = (st', ms, newts, clearedts) ->

    p = Ping /\
    st' = st /\
    ms = [(src, Pong)] /\
    newts = [] /\
    clearedts = [] \/

    p = Notify /\
    schedule_rectify_with st (make_pointer src) = (st', ms, newts, clearedts) \/

    p <> Notify /\
    p <> Ping /\
    ((exists query_dst query query_msg,
         cur_request st = Some (query_dst, query, query_msg) /\
         (is_request p = true /\
          handle_query_req_busy src st p = (st', ms, newts, clearedts) \/
          is_request p = false /\
          (addr_of query_dst <> src /\ st' = st /\ clearedts = [] /\ newts = [] /\ ms = [] \/
          handle_query_res src dst st query p = (st', ms, newts, clearedts)))) \/

     cur_request st = None /\
     st' = st /\
     clearedts = [] /\
     newts = [] /\
     ms = handle_query_req st src p).
Proof.
  unfold handle_msg.
  intros.
  destruct (payload_eq_dec p Notify), (payload_eq_dec p Ping);
    subst_max; try congruence.
  - tauto.
  - tuple_inversion; tauto.
  - do 2 right.
    repeat split; try auto.
    destruct (cur_request st) as [[[query_dst query] query_msg]|] eqn:H_cur.
    + left; repeat eexists; eauto.
      destruct (is_request p) eqn:?H;
        destruct (addr_eq_dec (addr_of query_dst) src) eqn:?H;
        repeat find_rewrite; simpl in *;
          break_match; simpl in *;
            try congruence; try tuple_inversion; intuition.
    + repeat break_match; try tuple_inversion; tauto.
Qed.

Lemma do_rectify_definition :
  forall h st st' ms' nts' cts' eff,
    do_rectify h st = (st', ms', nts', cts', eff) ->

    (cur_request st = None /\
     joined st = true /\
     (exists new,
         rectify_with st = Some new /\
         (exists x,
             pred st = Some x /\
             eff = StartRectify /\
             start_query h (clear_rectify_with st) (Rectify new) = (st', ms', nts', cts')) \/
         (pred st = None /\
          eff = SetPred /\
          st' = clear_rectify_with (update_pred st new) /\
          ms' = [] /\
          nts' = [] /\
          cts' = []))) \/
    ((joined st = false \/ rectify_with st = None \/ exists r, cur_request st = Some r) /\
     st' = st /\ ms' = [] /\ nts' = [] /\ cts' = [] /\ eff = Ineffective).
Proof using.
  unfold do_rectify.
  intros.
  repeat break_match; try tuple_inversion; try tauto.
  - firstorder eauto.
  - left.
    repeat (eexists; firstorder eauto).
  - left.
    repeat (eexists; firstorder).
Qed.

Lemma start_query_definition :
  forall h st k st' ms nts cts,
    start_query h st k = (st', ms, nts, cts) ->
    (exists dst msg,
        make_request h st k = Some (dst, msg) /\
        st' = update_query st dst k msg /\
        ms = [(addr_of dst, msg)] /\
        nts = [Request (addr_of dst) msg] /\
        cts = timeouts_in st) \/
    (make_request h st k = None /\
     st' = st /\
     ms = [] /\
     ms = [] /\
     nts = [] /\
     cts = []).
Proof using.
  unfold start_query.
  intros.
  repeat break_match; tuple_inversion; try tauto.
  left; repeat eexists.
Qed.

Lemma do_delayed_queries_definition :
  forall h st st' ms nts cts,
    do_delayed_queries h st = (st', ms, nts, cts) ->
    (exists r, cur_request st = Some r /\
               st' = st /\ ms = [] /\ nts = [] /\ cts = []) \/
    (cur_request st = None /\
     st' = clear_delayed_queries st /\
     ms = concat (map (handle_delayed_query h st) (delayed_queries st)) /\
     nts = [] /\
     cts = [KeepaliveTick]).
Proof using.
  unfold do_delayed_queries.
  intros.
  repeat break_match; tuple_inversion;
    [left; eexists|]; tauto.
Qed.

Lemma succ_list_preserved_by_do_delayed_queries :
  forall h st st' ms nts cts,
    do_delayed_queries h st = (st', ms, nts, cts) ->
    succ_list st = succ_list st'.
Proof.
  intros.
  find_apply_lem_hyp do_delayed_queries_definition; expand_def; reflexivity.
Qed.

Lemma pred_preserved_by_do_delayed_queries :
  forall h st st' ms nts cts,
    do_delayed_queries h st = (st', ms, nts, cts) ->
    pred st = pred st'.
Proof.
  intros.
  find_apply_lem_hyp do_delayed_queries_definition; expand_def; reflexivity.
Qed.

Lemma end_query_definition :
  forall st ms newts clearedts st' ms' newts' clearedts',
    end_query (st, ms, newts, clearedts) = (st', ms', newts', clearedts') ->
    st' = clear_query st /\
    ms' = ms /\
    newts' = newts /\
    clearedts' = timeouts_in st ++ clearedts.
Proof using.
  unfold end_query; simpl.
  intros.
  tuple_inversion; tauto.
Qed.

Lemma handle_rectify_definition :
  forall st my_pred notifier st' ms nts cts,
    handle_rectify st my_pred notifier = (st', ms, nts, cts) ->
    ms = [] /\
    nts = [] /\
    cts = [] /\
    (between (id_of my_pred) (id_of notifier) (id_of (ptr st)) /\
     st' = update_pred st notifier \/
     ~ between (id_of my_pred) (id_of notifier) (id_of (ptr st)) /\
     st' = st).
Proof using.
  unfold handle_rectify.
  intros.
  rewrite between_between_bool_equiv.
  rewrite Bool.not_true_iff_false.
  break_match; tuple_inversion; tauto.
Qed.

Lemma recv_handler_definition :
  forall src dst st msg st' ms nts cts st1 ms1 nts1 cts1 st2 ms2 nts2 cts2,
    recv_handler src dst st msg = (st', ms, nts, cts) ->
    handle_msg src dst st msg = (st1, ms1, nts1, cts1) ->
    do_delayed_queries dst st1 = (st2, ms2, nts2, cts2) ->

    st' = st2 /\
    ms = ms2 ++ ms1 /\
    nts = nts2 ++ remove_all timeout_eq_dec cts2 nts1 /\
    cts = cts1 ++ cts2.
Proof using.
  unfold recv_handler.
  intros.
  repeat find_rewrite.
  tuple_inversion; tauto.
Qed.

Lemma recv_handler_definition_existential :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    exists st1 ms1 nts1 cts1 st2 ms2 nts2 cts2,
      handle_msg src dst st p = (st1, ms1, nts1, cts1) /\
      do_delayed_queries dst st1 = (st2, ms2, nts2, cts2) /\

      st' = st2 /\
      ms = ms2 ++ ms1 /\
      nts = nts2 ++ remove_all timeout_eq_dec cts2 nts1 /\
      cts = cts1 ++ cts2.
Proof.
  intros.
  destruct (handle_msg src dst st p) as [[[st1 ms1] nts1] cts1] eqn:H_hm.
  destruct (do_delayed_queries dst st1) as [[[st2 ms2] nts2] cts2] eqn:H_dq.
  find_copy_eapply_lem_hyp recv_handler_definition; eauto; expand_def.
  repeat eexists; intuition eauto.
Qed.

Lemma update_for_start_definition :
  forall gst gst' h st ms newts,
    gst' = update_for_start gst h (st, ms, newts) ->
    nodes gst' = h :: nodes gst /\
    failed_nodes gst' = failed_nodes gst /\
    timeouts gst' = update addr_eq_dec (timeouts gst) h newts /\
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st) /\
    msgs gst' = (map (send h) ms) ++ (msgs gst) /\
    trace gst' = trace gst ++ map e_send (map (send h) ms).
Proof using.
  intros.
  subst.
  repeat split.
Qed.

Lemma add_tick_definition :
  forall st ms nts cts st' ms' nts' cts',
    add_tick (st, ms, nts, cts) = (st', ms', nts', cts') ->

    st' = st /\ ms = ms' /\ cts = cts' /\
    nts' = Tick :: nts.
Proof.
  unfold add_tick.
  intros.
  now tuple_inversion.
Qed.

Lemma tick_handler_definition :
  forall h st st' ms nts cts eff,
    tick_handler h st = (st', ms, nts, cts, eff) ->

    cur_request st = None /\ joined st = true /\
    add_tick (start_query h st Stabilize) = (st', ms, nts, cts) /\
    eff = StartStabilize \/

    ((exists req, cur_request st = Some req) \/
     joined st = false) /\
    st' = st /\ ms = [] /\ nts = [Tick] /\ cts = [] /\ eff = Ineffective.
Proof.
  unfold tick_handler.
  intros.
  repeat break_match; try tuple_inversion;
    intuition (eexists; eauto).
Qed.

Lemma keepalive_handler_definition :
  forall st st' ms nts cts eff,
    keepalive_handler st = (st', ms, nts, cts, eff) ->

    st' = st /\
    ms = send_keepalives st /\
    nts = [KeepaliveTick] /\
    cts = [] /\
    eff = SendKeepalives.
Proof.
  unfold keepalive_handler.
  intros.
  now tuple_inversion.
Qed.

Lemma handle_query_timeout_definition :
  forall h st dst query st' ms nts cts,
    handle_query_timeout h st dst query = (st', ms, nts, cts) ->

    (exists notifier,
        query = Rectify notifier /\
        end_query (update_pred st notifier, [], [], []) = (st', ms, nts, cts)) \/
    (query = Stabilize /\
     exists dead rest,
       succ_list st = dead :: rest /\
       start_query h (update_succ_list st rest) Stabilize = (st', ms, nts, cts)) \/
    (exists s, query = Stabilize2 s /\
          exists next rest,
            succ_list st = next :: rest /\
            end_query (st, [(addr_of next, Notify)], [], []) = (st', ms, nts, cts)) \/
    end_query (st, [], [], []) = (st', ms, nts, cts) /\
    ((exists k, query = Join k) \/
     (exists k, query = Join2 k) \/
     (query = Stabilize /\
      succ_list st = []) \/
     (exists s, query = Stabilize2 s /\
           succ_list st = [])).
Proof.
  unfold handle_query_timeout.
  intros.
  repeat break_match; intuition (eexists; eauto).
Qed.

Lemma request_timeout_handler_definition :
  forall h st dst msg st' ms nts cts eff,
    request_timeout_handler h st dst msg = (st', ms, nts, cts, eff) ->

    (exists dst_ptr query m,
        cur_request st = Some (dst_ptr, query, m) /\
        ((addr_of dst_ptr = dst /\
          eff = DetectFailure /\
          handle_query_timeout h st dst_ptr query = (st', ms, nts, cts)) \/
        (addr_of dst_ptr <> dst /\
         eff = Ineffective /\
         st' = st /\ ms = [] /\ nts = [] /\ cts = []))) \/
    cur_request st = None /\
    eff = Ineffective /\
    st' = st /\ ms = [] /\ nts = [] /\ cts = [].
Proof.
  unfold request_timeout_handler.
  intros; repeat break_match; try tuple_inversion;
    tauto || left; repeat eexists; eauto; tauto.
Qed.

Lemma timeout_handler_eff_definition :
  forall h st t res,
    timeout_handler_eff h st t = res ->
    t = Tick /\
    tick_handler h st = res \/
    t = KeepaliveTick /\
    keepalive_handler st = res \/
    t = RectifyTick /\
    do_rectify h st = res \/
    exists dst msg,
      t = Request dst msg /\
      request_timeout_handler h st dst msg = res.
Proof.
  unfold timeout_handler_eff.
  intros.
  break_match; intuition eauto.
Qed.

Lemma timeout_handler_l_definition :
  forall h st t st' ms nts cts l,
    timeout_handler_l h st t = (st', ms, nts, cts, l) ->

    exists eff,
      timeout_handler_eff h st t = (st', ms, nts, cts, eff) /\
      l = Chord.ChordSystem.Timeout h t eff.
Proof.
  unfold timeout_handler_l.
  intros.
  break_let.
  tuple_inversion.
  eauto.
Qed.

(* -------------------------------- *)
(* Specific handler properties      *)
(* -------------------------------- *)

Lemma busy_response_exists :
  forall msg st' sends nts cts src st,
    request_payload msg ->
    (st', sends, nts, cts) = handle_query_req_busy src st msg ->
    In (src, Busy) sends.
Proof using.
  unfold handle_query_req_busy.
  intuition.
  break_if;
    tuple_inversion;
    now apply in_eq.
Qed.

Lemma delay_query_adds_query :
  forall st src msg st',
    delay_query st src msg = st' ->
    In (src, msg) (delayed_queries st').
Proof.
  intros.
  subst.
  simpl.
  break_if; auto using dedup_In with datatypes.
Qed.

Lemma handle_query_req_busy_delays_query :
  forall src st msg st' ms nts cts,
    handle_query_req_busy src st msg = (st', ms, nts, cts) ->
    In (src, msg) (delayed_queries st').
Proof.
  intros.
  find_apply_lem_hyp handle_query_req_busy_definition; expand_def;
    eauto using delay_query_adds_query.
Qed.

Lemma handle_query_req_busy_sends_busy :
  forall src st msg st' ms nts cts,
    handle_query_req_busy src st msg = (st', ms, nts, cts) ->
    In (src, Busy) ms.
Proof using.
  unfold handle_query_req_busy.
  intuition.
  break_if;
    tuple_inversion;
    exact: in_eq.
Qed.

Lemma handle_query_req_busy_preserves_cur_request :
  forall src st msg st' ms nts cts,
    handle_query_req_busy src st msg = (st', ms, nts, cts) ->
    cur_request st' = cur_request st.
Proof.
  intros.
  find_apply_lem_hyp handle_query_req_busy_definition; expand_def;
    easy.
Qed.

Lemma unsafe_msgs_not_safe_ones :
  forall msg,
    is_safe msg = false ->
    msg <> Notify /\ msg <> Ping.
Proof using.
  unfold is_safe.
  intuition;
    break_match;
    easy.
Qed.

Lemma handle_query_req_gives_response :
  forall st src m,
    is_safe m = false ->
    request_payload m ->
    exists p,
      handle_query_req st src m = [(src, p)].
Proof using.
  unfold handle_query_req.
  intuition.
  find_copy_apply_lem_hyp unsafe_msgs_not_safe_ones; break_and.
  request_payload_inversion;
    eauto || congruence.
Qed.

Lemma do_delayed_queries_busy_nop :
  forall h st st' ms nts cts,
    cur_request st <> None ->
    do_delayed_queries h st = (st', ms, nts, cts) ->
    st' = st /\ ms = [] /\ nts = [] /\ cts = [].
Proof.
  unfold do_delayed_queries.
  intros.
  break_match; repeat split; congruence.
Qed.

Lemma real_requests_get_queued_and_busy_response :
  forall src dst msg st st' sends nts cts,
    request_payload msg ->
    cur_request st <> None ->
    msg <> Ping ->
    recv_handler src dst st msg = (st', sends, nts, cts) ->
    In (src, Busy) sends /\
    In (src, msg) (delayed_queries st').
Proof.
  intros.
  find_apply_lem_hyp recv_handler_definition_existential; expand_def.
  find_apply_lem_hyp handle_msg_definition; expand_def.
  - inv_prop request_payload.
  - split.
    + eauto using handle_query_req_busy_sends_busy with datatypes.
    + find_copy_apply_lem_hyp handle_query_req_busy_preserves_cur_request.
      find_copy_apply_lem_hyp do_delayed_queries_busy_nop; expand_def;
        try congruence.
      eapply handle_query_req_busy_delays_query; eauto.
  - find_apply_lem_hyp is_request_same_as_request_payload; congruence.
  - find_apply_lem_hyp is_request_same_as_request_payload; congruence.
Qed.

Lemma real_requests_get_busy_response :
  forall src dst msg st st' sends nts cts,
    request_payload msg ->
    cur_request st <> None ->
    msg <> Ping ->
    recv_handler src dst st msg = (st', sends, nts, cts) ->
    In (src, Busy) sends.
Proof.
  intros.
  find_apply_lem_hyp real_requests_get_queued_and_busy_response; tauto.
Qed.

Lemma real_requests_get_queued :
  forall src dst msg st st' sends nts cts,
    request_payload msg ->
    cur_request st <> None ->
    msg <> Ping ->
    recv_handler src dst st msg = (st', sends, nts, cts) ->
    In (src, msg) (delayed_queries st').
Proof.
  intros.
  find_apply_lem_hyp real_requests_get_queued_and_busy_response; tauto.
Qed.

Lemma real_requests_get_response_handle_query_req :
  forall st src req sends,
    request_payload req ->
    req <> Ping ->
    handle_query_req st src req = sends ->
    exists res,
      In (src, res) sends /\
      request_response_pair req res.
Proof.
  intros.
  match goal with
  | [H: request_payload _ |- _] =>
    inv H; congruence || simpl
  end;
    eexists; intuition eauto; constructor.
Qed.

Lemma pings_always_get_pongs_handle_msg :
  forall src dst st st' sends nts cts,
    handle_msg src dst st Ping = (st', sends, nts, cts) ->
    In (src, Pong) sends.
Proof.
  intros.
  find_apply_lem_hyp handle_msg_definition; expand_def;
    solve [auto with datatypes | congruence].
Qed.

Lemma pings_always_get_pongs_recv_handler :
  forall src dst st st' sends nts cts,
    recv_handler src dst st Ping = (st', sends, nts, cts) ->
    In (src, Pong) sends.
Proof.
  intros.
  find_apply_lem_hyp recv_handler_definition_existential; expand_def.
  apply in_or_app; right.
  eapply pings_always_get_pongs_handle_msg; eauto.
Qed.

Lemma real_requests_get_responses_handle_msg :
  forall src dst st req st' sends nts cts,
    handle_msg src dst st req = (st', sends, nts, cts) ->
    request_payload req ->
    req <> Ping ->
    cur_request st = None ->
    exists res,
      In (src, res) sends /\
      request_response_pair req res.
Proof.
  intros.
  find_apply_lem_hyp handle_msg_definition; expand_def.
  - solve_by_inversion.
  - congruence.
  - find_apply_lem_hyp is_request_same_as_request_payload; congruence.
  - find_apply_lem_hyp is_request_same_as_request_payload; congruence.
  - eapply real_requests_get_response_handle_query_req; eauto.
Qed.

Lemma real_requests_get_responses_recv_handler :
  forall src dst st req st' sends nts cts,
    recv_handler src dst st req = (st', sends, nts, cts) ->
    request_payload req ->
    req <> Ping ->
    cur_request st = None ->
    exists res,
      In (src, res) sends /\
      request_response_pair req res.
Proof.
  intros.
  find_apply_lem_hyp recv_handler_definition_existential; expand_def.
  find_apply_lem_hyp real_requests_get_responses_handle_msg; eauto.
  break_exists_exists; break_and.
  eauto with datatypes.
Qed.

Lemma requests_are_always_responded_to :
  forall src dst req st st' sends nts cts,
    request_payload req ->
    recv_handler src dst st req = (st', sends, nts, cts) ->

    cur_request st <> None /\
    req <> Ping /\
    In (src, Busy) sends \/

    exists res,
      In (src, res) sends /\
      request_response_pair req res.
Proof.
  intros.
  destruct (payload_eq_dec req Ping); subst.
  - right.
    eexists; eauto using pings_always_get_pongs_recv_handler, pair_Ping.
  - destruct (cur_request st) eqn:?H.
    + find_copy_eapply_lem_hyp real_requests_get_busy_response; eauto.
      * left; repeat split; assumption || congruence.
      * congruence.
    + find_apply_lem_hyp real_requests_get_responses_recv_handler; auto.
Qed.

Lemma apply_handler_result_preserves_nodes :
  forall gst gst' h res e,
    gst' = apply_handler_result h res e gst ->
    nodes gst = nodes gst'.
Proof using.
  unfold apply_handler_result.
  intuition.
  repeat break_let.
  find_rewrite; auto.
Qed.

Lemma apply_handler_result_preserves_failed_nodes :
  forall gst gst' h res e,
    gst' = apply_handler_result h res e gst ->
    failed_nodes gst = failed_nodes gst'.
Proof using.
  unfold apply_handler_result.
  intuition.
  repeat break_let.
  find_rewrite; auto.
Qed.

Lemma joined_preserved_by_start_query :
  forall h st k st' ms nts cts,
    start_query h st k = (st', ms, nts, cts) ->
    joined st = joined st'.
Proof using.
  unfold start_query.
  intuition.
  break_match.
  - break_let.
    tuple_inversion.
    unfold update_query; auto.
  - tuple_inversion; auto.
Qed.

Lemma joined_preserved_by_do_rectify :
  forall h st st' ms' cts' nts' eff,
    do_rectify h st = (st', ms', cts', nts', eff) ->
    joined st = joined st'.
Proof using.
  intros.
  find_eapply_lem_hyp do_rectify_definition; expand_def;
    try find_eapply_lem_hyp joined_preserved_by_start_query;
    simpl in *; eauto.
Qed.

Lemma joined_preserved_by_do_delayed_queries :
  forall h st st' ms nts cts,
    do_delayed_queries h st = (st', ms, nts, cts) ->
    joined st = joined st'.
Proof.
  intros.
  find_eapply_lem_hyp do_delayed_queries_definition; expand_def;
    simpl in *; eauto.
Qed.

Lemma joined_preserved_by_end_query :
  forall st st' ms ms' cts cts' nts nts',
    end_query (st, ms, cts, nts) = (st', ms', cts', nts') ->
    joined st = joined st'.
Proof using.
  unfold end_query.
  intros.
  tuple_inversion.
  tauto.
Qed.

Lemma joined_preserved_by_handle_stabilize :
  forall h src st q new_succ succ st' ms nts cts,
    handle_stabilize h src st q new_succ succ = (st', ms, nts, cts) ->
    joined st = joined st'.
Proof using.
  unfold handle_stabilize.
  unfold update_succ_list.
  intuition.
  repeat break_match;
    solve [find_apply_lem_hyp joined_preserved_by_start_query; auto |
           find_apply_lem_hyp joined_preserved_by_end_query; auto].
Qed.

Lemma joined_preserved_by_end_query_handle_rectify :
  forall st p n st' ms nts cts,
    end_query (handle_rectify st p n) = (st', ms, nts, cts) ->
    joined st = joined st'.
Proof using.
  unfold handle_rectify.
  intuition.
  repeat break_match;
    find_apply_lem_hyp joined_preserved_by_end_query;
    now simpl in *.
Qed.

(* not as strong as the other ones since handle_query for a Join query can change joined st from false to true *)
Lemma joined_preserved_by_handle_query :
  forall src h st q m st' ms nts cts,
    handle_query_res src h st q m = (st', ms, nts, cts) ->
    joined st = true ->
    joined st' = true.
Proof.
  intros.
  find_eapply_lem_hyp handle_query_res_definition; expand_def; auto;
    try (find_eapply_lem_hyp joined_preserved_by_end_query; simpl in *; congruence).
  - find_eapply_lem_hyp joined_preserved_by_end_query_handle_rectify; congruence.
  - find_eapply_lem_hyp joined_preserved_by_handle_stabilize; congruence.
  - find_eapply_lem_hyp joined_preserved_by_start_query; simpl in *; congruence.
Qed.

Lemma schedule_rectify_with_definition :
  forall st rw st' ms nts cts,
    schedule_rectify_with st rw = (st', ms, nts, cts) ->

    ms = [] /\
    cts = [] /\

    ((exists rw0,
        rectify_with st = Some rw0 /\
        nts = [] /\
        (ptr_between_bool rw0 rw (ptr st) = true /\
         st' = set_rectify_with st rw \/
         ptr_between_bool rw0 rw (ptr st) = false /\
         st' = st)) \/

     rectify_with st = None /\
     st' = st /\
     nts = [RectifyTick]).
Proof.
  unfold schedule_rectify_with.
  intros.
  repeat break_match; tuple_inversion;
    intuition (eexists; eauto).
Qed.

Lemma joined_preserved_by_schedule_rectify_with :
  forall st rw st' ms nts cts,
    schedule_rectify_with st rw = (st', ms, nts, cts) ->
    joined st = joined st'.
Proof.
  intros.
  simpl in *.
  find_apply_lem_hyp schedule_rectify_with_definition; expand_def;
    simpl; auto.
Qed.

Lemma joined_preserved_by_recv_handler :
  forall src h st msg st' ms nts cts,
    recv_handler src h st msg = (st', ms, nts, cts) ->
    joined st = true ->
    joined st' = true.
Proof using.
  intros.
  find_apply_lem_hyp recv_handler_definition_existential; expand_def.
  find_apply_lem_hyp joined_preserved_by_do_delayed_queries.
  find_apply_lem_hyp handle_msg_definition; expand_def; try congruence.
  - find_apply_lem_hyp joined_preserved_by_schedule_rectify_with; congruence.
  - find_apply_lem_hyp handle_query_req_busy_definition; expand_def; simpl in *; congruence.
  - find_apply_lem_hyp joined_preserved_by_handle_query; congruence.
Qed.

Lemma joined_preserved_by_tick_handler :
  forall h st st' ms nts cts eff,
    tick_handler h st = (st', ms, nts, cts, eff) ->
    joined st = joined st'.
Proof using.
  intros.
  find_apply_lem_hyp tick_handler_definition; expand_def; auto.
  destruct (start_query _ _ _) as [[[[?st ?ms] ?nts] ?cts] ?eff] eqn:?H.
  find_eapply_lem_hyp add_tick_definition; expand_def.
  find_eapply_lem_hyp joined_preserved_by_start_query.
  congruence.
Qed.

Lemma joined_preserved_by_handle_query_timeout :
  forall h st dst q st' ms nts cts,
    handle_query_timeout h st dst q = (st', ms, nts, cts) ->
    joined st = joined st'.
Proof using.
  unfold handle_query_timeout.
  intuition.
  repeat break_match;
    find_apply_lem_hyp joined_preserved_by_end_query ||
                       find_apply_lem_hyp joined_preserved_by_start_query;
    eauto.
Qed.

Lemma joined_preserved_by_timeout_handler_eff :
  forall h st t st' ms nts cts eff,
    timeout_handler_eff h st t = (st', ms, nts, cts, eff) ->
    joined st = joined st'.
Proof using.
  unfold timeout_handler_eff.
  intuition.
  repeat break_match;
    try tuple_inversion;
    eauto using joined_preserved_by_tick_handler, joined_preserved_by_handle_query_timeout, joined_preserved_by_do_rectify.
  - apply keepalive_handler_definition in H; expand_def; auto.
  - find_apply_lem_hyp request_timeout_handler_definition; expand_def; try reflexivity.
    find_apply_lem_hyp handle_query_timeout_definition;
      expand_def;
      try find_apply_lem_hyp end_query_definition;
      try find_apply_lem_hyp start_query_definition;
      expand_def;
      reflexivity.
Qed.

Lemma apply_handler_result_updates_sigma :
  forall h st ms nts cts e gst gst',
    gst' = apply_handler_result h (st, ms, nts, cts) e gst ->
    sigma gst' h = Some st.
Proof using.
  unfold apply_handler_result, update.
  intuition.
  repeat find_rewrite.
  simpl in *.
  break_if; congruence.
Qed.

Lemma sigma_ahr_updates :
  forall gst n st ms nts cts e,
    sigma (apply_handler_result n (st, ms, nts, cts) e gst) n = Some st.
Proof using.
  unfold apply_handler_result.
  simpl.
  intros.
  exact: update_eq.
Qed.

Lemma sigma_ahr_passthrough :
  forall gst n st ms nts cts e h d,
    n <> h ->
    sigma gst h = Some d ->
    sigma (apply_handler_result n (st, ms, nts, cts) e gst) h = Some d.
Proof using.
  unfold apply_handler_result.
  simpl.
  intros.
  find_reverse_rewrite.
  exact: update_diff.
Qed.

Lemma handle_msg_stabilize_response_pred_worse_sets_succs :
  forall s h st p succs,
    cur_request st = Some (make_pointer s, Stabilize, GetPredAndSuccs) ->
    ptr_between_bool (ptr st) p (make_pointer s) = false ->
    forall st' ms nts cts,
      handle_msg s h st (GotPredAndSuccs (Some p) succs) = (st', ms, nts, cts) ->
      succ_list st' = make_succs (make_pointer s) succs.
Proof.
  intros until 2.
  unfold handle_msg.
  find_rewrite; simpl.
  repeat (break_if; try congruence).
  intros.
  find_injection.
  reflexivity.
Qed.

Lemma recv_handler_stabilize_response_pred_worse_sets_succs :
  forall s h st p succs,
    cur_request st = Some (make_pointer s, Stabilize, GetPredAndSuccs) ->
    ptr_between_bool (ptr st) p (make_pointer s) = false ->
    forall st' ms nts cts,
      recv_handler s h st (GotPredAndSuccs (Some p) succs) = (st', ms, nts, cts) ->
      succ_list st' = make_succs (make_pointer s) succs.
Proof.
  intros until 2.
  unfold recv_handler.
  repeat break_let.
  intros.
  find_injection.
  erewrite <- succ_list_preserved_by_do_delayed_queries; eauto.
  eapply handle_msg_stabilize_response_pred_worse_sets_succs; eauto.
Qed.

Lemma ptr_between_ptr_between_bool :
  forall a b c,
    ptr_between a b c ->
    ptr_between_bool a b c = true.
Proof.
  unfold ptr_between, ptr_between_bool.
  intros.
  now apply between_between_bool_equiv.
Qed.
Hint Resolve ptr_between_ptr_between_bool.

Lemma not_ptr_between :
  forall a b c,
    ~ ptr_between a b c ->
    ptr_between_bool a b c = false.
Proof.
  intros.
  destruct (ptr_between_bool _ _ _) eqn:?H; [|reflexivity].
  find_apply_lem_hyp between_between_bool_equiv.
  exfalso; eauto.
Qed.
Hint Resolve not_ptr_between.

Lemma between_bool_false_not_between :
  forall x y z,
    between_bool x y z = false ->
    ~ between x y z.
Proof.
  intuition.
  find_apply_lem_hyp between_between_bool_equiv.
  congruence.
Qed.
Hint Resolve between_bool_false_not_between.

Lemma ptr_between_bool_false :
  forall a b c,
    ptr_between_bool a b c = false ->
    ~ ptr_between a b c.
Proof.
  unfold ptr_between, ptr_between_bool.
  intros.
  now apply between_bool_false_not_between.
Qed.
Hint Resolve ptr_between_bool_false.

Lemma ptr_between_bool_true :
  forall a b c,
    ptr_between_bool a b c = true ->
    ptr_between a b c.
Proof.
  unfold ptr_between, ptr_between_bool.
  intros.
  now apply between_bool_between.
Qed.
Hint Resolve ptr_between_bool_true.

Lemma handle_stabilize_definition :
  forall h src st q ns succs result,
    handle_stabilize h src st q ns succs = result ->
    (exists new_succ,
        ns = Some new_succ /\
        (ptr_between (ptr st) new_succ src /\
         start_query h (update_succ_list st (make_succs src succs)) (Stabilize2 new_succ) = result \/
         ~ ptr_between (ptr st) new_succ src /\
         end_query (update_succ_list st (make_succs src succs), [(addr_of src, Notify)], [], []) = result)) \/
    ns = None /\
    end_query (update_succ_list st (make_succs src succs), [(addr_of src, Notify)], [], []) = result.
Proof.
  unfold handle_stabilize.
  intros; repeat break_match;
    solve [left; econstructor; eauto | right; eauto].
Qed.

Lemma timeouts_in_None :
  forall st,
    cur_request st = None ->
    timeouts_in st = [].
Proof.
  unfold timeouts_in.
  intros; find_rewrite; reflexivity.
Qed.

Lemma timeouts_in_Some :
  forall st dst q m,
    cur_request st = Some (dst, q, m) ->
    timeouts_in st = [Request (addr_of dst) m].
Proof.
  unfold timeouts_in.
  intros; find_rewrite; reflexivity.
Qed.

Lemma timeouts_in_update_pred :
  forall st p,
    timeouts_in (update_pred st p) = timeouts_in st.
Proof.
  easy.
Qed.
Hint Rewrite timeouts_in_update_pred.

Lemma timeouts_in_update_succ_list :
  forall st sl,
    timeouts_in (update_succ_list st sl) = timeouts_in st.
Proof.
  easy.
Qed.
Hint Rewrite timeouts_in_update_succ_list.

Lemma timeouts_in_update_for_join :
  forall st sl,
    timeouts_in (update_for_join st sl) = timeouts_in st.
Proof.
  easy.
Qed.
Hint Rewrite timeouts_in_update_for_join.


Lemma NoDup_two_diff :
  forall A (a b : A),
    a <> b ->
    NoDup [a; b].
Proof.
  intros.
  constructor.
  - intro; find_apply_lem_hyp In_cons_neq; auto.
  - repeat constructor; auto.
Qed.

(* Hints for reasoning about handlers *)
Hint Unfold clear_delayed_queries.
Hint Unfold next_msg_for_join.
Hint Constructors request_payload.
Hint Constructors response_payload.
Hint Constructors NoDup.
Hint Resolve NoDup_disjoint_append.
Hint Resolve NoDup_two_diff.
Hint Extern 1 (_ <> _) => congruence.

(* TODO(ryan) move to structtact! *)
Lemma in_singleton_eq :
  forall A (x y : A),
    In x [y] ->
    x = y.
Proof.
  intros.
  simpl in *.
  intuition.
Qed.

Ltac handler_def :=
  match goal with
  | H: recv_handler _ _ _ _ = _ |- _ =>
    apply recv_handler_definition_existential in H; expand_def
  | H: handle_msg _ _ _ _ = _ |- _ =>
    apply handle_msg_definition in H; expand_def
  | H: end_query (_, _, _, _) = _ |- _ =>
    apply end_query_definition in H; expand_def
  | H: end_query (?arg) = _ |- _ =>
    destruct arg as [[[? ?] ?] ?] eqn:?
  | H: handle_query_res _ _ _ _ _ = _ |- _ =>
    apply handle_query_res_definition in H; expand_def
  | H: handle_query_req_busy _ _ _ = _ |- _ =>
    apply handle_query_req_busy_definition in H; expand_def
  | H: handle_rectify _ _ _ = _ |- _ =>
    apply handle_rectify_definition in H; expand_def
  | H: handle_stabilize _ _ _ _ _ _ = _ |- _ =>
    apply handle_stabilize_definition in H; expand_def
  | H: start_query _ _ _ = _ |- _ =>
    apply start_query_definition in H; expand_def
  | H: start_query ?h ?st ?q = _ |- _ =>
    destruct (start_query ?h ?st ?q) as [[[? ?] ?] ?] eqn:?
  | H: do_delayed_queries _ _ = _ |- _ =>
    apply do_delayed_queries_definition in H; expand_def
  | H: schedule_rectify_with _ _ = _ |- _ =>
    apply schedule_rectify_with_definition in H; expand_def
  end.

Ltac handler_simpl :=
  match goal with
  | |- _ => progress subst
  | H: _ = _ |- _ => injc H
  | H: In _ [_] |- _ => apply in_singleton_eq in H
  | |- _ => progress simpl in *
  | |- _ => progress autounfold in *
  | |- _ => progress autorewrite with list core in *
  | H: cur_request ?st = Some _ |- context[timeouts_in ?st] =>
    erewrite timeouts_in_Some; [|eassumption]
  | H: cur_request ?st = None |- context[timeouts_in ?st] =>
    erewrite timeouts_in_None; [|eassumption]
  | |- _ => solve [assumption | congruence | eauto ]
  end.

Lemma handle_query_res_info_from_changed_set_cur_request :
  forall src dst st q p st' ms nts cts,
    handle_query_res src dst st q p = (st', ms, nts, cts) ->
    forall dstp q' req,
      cur_request st <> cur_request st' ->
      cur_request st' = Some (dstp, q', req) ->

      (exists dstp succs,
          nts = [Request (addr_of dstp) GetSuccList] /\
          cts = timeouts_in st /\
          q = Stabilize /\
          p = GotPredAndSuccs (Some dstp) succs /\
          cur_request st' = Some (dstp, Stabilize2 dstp, GetSuccList) /\
          ptr_between (ptr st) dstp (make_pointer src)) \/

      (exists j dstp,
          nts = [Request (addr_of dstp) GetSuccList] /\
          cts = [Request (addr_of dstp) (GetBestPredecessor (ptr st))] /\
          q = Join j /\
          p = GotBestPredecessor dstp /\
          addr_of dstp = src /\
          cur_request st' = Some (dstp, Join j, GetSuccList)) \/

      (exists j dstp,
          nts = [Request (addr_of dstp) (GetBestPredecessor (ptr st))] /\
          cts = [Request src (GetBestPredecessor (ptr st))] /\
          q = Join j /\
          p = GotBestPredecessor dstp /\
          addr_of dstp <> src /\
          cur_request st' = Some (dstp, Join j, GetBestPredecessor (ptr st))) \/

      exists j dstp rest,
        nts = [Request (addr_of dstp) GetSuccList] /\
        cts = timeouts_in st /\
        q = Join j /\
        p = GotSuccList (dstp :: rest) /\
        cur_request st' = Some (dstp, Join2 dstp, GetSuccList).
Proof.
  intros.
  repeat (handler_def || handler_simpl);
    intuition (repeat eexists; eauto).
Qed.

Lemma cur_request_preserved_by_do_delayed_queries :
  forall h st st' ms nts cts,
    do_delayed_queries h st = (st', ms, nts, cts) ->
    cur_request st = cur_request st'.
Proof.
  intros; handler_def; reflexivity.
Qed.

Inductive possible_nts (st : data) : list timeout -> Prop :=
| NilPossible :
    possible_nts st []
| TickPossible :
    possible_nts st [Tick]
| RectifyTickPossible :
    possible_nts st [RectifyTick]
| KeepaliveTickPossible :
    possible_nts st [KeepaliveTick]
| Stabilize2RequestPossible :
    forall h dstp p,
      cur_request st = Some (dstp, Stabilize, p) ->
      possible_nts st [Request h GetSuccList]
| JoinGSLRequestPossible :
    forall h j dstp p,
      cur_request st = Some (dstp, Join j, p) ->
      possible_nts st [Request h GetSuccList]
| JoinGBPRequestPossible :
    forall h j dstp p,
      cur_request st = Some (dstp, Join j, p) ->
      possible_nts st [Request h (GetBestPredecessor (ptr st))]
| RefreshRequestPossible :
    forall dstp q p,
      cur_request st = Some (dstp, q, p) ->
      possible_nts st [Request (addr_of dstp) p].
Hint Constructors possible_nts.

Inductive possible_cts (st : data) : list timeout -> Prop :=
| NilClearedPossible :
    possible_cts st []
| KeepaliveTickClearedPossible :
    possible_cts st [KeepaliveTick]
| CurRequestClearedPossible :
    forall dstp q p,
      cur_request st = Some (dstp, q, p) ->
      possible_cts st [Request (addr_of dstp) p]
| CurRequestAndKeepaliveTickClearedPossible :
    forall dstp q p,
      cur_request st = Some (dstp, q, p) ->
      possible_cts st [Request (addr_of dstp) p; KeepaliveTick]
| GetBestPredClearedPossible :
    forall src,
      possible_cts st [Request src (GetBestPredecessor (ptr st))].
Hint Constructors possible_cts.

Lemma recv_handler_possible_nts :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    possible_nts st nts.
Proof.
  intros.
  repeat (handler_def || handler_simpl).
Qed.
Hint Resolve recv_handler_possible_nts.

Lemma recv_handler_nodup_nts :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    NoDup nts.
Proof.
  intros.
  assert (possible_nts st nts) by eauto.
  invcs_prop possible_nts; eauto.
Qed.

Lemma recv_handler_possible_cts :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    possible_cts st cts.
Proof.
  intros.
  repeat (handler_def || handler_simpl).
Qed.

Lemma recv_handler_nodup_cts :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    NoDup cts.
Proof.
  intros.
  repeat (handler_def || handler_simpl).
Qed.

Lemma recv_handler_small_cts :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    length cts <= 2.
Proof.
  intros.
  repeat (handler_def || handler_simpl).
Qed.

Lemma recv_handler_sets_cur_request_when_adding_new_timeout :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    forall dst req,
      In (Request dst req) nts ->
      ~ In (Request dst req) cts ->
      exists dstp q,
        addr_of dstp = dst /\
        query_request q req /\
        cur_request st' = Some (dstp, q, req).
Proof.
  intros.
  repeat (handler_def || handler_simpl || expand_def).
Qed.

Lemma cur_request_related_when_refreshing_timeout :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    forall dst req,
      In (Request dst req) nts ->
      In (Request dst req) cts ->
      exists dstp q,
        addr_of dstp = dst /\
        cur_request st = Some (dstp, q, req).
Proof.
  intros.
  repeat (handler_def || handler_simpl || expand_def);
    find_erewrite_lem timeouts_in_Some;
    find_apply_lem_hyp in_singleton_eq;
    find_injection;
    repeat find_rewrite;
    repeat eexists; intuition eauto.
Qed.

Lemma split_eq_singleton :
  forall A (x y : A) xs ys,
    [x] = xs ++ y :: ys ->
    x = y /\
    xs = [] /\
    ys = [].
Proof.
  destruct xs; destruct ys;
    intros; simpl in *.
  - intuition congruence.
  - find_inversion.
  - find_inversion;
      exfalso; eapply app_cons_not_nil; eauto.
  - find_inversion;
      exfalso; eapply app_cons_not_nil; eauto.
Qed.

Lemma recv_handler_sends_request_when_adding_new_timeout :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    forall dst req,
      In (Request dst req) nts ->
      ~ In (Request dst req) cts ->
      In (dst, req) ms /\
      request_payload req /\
      forall dst' req' xs ys,
        ms = xs ++ (dst, req) :: ys ->
        request_payload req' ->
        In (dst', req') (xs ++ ys) ->
        False.
Proof.
  intros.
  repeat (handler_def || handler_simpl || expand_def);
    intuition;
    solve [find_copy_apply_lem_hyp split_eq_singleton; expand_def; tauto].
Qed.

Lemma handle_query_req_only_sends_responses :
  forall st src p dst res,
    In (dst, res) (handle_query_req st src p) ->
    response_payload res.
Proof.
  unfold handle_query_req.
  intros.
  repeat break_match; simpl in *; intuition; find_injection; auto.
Qed.
Hint Resolve handle_query_req_only_sends_responses.

Lemma handle_delayed_query_only_sends_responses :
  forall h st l dst p,
    In (dst, p) (concat (map (handle_delayed_query h st) l)) ->
    response_payload p.
Proof.
  intros until 0.
  rewrite <- flat_map_concat_map.
  intros.
  find_apply_lem_hyp in_flat_map; expand_def.
  unfold handle_delayed_query in *.
  repeat break_match; eauto.
Qed.
Hint Resolve handle_delayed_query_only_sends_responses.

Lemma request_response_mutually_exclusive :
  forall p,
    request_payload p ->
    response_payload p ->
    False.
Proof.
  intros.
  destruct p;
    invcs_prop request_payload;
    invcs_prop response_payload.
Qed.
Hint Resolve request_response_mutually_exclusive.

Lemma recv_handler_adds_new_timeout_when_sending_request :
  forall src h st p st' ms nts cts,
    recv_handler src h st p = (st', ms, nts, cts) ->
    forall dst req,
      request_payload req ->
      In (dst, req) ms ->
      In (Request dst req) nts.
Proof.
  intros.
  repeat (handler_def || handler_simpl || expand_def);
    repeat (handler_simpl || in_crush);
    try solve [inv_prop request_payload].
Qed.
