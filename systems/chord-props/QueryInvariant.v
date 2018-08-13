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

Ltac chan2msg :=
  repeat match goal with
         | |- In _ (channel _ _ _) =>
           apply in_msgs_in_channel
         | H: In _ (channel _ _ _) |- _ =>
           apply in_channel_in_msgs in H
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
  handler_def.
Admitted.

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
        find_apply_lem_hyp send_keepalives_delayed_only; expand_def.
        destruct x0.
        find_eapply_lem_hyp delayed_query_sources_active; eauto.
        simpl in *.
        break_match; subst; auto.
        exfalso; eauto.
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
          destruct (channel gst' src dst) eqn:?; [reflexivity|exfalso].
          assert (In p (channel gst' src dst)) by (rewrite Heql; in_crush).
          assert (~ In dst (nodes gst')) by congruence.
          find_eapply_prop dst.
          eapply msgs_only_to_live_nodes; [eapply reachableStep; eauto|].
          chan2msg.
          eauto.
        }
        rewrite Hnomsgs.
        erewrite Hcr in * by eauto.
        constructor; eauto.
      * replace (nodes gst') with (nodes gst) by auto.
        replace (failed_nodes gst') with (failed_nodes gst) by auto.
        assert (Hnomsgs: channel gst' src dst = []).
        {
          destruct (channel gst' src dst) eqn:?; [reflexivity|exfalso].
          assert (In p (channel gst' src dst)) by (rewrite Heql; in_crush).
          assert (~ In dst (nodes gst')) by congruence.
          find_eapply_prop dst.
          eapply msgs_only_to_live_nodes; [eapply reachableStep; eauto|].
          chan2msg.
          eauto.
        }
        rewrite Hnomsgs.
        constructor; eauto.
        intros; in_crush.
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
        -- inv_option_map.
           erewrite channel_msgs_unchanged with (dst := src); eauto.
           repeat find_reverse_rewrite.
           replace (sigma gst' dst) with (@None data).
           eapply QMNotStarted; congruence || eauto.
           ++ intros; find_eapply_prop cur_request.
              now repeat find_rewrite || rewrite_update || find_injection.
           ++ repeat find_rewrite.
              rewrite_update.
              symmetry; auto.
        -- inv_option_map.
           erewrite channel_msgs_unchanged with (dst := src); eauto.
           repeat find_reverse_rewrite.
           replace (sigma gst' dst) with (@None data).
           eapply QMNotStarted; congruence || eauto.
           ++ intros; find_eapply_prop cur_request.
              now repeat find_rewrite || rewrite_update || find_injection.
           ++ repeat find_rewrite.
              rewrite_update.
              symmetry; auto.
      * inv_option_map.
        erewrite channel_msgs_unchanged with (dst := src); eauto.
        repeat find_rewrite.
        rewrite_update.
        repeat find_rewrite; simpl.
        eapply QMClient; eauto.
Qed.

Theorem query_message_ok'_tick_invariant :
 chord_tick_invariant
   (fun g : global_state =>
    forall src dst st__src,
    sigma g src = Some st__src ->
    query_message_ok' src dst (cur_request st__src)
      (option_map delayed_queries (sigma g dst)) (nodes g) (failed_nodes g) (channel g src dst)
      (channel g dst src)).
Proof.
Admitted.

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

Lemma handle_query_timeout_dqs :
  forall h st dst q st' ms nts cts,
    handle_query_timeout h st dst q = (st', ms, nts, cts) ->
    delayed_queries st' = delayed_queries st.
Proof.
  intros; repeat handler_def; reflexivity.
Qed.

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

Lemma handle_msg_dqs_change_queue :
  forall src dst st p st' ms nts cts,
    handle_msg src dst st p = (st', ms, nts, cts) ->
    delayed_queries st' <> delayed_queries st ->
    delayed_queries st' = dedup send_eq_dec ((src, p) :: delayed_queries st).
Proof.
  intros.
  repeat (handler_def || handler_simpl).
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

Lemma no_requests_app :
  forall xs ys,
    no_requests xs ->
    no_requests ys ->
    no_requests (xs ++ ys).
Proof.
  unfold no_requests.
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
         admit.
      -- inv_option_map.
         repeat find_rewrite.
         simpl.
         find_reverse_rewrite.
         erewrite !(channel_msgs_unchanged _ gst' gst); eauto.
         replace (channel gst src dst0) with (@nil payload).
         replace (channel gst dst0 src) with (@nil payload).
         eapply QMNotStarted; eauto.
         intros.
         admit.
      -- inv_option_map.
         repeat find_rewrite.
         simpl.
         find_reverse_rewrite.
         erewrite !(channel_msgs_unchanged _ gst' gst); eauto.
         eapply QMClient; eauto.
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
         intros.
         admit.
         right.
         intros.
         find_injection.
         intro; subst.
         find_eapply_prop nodes.
         replace (nodes gst) with (nodes gst').
          eapply msgs_only_to_live_nodes; [eapply reachableStep; eauto|].
         repeat find_rewrite.
         apply in_or_app; left.
         apply in_map_iff.
         eexists; split; eauto.
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
Admitted.

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

Lemma cur_request_in_nodes :
  forall gst,
    reachable_st gst ->
    forall src dst q m st,
      sigma gst src = Some st ->
      cur_request st = Some (dst, q, m) ->
      In (addr_of dst) (nodes gst).
Proof.
Admitted.

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
  assert (forall src m, ~ In m (channel gst src h)).
  {
    intros.
    intro; chan2msg.
    find_eapply_lem_hyp msgs_out_of_net_go_to_clients; auto.
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
  assert (forall src, channel gst src h = []).
  {
    intros.
    destruct (channel gst src0 h) eqn:?; auto.
    exfalso.
    eapply H17.
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
        intuition eauto.
      * intuition.
        find_eapply_lem_hyp delayed_query_sources_active; eauto.
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
        replace (channel gst dst h) with (@nil payload) by auto.
        replace (channel gst h dst) with (@nil payload) by auto.
        autorewrite with list; simpl.
        destruct (addr_eq_dec k dst); try congruence.
        destruct (In_dec addr_eq_dec dst (failed_nodes gst));
          [|destruct (sigma gst dst) eqn:?].
        -- find_copy_apply_lem_hyp in_failed_in_nodes; auto.
           find_copy_apply_lem_hyp nodes_have_state; auto; expand_def.
           find_rewrite; simpl.
           eapply QMFailedNothing; in_crush.
           find_injection; auto.
        -- repeat find_rewrite; simpl.
           eapply QMLive; in_crush; eauto using only_nodes_have_state.
           eapply CIother; in_crush.
           find_eapply_lem_hyp delayed_query_sources_active; eauto.
        -- repeat find_rewrite; simpl.
           eapply QMNotStarted.
           in_crush.
           find_apply_lem_hyp nodes_have_state; expand_def; congruence.
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
        replace (channel gst src dst) with (@nil payload) by auto.
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
                  eapply H30; eauto.
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
      eapply QMNotStarted; eauto.
      * intro.
        find_apply_lem_hyp nodes_have_state;
          solve [expand_def; congruence
              |constructor; auto].
      * assert (In src (nodes gst)).
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
    assert (h <> dst).
    {
      destruct m as [? [? ?]]; simpl in *.
      repeat find_rewrite; simpl in *.
      intro; subst.
      eapply nodes_not_clients; [ | | eauto]; eauto.
      eapply msgs_only_to_live_nodes; auto.
      find_rewrite; in_crush.
    }
    erewrite (channel_msgs_remove_unchanged gst' gst);
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
