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

Set Bullet Behavior "Strict Subproofs".

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
      repeat find_rewrite.
      eauto with datatypes.
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
              repeat find_rewrite; auto with datatypes.
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

Lemma start_handler_with_single_known :
  forall h k,
    start_handler h (k :: nil) = pi (start_query h (init_state_join h k) (Join (make_pointer k))).
Proof.
  easy.
Qed.
Hint Rewrite start_handler_with_single_known.

Lemma open_pi :
  forall (x : res) a b c,
    pi x = (a, b, c) ->
    exists d,
      x = (a, b, c, d).
Proof.
  intros.
  destruct x as [[[? ?] ?] ?]; simpl in *; tuple_inversion.
  eauto.
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
    list (addr * payload) ->
    list addr ->
    list payload ->
    list payload ->
    Prop :=
| QMLive :
    forall dst outbound inbound failed dqs cr,
      ~ In dst failed ->
      query_message_ok src dst cr dqs outbound inbound ->
      query_message_ok' src dst cr dqs failed outbound inbound
| QMFailedRes :
    forall outbound inbound res dqs dstp q failed req,
      In (addr_of dstp) failed ->
      request_response_pair req res ->
      In res inbound ->
      (forall xs ys, inbound = xs ++ res :: ys -> no_responses (xs ++ ys)) ->
      no_requests outbound ->
      (forall m, ~ In (src, m) dqs) ->
      query_request q req ->
      query_message_ok' src (addr_of dstp) (Some (dstp, q, req)) dqs failed outbound inbound
| QMFailedNothing :
    forall dst outbound inbound failed cr dqs,
      In dst failed ->
      no_responses inbound ->
      query_message_ok' src dst cr dqs failed outbound inbound.

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

Theorem query_message_ok'_recv_invariant :
 chord_recv_handler_invariant
   (fun g : global_state =>
    forall (src dst : addr) (st__src st__dst : data),
    sigma g src = Some st__src ->
    sigma g dst = Some st__dst ->
    query_message_ok' src dst (cur_request st__src)
      (delayed_queries st__dst) (failed_nodes g) (channel g src dst)
      (channel g dst src)).
Proof.
  repeat autounfold; intros.
  handler_def.
Admitted.

Theorem query_message_ok'_keepalive_invariant :
 chord_keepalive_invariant
   (fun g : global_state =>
    forall (src dst : addr) (st__src st__dst : data),
    sigma g src = Some st__src ->
    sigma g dst = Some st__dst ->
    query_message_ok' src dst (cur_request st__src)
      (delayed_queries st__dst) (failed_nodes g) (channel g src dst)
      (channel g dst src)).
Proof.
  repeat autounfold; intros.
  handler_def.
Admitted.

Theorem query_message_ok'_rectify_invariant :
 chord_rectify_invariant
   (fun g : global_state =>
    forall (src dst : addr) (st__src st__dst : data),
    sigma g src = Some st__src ->
    sigma g dst = Some st__dst ->
    query_message_ok' src dst (cur_request st__src)
      (delayed_queries st__dst) (failed_nodes g) (channel g src dst)
      (channel g dst src)).
Proof.
  repeat autounfold; intros.
  handler_def.
Admitted.

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

Theorem dq_res_qmo :
  forall gst gst' src dst req res st__src st__src' st__dst st__dst' l ms,
    query_message_ok' src dst (cur_request st__src)
      (delayed_queries st__dst) (failed_nodes gst) (channel gst src dst)
      (channel gst dst src) ->
    msgs gst' = map (send dst) l ++ ms ->
    In (src, req) (delayed_queries st__dst) ->
    src <> dst ->
    (forall m, In m ms -> In m (msgs gst)) ->
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
    [|tauto|tauto].
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
    unfold channel in H18.
    repeat find_rewrite.
    find_copy_apply_lem_hyp (in_split (src, res0)); expand_def.
    rewrite ?map_app, ?map_cons, ?filterMap_app in *.
    rewrite filterMap_defn in *; break_match; simpl in *;
      repeat match goal with
             | H: context[addr_eq_dec ?x ?x] |- _ =>
               destruct (addr_eq_dec x x); simpl in H; try congruence
             end.
    find_injection.
    autorewrite with list in H18.
    match goal with
    | H: (?a ++ p :: ?b) ++ ?more = ?xs ++ p :: ?ys |- _ =>
      rewrite <- app_assoc in H; simpl in H;
        assert (a = xs /\ b ++ more = ys)
    end.
    {
      eapply splits_uniq_eq; eauto.
      intros; intro.
      assert (~ In (src, z) (x ++ x0)) by eauto.
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

Theorem query_message_ok'_request_invariant_dst_live :
 chord_request_invariant
   (fun g : global_state =>
    forall (src dst : addr) (st__src st__dst : data),
      ~ In dst (failed_nodes g) ->
        sigma g src = Some st__src ->
      sigma g dst = Some st__dst ->
      query_message_ok' src dst (cur_request st__src)
                        (delayed_queries st__dst) (failed_nodes g) (channel g src dst)
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
      handler_def; try congruence.
      handler_def.
      * repeat handler_def; simpl in *; try congruence.
        eapply CInone.
        -- admit.
        -- admit.
        -- admit.
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.
    + repeat find_rewrite || find_injection.
      inv_prop query_message_ok.
      * repeat find_rewrite || find_injection.
        handler_def; try congruence.
        simpl in *.
        replace (channel gst' src dst0) with (channel gst src dst0)
          by eauto using msgs_eq_channels_eq.
        replace (channel gst' dst0 src) with (channel gst dst0 src)
          by eauto using msgs_eq_channels_eq.
        auto.
      * repeat handler_def || handler_simpl.
        -- eapply CInone; eauto.
           simpl in *.
           admit.
           admit.
        -- admit.
        -- admit.
        -- admit.
        -- admit.
        -- admit.
        -- admit.
        -- admit.
        -- admit.
      * admit.
      * admit.
      * admit.
  - repeat find_rewrite.
    destruct (addr_eq_dec h dst0); subst.
    + repeat rewrite_update.
      erewrite (channel_msgs_unchanged ms gst'); eauto.
      find_injection.
      invcs_prop cur_request_timeouts_ok;
        [exfalso; intuition eauto|].
      match goal with
      | H: forall (_ _ : addr), _ |- _ =>
        specialize (H src dst0);
          do 2 insterU H;
          repeat (forward H; eauto; concludes)
      end.
      assert (Request dst req = Request (addr_of dstp) req0)
        by eauto using at_most_one_request_timeout'_uniqueness.
      assert (no_responses (channel gst dst0 src) ->
              (forall m, ~ In (src, m) (delayed_queries st)) ->
              no_responses (channel gst' dst0 src))
        by admit.
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
      * admit.
      * find_apply_lem_hyp do_delayed_queries_definition; expand_def.
        -- admit.
        -- repeat find_rewrite.
           replace (failed_nodes gst) with (failed_nodes gst').
           replace (channel gst src (addr_of dstp0)) with (channel gst' src (addr_of dstp0))
             by eauto using channel_msgs_unchanged.
           find_copy_apply_lem_hyp handle_query_timeout_dqs.
           destruct (handle_query_req x2 src req1) eqn:?;
             find_copy_eapply_lem_hyp real_requests_get_response_handle_query_req; eauto.
           ++ simpl in *; exfalso; expand_def; eauto.
           ++ admit.
           ++ expand_def.
             eapply dq_res_qmo; try solve [eauto|congruence];
               [apply in_or_app; right|].
             rewrite <- flat_map_concat_map, in_flat_map.
             eexists; split; eauto.
             repeat find_rewrite; eauto.
             simpl; congruence.
             intros.
             simpl in *.
             admit.
           ++ admit.
    + erewrite (channel_msgs_unchanged ms gst'); eauto.
      erewrite (channel_msgs_unchanged ms gst'); eauto.
      repeat rewrite_update; eauto.
Admitted.

Theorem query_message_ok'_request_invariant :
 chord_request_invariant
   (fun g : global_state =>
    forall (src dst : addr) (st__src st__dst : data),
    sigma g src = Some st__src ->
    sigma g dst = Some st__dst ->
    query_message_ok' src dst (cur_request st__src)
      (delayed_queries st__dst) (failed_nodes g) (channel g src dst)
      (channel g dst src)).
Proof.
  repeat autounfold; intros.
  destruct (In_dec addr_eq_dec dst0 (failed_nodes gst)).
  - repeat find_rewrite.
    update_destruct; subst; try tauto.
    admit.
  - eapply query_message_ok'_request_invariant_dst_live; eauto.
    congruence.
Admitted.

Theorem query_message_ok'_start_invariant :
 chord_start_invariant
   (fun g : global_state =>
    forall (src dst : addr) (st__src st__dst : data),
    sigma g src = Some st__src ->
    sigma g dst = Some st__dst ->
    query_message_ok' src dst (cur_request st__src)
      (delayed_queries st__dst) (failed_nodes g) (channel g src dst)
      (channel g dst src)).
Proof.
  repeat autounfold; intros.
Admitted.

Theorem query_message_ok'_invariant :
  forall gst,
    reachable_st gst ->
    forall src dst st__src st__dst,
      sigma gst src = Some st__src ->
      sigma gst dst = Some st__dst ->
      query_message_ok' src dst (cur_request st__src) (delayed_queries st__dst) (failed_nodes gst)
                       (channel gst src dst) (channel gst dst src).
Proof.
  intros gst Hreachable; pattern gst; revert Hreachable; revert gst.
  eapply chord_net_invariant.
  - autounfold; intros.
    apply QMLive; auto.
    repeat rewrite initial_st_channels_empty by auto.
    erewrite initial_st_cur_request_None by eauto.
    erewrite initial_st_delayed_queries_empty by eauto.
    eapply CInone; unfold no_requests, no_responses; eauto.
  - eapply query_message_ok'_start_invariant.
  - repeat (autounfold; intros).
    repeat find_rewrite.
    match goal with
      H: _ |- _ => specialize (H src dst st__src st__dst)
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
      inv_prop query_message_ok;
        solve [eapply QMFailedNothing; simpl; eauto
              |eapply QMFailedRes; simpl;
               try erewrite msgs_eq_channels_eq; eauto].
    + repeat erewrite (msgs_eq_channels_eq gst' gst) by eauto.
      inv_prop query_message_ok';
        solve [constructor; simpl; intuition
              |econstructor; eauto with datatypes].
  - repeat (autounfold; intros).
    assert (In dst (nodes gst'))
      by (eapply only_nodes_have_state;
          solve [try econstructor; eauto]).
    repeat find_rewrite.
    match goal with
      H: _ |- _ => specialize (H src dst)
    end.
    destruct (addr_eq_dec src h); rewrite_update.
    + subst.
      find_eapply_lem_hyp nodes_have_state; break_exists; eauto.
      repeat find_rewrite.
      do 2 find_insterU; do 2 concludes.
      inv_prop query_message_ok'.
      * constructor 1; auto.
        assert (delayed_queries st__dst = delayed_queries x).
        {
          update_destruct; rewrite_update;
            repeat find_rewrite || find_injection;
            eauto.
          repeat handler_def; simpl; reflexivity.
        }
        repeat find_rewrite.
        repeat handler_def.
        -- inv_prop query_message_ok; try congruence.
           simpl.
           unfold make_request in *.
           find_apply_lem_hyp option_map_Some; expand_def.
           repeat find_rewrite || find_injection.
           simpl in *.
           destruct (addr_eq_dec (addr_of x0) dst); subst.
           ++ eapply CIreq; eauto.
              eapply in_msgs_in_channel.
              find_rewrite.
              left.
              eauto.
              intros.
              erewrite channel_msgs_cons in * by eauto.
              assert (xs = []); subst.
              {
                destruct xs; auto.
                exfalso; simpl in *.
                find_injection.
                repeat find_rewrite.
                eapply_prop no_requests; eauto with datatypes.
              }
              simpl in *; find_injection; eauto.
              unfold no_responses; intros.
              find_apply_lem_hyp in_channel_in_msgs.
              repeat find_rewrite; simpl in *; break_or_hyp; eauto.
              rewrite send_definition in *; find_injection; eauto.
           ++ erewrite (channel_msgs_unchanged [(addr_of x0, GetPredAndSuccs)] gst');
                simpl in *; [|eauto|intuition eauto; congruence].
              eapply CIother; eauto.
              unfold no_responses; intros.
              find_apply_lem_hyp in_channel_in_msgs; repeat find_rewrite;
                simpl in *; break_or_hyp;
                  [rewrite send_definition in *; find_injection; eauto
                  |eapply_prop no_responses; eauto].
        -- find_injection.
           inv_prop query_message_ok'; try tauto.
           inv_prop query_message_ok; try congruence.
           simpl in *.
           repeat erewrite (msgs_eq_channels_eq gst' gst); eauto.
           eapply CInone; eauto.
        -- repeat find_rewrite || find_injection.
           repeat erewrite (msgs_eq_channels_eq gst' gst); eauto.
        -- repeat find_rewrite || find_injection.
           repeat erewrite (msgs_eq_channels_eq gst' gst); eauto.
      * update_destruct; rewrite_update;
          repeat find_rewrite; [tauto|].
        handler_def; try congruence;
          simpl in *; repeat find_injection.
        -- repeat erewrite (msgs_eq_channels_eq gst' gst) by eauto.
           eauto.
        -- repeat erewrite (msgs_eq_channels_eq gst' gst) by eauto.
           eauto.
      * eapply QMFailedNothing; simpl; eauto.
        unfold no_responses in *; intros.
        find_eapply_lem_hyp in_channel_in_msgs; repeat find_rewrite.
        find_apply_lem_hyp in_app_or.
        break_or_hyp;
          [|now eauto using in_msgs_in_channel].
        find_apply_lem_hyp in_map_iff.
        break_exists_name pk; break_and; destruct pk.
        rewrite send_definition in *.
        handler_def.
    + update_destruct; rewrite_update; repeat find_rewrite.
      * subst.
        assert (no_responses (channel gst dst src) ->
                no_responses (channel gst' dst src)).
        {
          intros; unfold no_responses; intros.
          find_eapply_lem_hyp in_channel_in_msgs; repeat find_rewrite.
          find_apply_lem_hyp in_app_or.
          break_or_hyp.
          - repeat handler_def; simpl in *.
            find_apply_lem_hyp option_map_Some;
              expand_def.
            rewrite send_definition in *; find_injection; eauto.
          - eapply_prop no_responses; eauto.
        }
        repeat find_injection.
        match goal with
        | H: _ |- _ => do 2 insterU H; do 2 specialize (H ltac:(eauto))
        end.
        repeat handler_def;
          try solve [repeat erewrite (msgs_eq_channels_eq gst' gst); eauto].
        simpl.
        erewrite (channel_msgs_unchanged); repeat find_rewrite; eauto.
        inv_prop query_message_ok'; try tauto.
        constructor; eauto.
        inv_prop query_message_ok;
          try solve [econstructor; eauto].
        eapply CIres; eauto.
        simpl in *.
        eapply in_msgs_in_channel.
        find_eapply_lem_hyp in_channel_in_msgs.
        repeat find_rewrite; eauto with datatypes.
        intros.
        destruct (addr_eq_dec (addr_of x) src); subst.
        -- erewrite channel_msgs_cons in H26; repeat find_rewrite; simpl; eauto.
           find_apply_lem_hyp option_map_Some; expand_def.
           destruct xs; simpl in *; find_injection.
           inv_prop request_response_pair.
           unfold no_responses; simpl; intuition.
           subst; inv_prop response_payload.
           find_eapply_prop no_responses; eauto.
        -- erewrite channel_msgs_unchanged in H26; eauto.
           right; intros; simpl in *.
           intuition; find_injection.
           eauto.
      * replace (channel gst' src dst) with (channel gst src dst);
          replace (channel gst' dst src) with (channel gst dst src);
          eauto;
          unfold channel;
          repeat find_rewrite;
          rewrite filterMap_app, (filterMap_all_None ltac:(auto) (map (send h) ms));
          eauto with datatypes;
          intros [a b];
          rewrite in_map_iff;
          intros; break_exists_name pk; break_and; destruct pk;
            rewrite send_definition in *;
            find_injection;
            simpl;
            repeat match goal with
                   | |- context[addr_eq_dec ?x ?y] =>
                     destruct (addr_eq_dec x y);
                       simpl;
                       try congruence
                   end.
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
    assert (In dst (nodes gst')).
    {
      eapply only_nodes_have_state; eauto.
      solve [econstructor; eauto].
    }
    assert (~ In h (nodes gst')).
    {
      intro.
      eapply nodes_not_clients;
        solve [try econstructor; eauto].
    }
    assert (h <> dst) by (intro; subst; tauto).
    assert (h <> src) by (intro; subst; tauto).
    erewrite (channel_msgs_unchanged [(to, i)] gst');
      [|repeat find_rewrite; simpl; eauto|left; eauto].
    erewrite (channel_msgs_unchanged [(to, i)] gst');
      [|repeat find_rewrite; simpl; eauto|left; eauto].
    replace (failed_nodes gst') with (failed_nodes gst).
    repeat find_rewrite; simpl in *.
    find_eapply_prop query_message_ok'; eauto.
    repeat find_rewrite; reflexivity.
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
      repeat find_rewrite.
      intro; subst.
      eapply nodes_not_clients; try eassumption.
      eapply only_nodes_have_state; eauto.
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
  inv_prop query_message_ok'; tauto || eauto.
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
  do 2 find_insterU.
  forwards; eauto. concludes.
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
