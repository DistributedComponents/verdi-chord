Require Import List.
Require Import Omega.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.

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
    autounfold; intros.
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
  autounfold; intros.
  destruct xs; simpl in *; find_injection.
  - eapply at_most_one_request_timeout'_remove_drops_all; eauto.
  - eapply at_most_one_request_timeout'_remove_drops_all; eauto.
    find_rewrite; eauto with datatypes.
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

Lemma start_handler_init_state_preset :
  forall h knowns,
    length knowns > 1 ->
    start_handler h knowns =
    (init_state_preset h
                       (find_pred h (sort_by_between h (map make_pointer knowns)))
                       (find_succs h (sort_by_between h (map make_pointer knowns))),
     nil,
     Tick :: nil).
Proof.
  intros.
  unfold start_handler.
  repeat break_match;
    match goal with H : _ = _ |- _ => symmetry in H end;
    find_copy_apply_lem_hyp sort_by_between_permutes;
    [| | reflexivity];
    find_apply_lem_hyp Permutation.Permutation_length;
    rewrite map_length in *; simpl in *; repeat find_reverse_rewrite;
      exfalso; eapply gt_irrefl; eauto.
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

Theorem at_most_one_request_timeout_invariant :
  forall gst h,
    reachable_st gst ->
    at_most_one_request_timeout gst h.
Proof.
Admitted.

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
    find_false;
    intuition.
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
    solve [tauto | find_false; intuition].
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
Hint Constructors cur_request_timeouts_ok.

Definition all_nodes_cur_request_timeouts_related (gst : global_state) : Prop :=
  forall h st,
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
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
  autounfold; intros.
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
             eauto using remove_In with datatypes.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
           ++ admit.
           ++ admit.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
           ++ simpl;
                eauto with datatypes;
                econstructor; intros; eauto;
                  rewrite remove_comm;
                  eauto using remove_preserve.
              admit.
        -- repeat (handler_def || handler_simpl).
      * find_copy_eapply_lem_hyp recv_msg_not_right_response_preserves_cur_request; eauto.
        find_eapply_lem_hyp recv_msg_not_right_response_never_removes_request_timeout; eauto.
        inv_prop cur_request_timeouts_ok; try congruence.
        repeat find_rewrite; rewrite_update; find_injection.
        break_or_hyp.
        -- econstructor 2; eauto with datatypes.
           admit.
        -- admit.
  - repeat find_rewrite; rewrite_update; eauto.
Admitted.

Lemma open_request_with_response_on_wire_closed_or_preserved :
  forall gst l gst' src dst req res,
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
Admitted.