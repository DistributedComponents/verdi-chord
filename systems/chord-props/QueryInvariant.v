Require Import List.
Require Import Omega.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.

Set Bullet Behavior "Strict Subproofs".

Ltac start_cases :=
  match goal with
  | [H : ?h' = ?h \/ _,
     H' : update _ (timeouts ?gst) ?h' _ ?h = _ ++ _ :: _
     |- _] =>
    destruct H
  end.

Ltac fail_cases :=
  idtac.

Ltac timeout_cases :=
  idtac.

Ltac recv_cases :=
  idtac.

Ltac input_cases :=
  idtac.

Ltac client_cases :=
  idtac.

Ltac step_dynamic_cases :=
  match goal with
  | H : step_dynamic ?gst ?gst' |- _ =>
    invcs H;
    [ start_cases
    | fail_cases
    | timeout_cases
    | recv_cases
    | input_cases
    | client_cases
    ];
    subst_max;
    rewrite_update;
    try find_injection
  end.

Definition at_most_one_request_timeout (gst : global_state) (h : addr) :=
  forall xs ys dst p,
    timeouts gst h = xs ++ Request dst p :: ys ->
    forall dst' p',
      ~ In (Request dst' p') (xs ++ ys).
Hint Unfold at_most_one_request_timeout.

Lemma at_most_one_request_timeout_uniqueness :
  forall gst h dst dst' p p',
    at_most_one_request_timeout gst h ->
    In (Request dst p) (timeouts gst h) ->
    In (Request dst' p') (timeouts gst h) ->
    Request dst p = Request dst' p'.
Proof.
  unfold at_most_one_request_timeout.
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
    intuition eauto.
  - easy.
Qed.

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

Inductive request_msg_for_query : query -> payload -> Prop :=
| RectifyMsg :
    forall p,
      request_msg_for_query (Rectify p) Ping
| StabilizeMsg :
    request_msg_for_query Stabilize GetPredAndSuccs
| Stabilize2Msg :
    forall p,
      request_msg_for_query (Stabilize2 p) GetSuccList
| JoinGetBestPredecessor :
    forall k p,
      request_msg_for_query (Join k) (GetBestPredecessor p)
| JoinGetSuccList :
    forall k,
      request_msg_for_query (Join k) GetSuccList
| Join2Msg :
    forall s,
      request_msg_for_query (Join2 s) GetSuccList.

Definition open_request_to (gst : global_state) (h : addr) (dst : addr) (m : payload) : Prop :=
  In (Request dst m) (timeouts gst h) /\
  exists q st dstp,
    request_msg_for_query q m /\
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