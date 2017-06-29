Require Import List.
Require Import Omega.
Require Import StructTact.StructTactics.

Require Import Chord.Chord.
Require Import Chord.ChordLocalProps.
Require Import Chord.ChordProof.
Require Import Chord.ChordSemantics.
Require Import Chord.ChordDefinitionLemmas.
Import ChordSemantics.
Import Chord.Chord.Chord.
Import ChordIDSpace.

Set Bullet Behavior "Strict Subproofs".

Definition at_most_one_request_timeout (gst : global_state) (h : addr) :=
  forall xs ys dst p,
    timeouts gst h = xs ++ Request dst p :: ys ->
    forall dst' p',
      ~ In (Request dst' p') (xs ++ ys).

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

Theorem at_most_one_requuest_timeout_invariant :
  forall gst h,
    reachable_st gst ->
    at_most_one_request_timeout gst h.
Proof.
Admitted.

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

Lemma msgs_initial_st_empty :
  msgs initial_st = nil.
Proof.
  unfold initial_st.
  cut (forall l gst, msgs (fold_left run_init_for l gst) = msgs gst);
    [intros; now find_higher_order_rewrite|].
  induction l; [easy|].
  intros; simpl.
  rewrite IHl.
  autounfold in *.
  simpl.
  repeat break_let.
  rewrite start_handler_init_state_preset in *;
    [| pose proof initial_nodes_length;
       pose proof Chord.succ_list_len_lower_bound;
       omega].
  solve_by_inversion.
Qed.

Lemma no_msg_in_initial_st :
  forall src dst msg,
    ~ In (src, (dst, msg)) (msgs initial_st).
Proof.
  intros.
  rewrite msgs_initial_st_empty.
  apply in_nil.
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
    pose proof msgs_initial_st_empty.
    repeat find_rewrite; find_apply_lem_hyp app_eq_nil; break_and.
    discriminate.
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
