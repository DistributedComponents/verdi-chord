Require Import Arith.
Require FunctionalExtensionality.
Require Import List.
Import List.ListNotations.

Require Import mathcomp.ssreflect.ssreflect.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Verdi.Coqlib.
Require Import Verdi.DynamicNet.

Require Chord.Chord.
Import Chord.Chord.Chord.
Import Chord.ChordIDSpace.
Require Import Chord.ChordLocalProps.
Require Import Chord.ChordDefinitionLemmas.
Require Chord.ChordSemantics.
Import Chord.ChordSemantics.ConstrainedChord.
Import Chord.ChordSemantics.ChordSemantics.

Set Bullet Behavior "Strict Subproofs".

Close Scope boolean_if_scope.
Open Scope general_if_scope.
Open Scope string_scope.

Definition timeouts_detect_failure (gst : global_state) : Prop :=
  forall xs t ys h dead req,
    (trace gst) = xs ++ t :: ys ->
    (* if a request timeout occurs at some point in the trace... *)
    t = (e_timeout h (Request dead req)) ->
    (* then it corresponds to an earlier node failure. *)
    In (e_fail dead) xs.

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

Lemma only_safe_request_is_Ping :
  forall msg,
    request_payload msg ->
    is_safe msg = true ->
    msg = Ping.
Proof using.
  intuition.
  request_payload_inversion;
    find_apply_lem_hyp safe_msgs;
    break_or_hyp;
    auto || discriminate.
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

Lemma real_requests_get_busy_response :
  forall src dst msg st st' sends nts cts,
    request_payload msg ->
    cur_request st <> None ->
    msg <> Ping ->
    recv_handler src dst st msg = (st', sends, nts, cts) ->
    In (src, Busy) sends.
Proof.
  intros.
  find_apply_lem_hyp recv_handler_definition_existential; expand_def.
  apply in_or_app; right.
  find_apply_lem_hyp handle_msg_definition; expand_def.
  - match goal with
    | [H: request_payload _ |- _] => inv H
    end.
  - eapply handle_query_req_busy_sends_busy; eauto.
  - find_apply_lem_hyp is_request_same_as_request_payload; congruence.
  - find_apply_lem_hyp is_request_same_as_request_payload; congruence.
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

Ltac inv_prop P :=
  match goal with
  | [ H : context[P] |- _] =>
    inv H
  end.

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

Fixpoint fake_name (k : nat) :=
  match k with
  | 0 => ":^)"
  | S k' => String.append ":^) " (fake_name k')
  end.

Lemma fake_name_inj :
  forall i j,
    fake_name i = fake_name j ->
    i = j.
Proof.
  intro i.
  induction i; intros; destruct j;
    simpl in *; try congruence.
  find_injection; auto.
Qed.

Fixpoint make_initial_nodes (num_nodes : nat) : list addr :=
  match num_nodes with
  | 0 => []
  | S k => fake_name k :: make_initial_nodes k
  end.

Lemma in_make_initial_nodes :
  forall k nm,
    In nm (make_initial_nodes k) ->
    exists j,
      Nat.lt j k /\
      nm = fake_name j.
Proof.
  induction k.
  - intros; solve_by_inversion.
  - intros.
    destruct (addr_eq_dec nm (fake_name k)).
    + exists k; eauto.
    + inv_prop In; try congruence.
      find_apply_lem_hyp IHk; break_exists_exists; break_and.
      auto with arith.
Qed.

Lemma make_initial_nodes_NoDup :
  forall k,
    NoDup (make_initial_nodes k).
Proof.
  induction k.
  - constructor.
  - simpl.
    constructor; auto.
    intro.
    find_eapply_lem_hyp in_make_initial_nodes; break_exists; break_and.
    find_apply_lem_hyp fake_name_inj.
    solve_by_inversion.
Qed.

Lemma make_initial_nodes_length :
  forall k,
    length (make_initial_nodes k) = k.
Proof.
  induction k.
  - easy.
  - simpl; now f_equal.
Qed.

Definition initial_nodes : list addr :=
  make_initial_nodes (Chord.SUCC_LIST_LEN + 1).

Lemma initial_nodes_NoDup : NoDup initial_nodes.
Proof.
  apply make_initial_nodes_NoDup.
Qed.

Lemma initial_nodes_length : length initial_nodes = Chord.SUCC_LIST_LEN + 1.
Proof.
  apply make_initial_nodes_length.
Qed.

Definition run_init_for (gst : global_state) (h : addr) : global_state :=
  let res := start_handler h initial_nodes in
  apply_handler_result h (res, []) [] gst.
Hint Unfold run_init_for.

Definition initial_st : global_state :=
  fold_left run_init_for initial_nodes
            {| nodes := initial_nodes;
               failed_nodes := [];
               timeouts := fun h => [];
               sigma := fun h => None;
               msgs := [];
               trace := [] |}.

Inductive reachable_st : global_state -> Prop :=
| reachableInit : reachable_st initial_st
| reachableStep : forall gst gst',
    reachable_st gst ->
    step_dynamic gst gst' ->
    reachable_st gst'.

Ltac induct_reachable_st :=
  match goal with
  | [H : reachable_st _ |- _ ] => prep_induction H; induction H
  end.

Inductive intermediate_reachable_st : global_state -> Prop :=
| intReachableInit :
    intermediate_reachable_st initial_st
| intReachableStep :
    forall gst gst',
      intermediate_reachable_st gst ->
      step_dynamic gst gst' ->
      intermediate_reachable_st gst'
| intReachableDelayedQueries :
    forall gst h d res,
      In h (nodes gst) ->
      ~ In h (failed_nodes gst) ->
      sigma gst h = Some d ->
      do_delayed_queries h d = res ->
      intermediate_reachable_st (apply_handler_result h res [] gst).

Ltac induct_int_reachable_st :=
  match goal with
  | [H : intermediate_reachable_st _ |- _ ] => prep_induction H; induction H
  end.

Ltac induct type :=
  match goal with
  | [H : type _ |- _ ] => prep_induction H; induction H
  end.

Lemma reachable_intermediate_reachable :
  forall gst,
    reachable_st gst ->
    intermediate_reachable_st gst.
Proof using.
  intros.
  induct_reachable_st; econstructor; eauto.
Qed.

Theorem live_node_characterization :
  forall gst h st,
    sigma gst h = Some st ->
    joined st = true ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    live_node gst h.
Proof using.
  unfold live_node.
  intuition.
  match goal with
  | x : data |- exists _ : data, _ => exists x
  end.
  intuition.
Qed.

Definition live_node_bool (gst : global_state) (h : addr) :=
  match sigma gst h with
  | Some st =>
    if joined st
    then if in_dec addr_eq_dec h (nodes gst)
         then if in_dec addr_eq_dec h (failed_nodes gst)
              then false
              else true
         else false
    else false
  | None => false
  end.

Ltac break_live_node :=
  match goal with
  | H : live_node _ _ |- _ =>
    unfold live_node in H; repeat break_and; break_exists; repeat break_and
  end.

Ltac break_live_node_name var :=
  match goal with
  | H : live_node _ _ |- _ =>
    unfold live_node in H; repeat break_and; break_exists_name var; repeat break_and
  end.

Ltac break_live_node_exists_exists :=
  match goal with
  | H : live_node _ _ |- _ =>
    unfold live_node in H; repeat break_and; break_exists_exists; repeat break_and
  end.

Ltac break_dead_node :=
  match goal with
  | H : dead_node _ _ |- _ =>
    unfold dead_node in H; repeat break_and; break_exists; repeat break_and
  end.

Ltac break_dead_node_name var :=
  match goal with
  | H : dead_node _ _ |- _ =>
    unfold dead_node in H; repeat break_and; break_exists_name var; repeat break_and
  end.

Ltac break_dead_node_exists_exists :=
  match goal with
  | H : dead_node _ _ |- _ =>
    unfold dead_node in H; repeat break_and; break_exists_exists; repeat break_and
  end.

Definition live_node_dec (gst : global_state) :
  forall h,
    {live_node gst h} + {~ live_node gst h}.
Proof using.
  move => h.
  destruct (sigma gst h) as [st |] eqn:H_st.
  - destruct (joined st) eqn:H_joined;
      destruct (In_dec addr_eq_dec h (nodes gst));
      destruct (In_dec addr_eq_dec h (failed_nodes gst));
      try (right; move => H_live; break_live_node; easy || congruence).
    left; eapply live_node_characterization; eauto.
  - right.
    move => H_live.
    break_live_node.
    congruence.
Defined.

Theorem live_node_dec_equiv_live_node :
  forall gst h,
    live_node gst h <-> live_node_bool gst h = true.
Proof using.
  unfold live_node_bool.
  intuition.
  - repeat break_match;
      break_live_node;
      congruence || auto.
  - repeat break_match;
      congruence || eauto using live_node_characterization.
Qed.

Theorem having_st_means_node :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    In h (nodes gst).
Proof.
Admitted.

Theorem nodes_have_st :
  forall gst h,
    reachable_st gst ->
    In h (nodes gst) ->
    exists st,
      sigma gst h = Some st.
Proof.
Admitted.

(* transitive closure of best_succ *)
(* treat as opaque *)
Inductive reachable (gst : global_state) : addr -> addr -> Prop :=
| ReachableSucc : forall from to,
    best_succ gst from to ->
    reachable gst from to
| ReachableTransL : forall from x to,
    best_succ gst from x ->
    reachable gst x to ->
    reachable gst from to.

Ltac induct_reachable :=
  match goal with
  | H : reachable _ _ _ |- _ =>
    induction H
  end.

Lemma ReachableTransR : forall gst from x to,
    reachable gst from x ->
    best_succ gst x to ->
    reachable gst from to.
Proof using.
  intuition.
  induct_reachable.
  - eapply ReachableTransL.
    eauto.
    eapply ReachableSucc.
    eauto.
  - eauto using ReachableTransL.
Qed.

Lemma ReachableTrans : forall gst from x to,
    reachable gst from x ->
    reachable gst x to ->
    reachable gst from to.
Proof using.
  intros gst from x to H.
  generalize dependent to.
  induction H.
  - intuition.
    eauto using ReachableSucc, ReachableTransL.
  - intuition.
    eauto using ReachableSucc, ReachableTransL.
Qed.

Definition best_succ_of (gst : global_state) (h : addr) : option addr :=
  match (sigma gst) h with
  | Some st => head (filter (live_node_bool gst) (map addr_of (succ_list st)))
  | None => None
  end.

(* treat as opaque *)
Definition ring_member (gst : global_state) (h : addr) : Prop :=
  reachable gst h h.
Hint Unfold ring_member.

Definition at_least_one_ring (gst : global_state) : Prop :=
  exists h, ring_member gst h.

Definition at_most_one_ring (gst : global_state) : Prop :=
  forall x y,
    ring_member gst x ->
    ring_member gst y ->
    reachable gst x y.

Definition ordered_ring (gst : global_state) : Prop :=
  forall h s x,
    ring_member gst (addr_of h) ->
    best_succ gst (addr_of h) (addr_of s) ->
    ring_member gst (addr_of x) ->
    ~ between (id_of h) (id_of x) (id_of s).

Definition connected_appendages (gst : global_state) : Prop :=
  forall a, live_node gst a ->
       exists r, ring_member gst r /\ reachable gst a r.

Definition state_invariant (gst : global_state) : Prop :=
  sufficient_principals gst /\
  live_node_in_succ_lists gst.

(* this is not quite what it sounds like, since Chord.start_query will sometimes not send anything *)
Inductive query_request : query -> payload -> Prop :=
| QReq_RectifyPing : forall n, query_request (Rectify n) Ping
| QReq_StabilizeGetPredAndSuccs : query_request Stabilize GetPredAndSuccs
| QReq_Stabilize2 : forall p, query_request (Stabilize2 p) GetSuccList
| QReq_JoinGetBestPredecessor : forall k a, query_request (Join k) (GetBestPredecessor a)
| QReq_JoinGetSuccList : forall k, query_request (Join k) GetSuccList
| QReq_Join2 : forall n, query_request (Join2 n) GetSuccList.

Inductive query_response : query -> payload -> Prop :=
| QRes_RectifyPong : forall n, query_response (Rectify n) Pong
| QRes_StabilizeGetPredAndSuccs : forall p l, query_response Stabilize (GotPredAndSuccs p l)
| QRes_Stabilize2 : forall p l, query_response (Stabilize2 p) (GotSuccList l)
| QRes_JoinGotBestPredecessor : forall k p, query_response (Join k) (GotBestPredecessor p)
| QRes_JoinGotSuccList : forall k l, query_response (Join k) (GotSuccList l)
| QRes_Join2 : forall n l, query_response (Join2 n) (GotSuccList l).

(* for all nodes, query = none -> no request or response in the network for node *)
(* for all nodes, query = some -> exactly one corresponding req or res in net *)
Definition request_for_query (gst : global_state) (src dst : addr) (q : query) (msg : payload) : Prop :=
  query_request q msg /\
  In (src, (dst, msg)) (msgs gst).

Definition response_for_query (gst : global_state) (src dst : addr) (q : query) (msg : payload) : Prop :=
  query_response q msg /\
  In (dst, (src, msg)) (msgs gst).

Definition query_delayed_at (dst : addr) (st : data) (src : addr) (msg : payload) : Prop :=
  In (src, msg) (delayed_queries st).

Definition addr_eqb (a b : addr) : bool :=
  Coqlib.proj_sumbool (addr_eq_dec a b).

Lemma addr_eqb_true :
  forall a b,
    addr_eqb a b = true ->
    a = b.
Proof using.
  unfold addr_eqb.
  intros.
  now find_eapply_lem_hyp Coqlib.proj_sumbool_true.
Qed.

Lemma addr_eqb_false :
  forall a b,
    addr_eqb a b = false ->
    a <> b.
Proof using.
  intros.
  intuition.
  find_apply_lem_hyp (Coqlib.proj_sumbool_is_true (addr_eq_dec a b)).
  unfold addr_eqb in *.
  destruct (addr_eqb a b);
    congruence.
Qed.

Lemma addr_eqb_refl :
  forall a,
    addr_eqb a a = true.
Proof using.
  unfold addr_eqb.
  intros.
  now apply (Coqlib.proj_sumbool_is_true (addr_eq_dec a a)).
Qed.

Definition on_channel (src dst : addr) (t : addr * (addr * payload)) :=
  let '(s, (d, m)) := t in
  andb (addr_eqb src s) (addr_eqb dst d).

Definition channel (gst : global_state) (src dst : addr) : list payload :=
  filterMap
    (fun m =>
       if andb (addr_eqb (fst m) src)
               (addr_eqb (fst (snd m)) dst)
       then Some (snd (snd m))
       else None)
    (msgs gst).

(* note: this doesn't really tell you anything about repeated messages *)
Lemma channel_contents :
  forall gst src dst p,
    In (src, (dst, p)) (msgs gst) <-> In p (channel gst src dst).
Proof using.
  unfold channel.
  intuition.
  - eapply filterMap_In; eauto.
    now repeat rewrite addr_eqb_refl.
  - find_eapply_lem_hyp In_filterMap; eauto.
    break_exists.
    break_and.
    assert (x = (src, (dst, p))).
    { break_if; try discriminate.
      find_apply_lem_hyp Bool.andb_true_iff; break_and.
      repeat find_apply_lem_hyp addr_eqb_true.
      find_injection.
      now repeat apply injective_projections. }
    now find_reverse_rewrite.
Qed.

(* If we have an open query at a live node, we have one of the following:
     - an appropriate request from src to dst
       and no other requests from src to dst
       and no responses from dst to src
       and no pending queries from src in the local state of dst
     - an appropriate response from dst to src
       and no requests from src to dst
       and no other responses from dst to src
       and no pending queries from src in the local state of dst
     - a corresponding pending query from src in the local state of dst
       and no requests from src to dst
       and no responses from dst to src *)
Definition request_in_transit (gst : global_state) (src dst : addr) (q : query) : Prop :=
  forall chan,
    chan = channel gst src dst ->
    exists req,
      query_request q req /\
      In req chan /\
      (* no other requests *)
      (forall m xs ys,
          chan = xs ++ req :: ys ->
          In m (xs ++ ys) ->
          request_payload m ->
          m = req) /\
      (* no responses *)
      (forall m,
          In m (channel gst dst src) ->
          ~ response_payload m) /\
      (forall m st,
          sigma gst dst = Some st ->
          ~ query_delayed_at dst st src m).

Definition response_in_transit (gst : global_state) (src dst : addr) (q : query) : Prop :=
  forall chan,
    chan = channel gst dst src ->
    exists res,
      query_response q res /\
      In res chan /\
      (* no other responses *)
      (forall m xs ys,
          chan = xs ++ res :: ys ->
          In m (xs ++ ys) ->
          response_payload m ->
          m = res) /\
      (* no requests *)
      (forall m,
          In m (channel gst src dst) ->
          ~ request_payload m) /\
      (forall m st,
          sigma gst dst = Some st ->
          ~ query_delayed_at dst st src m).

Definition pending_query (gst : global_state) (src dst : addr) (q : query) : Prop :=
  (forall st,
      exists m,
        sigma gst src = Some st ->
        query_delayed_at dst st src m) /\
  (forall m,
      In m (channel gst src dst) ->
      ~ request_payload m) /\
  (forall m,
      In m (channel gst dst src) ->
      ~ response_payload m).

Theorem queries_always_remote :
  forall gst,
    reachable_st gst ->
    forall h st dstp q p,
      sigma gst h = Some st ->
      cur_request st = Some (dstp, q, p) ->
      h <> (addr_of dstp).
Admitted.

Definition query_state_net_invariant (gst : global_state) : Prop :=
  forall src st dstp q m,
    In src (nodes gst) ->
    sigma gst src = Some st ->
    cur_request st = Some (dstp, q, m) ->
    src <> (addr_of dstp) /\
    (request_in_transit gst src (addr_of dstp) q \/
     response_in_transit gst src (addr_of dstp) q \/
     pending_query gst src (addr_of dstp) q).

Lemma query_state_net_invariant_elim :
  forall gst,
    query_state_net_invariant gst ->
    forall src dstp q st m,
      In src (nodes gst) ->
      sigma gst src = Some st ->
      cur_request st = Some (dstp, q, m) ->
      src <> (addr_of dstp) /\
      (request_in_transit gst src (addr_of dstp) q \/
       response_in_transit gst src (addr_of dstp) q \/
       pending_query gst src (addr_of dstp) q).
Proof using.
  eauto.
Qed.

Definition query_set_for_request (st : data) (dst : addr) (r : payload) :=
  exists q remove,
    cur_request st = Some (make_pointer dst, q, remove) /\
    query_request q r.

Definition request_timed_out (gst : global_state) (src dst : addr) (r : payload) :=
  forall req_event,
    req_event = e_send (dst, (src, r)) ->
    exists before since,
      trace gst = before ++ req_event :: since /\
      ~ In req_event since /\
      In (e_timeout src (Request dst r)) since.

Definition requests_have_queries_or_timeouts (gst : global_state) : Prop :=
  forall src dst r st,
    request_payload r ->
    In (dst, (src, r)) (msgs gst) ->
    sigma gst src = Some st ->
    query_set_for_request st dst r \/ request_timed_out gst src dst r.

Definition timeouts_match_msg (gst : global_state) : Prop :=
  forall src dst m,
    In (Request dst m) (timeouts gst src) ->
    In src (nodes gst) ->
    In (src, (dst, m)) (msgs gst) \/
    exists p,
      request_response_pair m p /\
      In (dst, (src, p)) (msgs gst).

Definition timeouts_match_query (gst : global_state) : Prop :=
  forall src dst st m p,
    In (Request dst m) (timeouts gst src) ->
    In src (nodes gst) ->
    sigma gst src = Some st ->
    addr_of p = dst ->
    exists q,
      cur_request st = Some (p, q, m) /\
      query_request q m.

Definition responses_have_queries (gst : global_state) : Prop :=
  forall src dst r st,
    sigma gst src = Some st ->
    response_payload r ->
    In (src, (dst, r)) (msgs gst) ->
    exists q m,
      query_request q r /\
      cur_request st = Some (make_pointer dst, q, m).

(* should follow from invariant *)
Definition Request_goes_to_real_node (gst : global_state) : Prop :=
  forall src dst p,
    In (Request dst p) (timeouts gst src) ->
    In dst (nodes gst).

Definition network_invariant (gst : global_state) : Prop :=
  True.

Definition live_nodes_have_state (gst : global_state) : Prop :=
  forall h,
    In h (nodes gst) ->
    exists st,
      sigma gst h = Some st.

Theorem nodes_have_state :
  forall gst gst',
    live_nodes_have_state gst ->
    step_dynamic gst gst' ->
    live_nodes_have_state gst'.
Proof using.
  unfold live_nodes_have_state.
  move => gst gst' H_st H_step n H_in.
  break_step.
  - destruct (addr_eq_dec h n).
    + subst_max.
      apply update_for_start_sigma_h_exists.
    + find_rewrite_lem update_for_start_nodes_eq.
      find_apply_lem_hyp in_inv.
      break_or_hyp; try (exfalso; eauto; fail).
      find_apply_lem_hyp H_st.
      break_exists_exists.
      eapply update_for_start_sigma_h_n; eauto.
  - eauto.
  - destruct (addr_eq_dec h n).
    * eexists.
      now apply update_eq.
    * find_apply_lem_hyp H_st.
      break_exists_exists.
      find_reverse_rewrite.
      now apply update_diff.
  - (*simpl in *.*)
    destruct (addr_eq_dec (fst (snd m)) n).
    * eexists.
      now apply update_eq.
    * simpl.
      find_apply_lem_hyp H_st.
      break_exists_exists.
      repeat find_reverse_rewrite.
      now apply update_diff.
  - admit.
  - admit.
Admitted.

Theorem network_invariant_is_inductive :
  forall gst gst',
    network_invariant gst ->
    step_dynamic gst gst' ->
    network_invariant gst'.
Abort.

Definition inductive_invariant (gst : global_state) : Prop :=
  state_invariant gst /\
  network_invariant gst.

Ltac break_invariant :=
  match goal with
  | H : inductive_invariant _ |- _ =>
    unfold inductive_invariant, state_invariant, network_invariant in H; break_and
  end.

Lemma live_node_specificity :
  forall gst gst',
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst = sigma gst' ->
    live_node gst = live_node gst'.
Proof using.
  intuition.
  unfold live_node.
  repeat find_rewrite.
  auto.
Qed.

Lemma live_node_joined :
  forall gst h,
    live_node gst h ->
    exists st,
      sigma gst h = Some st /\
      joined st = true.
Proof using.
  intuition.
    by break_live_node_exists_exists.
Qed.

Lemma live_node_in_nodes :
  forall gst h,
    live_node gst h ->
    In h (nodes gst).
Proof using.
  intuition.
    by break_live_node.
Qed.

Lemma live_node_not_in_failed_nodes :
  forall gst h,
    live_node gst h ->
    ~ In h (failed_nodes gst).
Proof using.
  intuition.
    by break_live_node.
Qed.

Lemma live_node_equivalence :
  forall gst gst' h st st',
    live_node gst h ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    joined st = joined st' ->
    live_node gst' h.
Proof using.
  intuition.
  break_live_node.
  eapply live_node_characterization.
  * eauto.
  * repeat find_rewrite.
    find_injection.
    eauto.
  * repeat find_rewrite; auto.
  * repeat find_rewrite; auto.
Qed.

Lemma live_node_means_state_exists :
  forall gst h,
    live_node gst h ->
    exists st, sigma gst h = Some st.
Proof using.
  intuition.
  find_apply_lem_hyp live_node_joined.
  break_exists_exists.
    by break_and.
Qed.

Lemma coarse_live_node_characterization :
  forall gst gst' h,
    live_node gst h ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst = sigma gst' ->
    live_node gst' h.
Proof using.
  intuition.
  find_copy_apply_lem_hyp live_node_means_state_exists.
  break_exists.
  eapply live_node_equivalence.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
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

Lemma when_apply_handler_result_preserves_live_node :
  forall h h0 st st' gst gst' e ms cts nts,
    live_node gst h ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    joined st' = true ->
    gst' = apply_handler_result h0 (st', ms, cts, nts) e gst ->
    live_node gst' h.
Proof using.
  intuition.
  eapply live_node_characterization.
  - eauto.
  - break_live_node.
    repeat find_rewrite.
    find_inversion; eauto.
  - find_apply_lem_hyp apply_handler_result_preserves_nodes.
    find_inversion.
    break_live_node; auto.
  - find_apply_lem_hyp apply_handler_result_preserves_failed_nodes.
    find_inversion.
    break_live_node; auto.
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
  - find_rewrite; simpl; congruence.
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

Lemma joined_preserved_by_update_pred :
  forall st p st',
    st' = update_pred st p ->
    joined st = joined st'.
Proof using.
  unfold update_pred.
  intuition.
  find_rewrite; auto.
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
Admitted.

Lemma update_determined_by_f :
  forall A (f : addr -> A) x d d' y,
    y <> x ->
    update addr_eq_dec f x d y = d' ->
    f y = d'.
Proof using.
  intuition.
  symmetry.
  repeat find_reverse_rewrite.
  apply update_diff.
  now apply not_eq_sym.
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

Theorem live_node_preserved_by_recv_step :
  forall gst h src st msg gst' e st' ms nts cts,
    live_node gst h ->
    Some st = sigma gst h ->
    recv_handler src h st msg = (st', ms, nts, cts) ->
    gst' = apply_handler_result h (st', ms, nts, cts) e gst ->
    live_node gst' h.
Proof using.
  intuition.
  eapply when_apply_handler_result_preserves_live_node; eauto.
  - eauto using apply_handler_result_updates_sigma.
  - eapply joined_preserved_by_recv_handler.
    * eauto.
    * break_live_node.
      find_rewrite.
      find_injection.
      auto.
Qed.

Theorem live_node_preserved_by_timeout_step :
  forall gst h st st' t ms nts cts e gst',
    live_node gst h ->
    sigma gst h = Some st ->
    timeout_handler h st t = (st', ms, nts, cts) ->
    gst' = apply_handler_result h (st', ms, nts, t :: cts) e gst ->
    live_node gst' h.
Proof using.
  intuition.
  eapply when_apply_handler_result_preserves_live_node; eauto.
  - eauto using apply_handler_result_updates_sigma.
  - break_live_node.
    unfold timeout_handler, fst in *; break_let.
    repeat find_rewrite.
    find_apply_lem_hyp joined_preserved_by_timeout_handler_eff.
    repeat find_rewrite.
    find_injection.
    eauto.
Qed.

Lemma adding_nodes_does_not_affect_live_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n (Some st) ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    live_node gst h ->
    live_node gst' h.
Proof using.
  intuition.
  break_live_node_name d.
  repeat split.
  * repeat find_rewrite.
    now apply in_cons.
  * by find_rewrite.
  * exists d.
    split => //.
    repeat find_reverse_rewrite.
    find_rewrite.
    find_rewrite.
    apply update_diff.
    congruence.
Qed.

(* reverse of the above, with additional hypothesis that h <> n. *)
Lemma adding_nodes_did_not_affect_live_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n st ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    live_node gst' h ->
    h <> n ->
    live_node gst h.
Proof using.
  intuition.
  unfold live_node.
  break_live_node_name d.
  repeat split.
  * repeat find_rewrite.
    find_apply_lem_hyp in_inv.
    break_or_hyp; congruence.
  * repeat find_rewrite.
    auto.
  * exists d.
    split => //.
    repeat find_reverse_rewrite.
    find_rewrite.
    find_rewrite.
    find_rewrite.
    find_rewrite.
    symmetry.
    apply update_diff; auto.
Qed.

Lemma adding_nodes_does_not_affect_dead_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n st ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    dead_node gst h ->
    dead_node gst' h.
Proof using.
  intuition.
  break_dead_node_name d.
  repeat split.
  - find_rewrite.
    eauto using in_cons.
  - find_rewrite; auto.
  - exists d.
    repeat find_reverse_rewrite.
    find_rewrite.
    find_rewrite.
    eapply update_diff.
    congruence.
Qed.

Lemma adding_nodes_did_not_affect_dead_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    In h (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n st ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    dead_node gst' h ->
    dead_node gst h.
Proof using.
  intuition.
  break_dead_node_name d.
  unfold dead_node.
  repeat split.
  - find_rewrite.
    eauto using in_cons.
  - now repeat find_rewrite.
  - eexists.
    eapply update_determined_by_f.
    * instantiate (1 := n).
      eauto using In_notIn_implies_neq.
    * repeat find_rewrite; eauto.
Qed.

Lemma coarse_dead_node_characterization :
  forall gst gst' h,
    dead_node gst h ->
    sigma gst' = sigma gst ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    dead_node gst' h.
Proof using.
  intuition.
  break_dead_node_name d.
  repeat split; try (find_rewrite; auto).
  now exists d.
Qed.

Lemma coarse_best_succ_characterization :
  forall gst gst' h s,
    best_succ gst h s ->
    sigma gst' = sigma gst ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    best_succ gst' h s.
Proof using.
  unfold best_succ in *.
  intuition.
  break_exists_exists.
  break_and.
  repeat break_and_goal.
  - eapply live_node_equivalence; eauto.
    now repeat find_rewrite.
  - now repeat find_rewrite.
  - easy.
  - move => o H_in.
    find_apply_hyp_hyp.
    eapply coarse_dead_node_characterization; eauto.
  - eapply coarse_live_node_characterization; eauto.
Qed.

Lemma adding_nodes_does_not_affect_best_succ :
  forall gst gst' h s n st,
    best_succ gst h s ->
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n (Some st) ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    best_succ gst' h s.
Proof using.
  unfold best_succ.
  intuition.
  break_exists_exists.
  break_and.
  repeat break_and_goal;
    eauto using adding_nodes_does_not_affect_live_node.
  - repeat break_live_node.
    repeat find_rewrite.
    match goal with
    | H: sigma gst h = Some _ |- _ = Some _ => rewrite <- H
    end.
    eapply update_diff.
    congruence.
  - intuition.
    find_copy_apply_hyp_hyp.
    break_dead_node.
    eauto using adding_nodes_does_not_affect_dead_node.
Qed.

Lemma in_half_means_in_whole :
  forall A (x : A) (xs ys : list A),
    In x xs -> In x (xs ++ ys).
Proof using.
  intuition.
Qed.

Lemma in_middle_means_in_whole :
  forall A (x : A) (xs ys : list A),
    In x (xs ++ x :: ys).
Proof using.
  intuition.
Qed.

Lemma adding_nodes_did_not_affect_best_succ :
  forall gst gst' h s n st,
    best_succ gst' h s ->
    In h (nodes gst) ->
    ~ In n (nodes gst) ->
    sigma gst' h = Some st ->
    ~ In n (map addr_of (succ_list st)) ->
    sigma gst' = update addr_eq_dec (sigma gst) n (Some st) ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    best_succ gst h s.
Proof using.
  intuition.
  unfold best_succ in *.
  break_exists_exists.
  break_and.
  repeat break_and_goal.
  - break_live_node.
    break_live_node.
    unfold live_node.
    repeat find_rewrite.
    repeat break_and_goal; eauto.
    eexists; split; eauto.
Admitted.
(*

      break_exists.
      break_and.
      match goal with
        | H : sigma gst' ?h = Some ?st |- exists _, sigma gst ?h = _ /\ _ => exists st
      end.
      repeat find_rewrite.
      repeat find_injection.
      repeat split.
      * match goal with
        | H: sigma _ = update _ _ _ (Some ?st) |- sigma _ _ = Some ?st => symmetry in H
        end.
        eapply update_determined_by_f.
        + eapply In_notIn_implies_neq; eauto.
        + eauto.
      * eauto.
      * eauto.
      * eauto.
    - repeat find_reverse_rewrite.
      eapply update_determined_by_f;
        [eapply In_notIn_implies_neq; now eauto|]; now repeat find_rewrite.
    - eauto.
    - intuition.
      eapply adding_nodes_did_not_affect_dead_node; eauto.
      find_copy_apply_hyp_hyp.
      unfold dead_node in *.
      break_exists.
      break_and.
      repeat find_rewrite.
      find_injection.
      eapply In_cons_neq.
      * eauto.
      * intuition; subst.
        find_false.
        repeat find_rewrite.
        auto using in_half_means_in_whole.
    - eapply adding_nodes_did_not_affect_live_node; eauto.
      * intuition; subst.
        find_false.
        repeat (find_rewrite; try find_injection).
        auto using in_middle_means_in_whole.
  Qed.
 *)
Lemma coarse_reachable_characterization :
  forall from to gst gst',
    reachable gst from to ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    sigma gst' = sigma gst ->
    reachable gst' from to.
Proof using.
  intuition.
  induction H;
    eauto using ReachableSucc, ReachableTransL, coarse_best_succ_characterization.
Qed.

Lemma adding_node_preserves_reachable :
  forall h from to gst gst' st,
    reachable gst from to ->
    ~ In h (nodes gst) ->
    nodes gst' = h :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st) ->
    reachable gst' from to.
Proof using.
  intuition.
  induction H;
    eauto using ReachableSucc, ReachableTransL, adding_nodes_does_not_affect_best_succ.
Qed.

Ltac break_best_succ :=
  match goal with
  | H : best_succ _ _ _ |- _ =>
    let x := fresh in
    pose proof H as x;
    unfold best_succ in x;
    break_exists;
    break_and
  end.

Lemma adding_node_preserves_reachable_converse :
  forall h from to gst gst' st,
    reachable gst' from to ->
    ~ In h (nodes gst) ->
    In from (nodes gst) ->
    nodes gst' = h :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    sigma gst' = update addr_eq_dec (sigma gst) h st ->
    reachable gst from to.
Admitted.

Definition fail_step_preserves (P : global_state -> Prop) : Prop :=
  forall gst gst' h,
    inductive_invariant gst ->
    In h (nodes gst) ->
    sigma gst' = sigma gst ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = h :: failed_nodes gst ->
    P gst'.

Definition timeout_step_preserves (P : global_state -> Prop) : Prop :=
  forall gst gst' h st t st' ms newts clearedts,
    inductive_invariant gst ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    In t (timeouts gst h) ->
    timeout_handler h st t = (st', ms, newts, clearedts) ->
    gst' = (apply_handler_result
              h
              (st', ms, newts, t :: clearedts)
              [e_timeout h t]
              gst) ->
    P gst'.

Definition preserved_when_nodes_and_sigma_preserved (P : global_state -> Prop) : Prop :=
  forall gst gst',
    inductive_invariant gst ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    sigma gst' = sigma gst ->
    P gst'.

Definition node_deliver_step_preserves (P : global_state -> Prop) : Prop :=
  forall gst xs m ys gst' h d st ms nts cts e,
    inductive_invariant gst ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some d ->
    h = fst (snd m) ->
    msgs gst = xs ++ m :: ys ->
    gst' = update_msgs gst (xs ++ ys) ->
    recv_handler (fst m) h d (snd (snd m)) = (st, ms, nts, cts) ->
    P (apply_handler_result h (st, ms, nts, cts) e gst').

Lemma In_timeouts_in :
  forall t st,
    In t (timeouts_in st) ->
    exists dst q m,
      cur_request st = Some (dst, q, m) /\
      t = Request (addr_of dst) m.
Proof using.
  unfold timeouts_in.
  intros.
  repeat break_match.
  repeat eexists; eauto.
  match type of H with
  | In _ _ => inv H
  end.
  eauto.
  exfalso; auto with *.
  exfalso; auto with *.
Qed.

Definition query_state_net_invariant_inductive :
  forall gst,
    reachable_st gst ->
    query_state_net_invariant gst.
Proof using.
  intros.
  induct_reachable_st.
  { admit. } (* have to define valid initial states *)
  assert (reachable_st gst') by eauto using reachableStep.
  pose proof (query_state_net_invariant_elim gst IHreachable_st).
  intros until 3.
  split.
  - eapply queries_always_remote; eauto.
  - break_step.
    + (* start case *)
      destruct (addr_eq_dec src h).
      * (* source of query is the joining node *)
        admit.
      * (* it's unrelated *)
        admit.
    + (* fail case *)
      admit.
    + (* timeout case *)
      admit.
    + (* receive case *)
      admit.
Admitted.

Definition chord_init_invariant (P : global_state -> Prop) :=
  P initial_st.

Definition chord_start_invariant (P : global_state -> Prop) : Prop :=
  forall h gst gst' res k,
    res = start_handler h [k] ->
    gst' = update_for_start gst h res ->
    P gst ->
    ~ In h (nodes gst) ->
    In k (nodes gst) ->
    ~ In k (failed_nodes gst) ->
    P gst'.

Definition chord_fail_invariant (P : global_state -> Prop) : Prop :=
  forall h gst gst',
    failure_constraint gst h gst' ->
    gst' = fail_node gst h ->
    P gst ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    P gst'.

Definition chord_tick_invariant (P : global_state -> Prop) : Prop :=
  forall gst gst' h st st' ms newts clearedts eff,
    In Tick (timeouts gst h) ->
    tick_handler h st = (st', ms, newts, clearedts, eff) ->
    P gst ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    gst' = apply_handler_result
             h
             (st', ms, newts, Tick :: clearedts)
             [e_timeout h Tick]
             gst ->
    timeout_constraint gst h Tick ->
    P gst'.

Definition chord_do_delayed_queries_invariant (P : global_state -> Prop) : Prop :=
  forall gst gst' h st,
    P gst ->
    sigma gst h = Some st ->
    gst' = apply_handler_result h (do_delayed_queries h st) [] gst ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    P gst'.

Definition chord_do_rectify_invariant (P : global_state -> Prop) : Prop :=
  forall gst gst' h st,
    P gst ->
    sigma gst h = Some st ->
    gst' = apply_handler_result h (fst (do_rectify h st)) [] gst ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    P gst'.

Definition chord_keepalive_invariant (P : global_state -> Prop) : Prop :=
  forall gst gst' h st st' ms newts clearedts eff,
    In KeepaliveTick (timeouts gst h) ->
    keepalive_handler st = (st', ms, newts, clearedts, eff) ->
    P gst ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    gst' = apply_handler_result
             h
             (st', ms, newts, KeepaliveTick :: clearedts)
             [e_timeout h KeepaliveTick]
             gst ->
    timeout_constraint gst h KeepaliveTick ->
    P gst'.

Definition chord_handle_msg_invariant (P : global_state -> Prop) : Prop :=
  forall gst gst' xs m ys h d res,
    handle_msg (fst m) h d (snd (snd m)) = res ->
    P gst ->
    msgs gst = xs ++ m :: ys ->
    h = fst (snd m) ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst') ->
    sigma gst h = Some d ->
    gst' = (apply_handler_result
              h
              res
              [e_recv m]
              (update_msgs gst (xs ++ ys))) ->
    P gst'.

Definition chord_request_invariant (P : global_state -> Prop) : Prop :=
  forall gst gst' h req dst t d st ms newts clearedts eff,
    reachable_st gst ->
    P gst ->
    request_timeout_handler h d dst req = (st, ms, newts, clearedts, eff) ->
    t = Request dst req ->
    sigma gst h = Some d ->
    gst' = apply_handler_result
             h
             (st, ms, newts, t :: clearedts)
             [e_timeout h t]
             gst ->
    timeout_constraint gst h t ->
    P gst'.

Definition chord_rectify_invariant (P : global_state -> Prop) :=
  forall gst h st st' ms newts clearedts eff,
    reachable_st gst ->
    P gst ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    In RectifyTick (timeouts gst h) ->
    do_rectify h st = (st', ms, newts, clearedts, eff) ->
    P (apply_handler_result h (st', ms, newts, RectifyTick :: clearedts)
                            [e_timeout h RectifyTick] gst).

Definition chord_input_invariant (P : global_state -> Prop) :=
  forall gst h i to m,
    reachable_st gst ->
    P gst ->
    client_addr h ->
    client_payload i ->
    m = send h (to, i) ->
    P (update_msgs_and_trace gst (m :: msgs gst) (e_send m)).

Definition chord_output_invariant (P : global_state -> Prop) :=
  forall gst h xs m ys,
    client_addr h ->
    msgs gst = xs ++ m :: ys ->
    h = fst (snd m) ->
    P (update_msgs_and_trace gst (xs ++ ys) (e_recv m)).

Lemma update_msgs_definition :
  forall gst gst' ms,
    gst' = update_msgs gst ms ->
    nodes gst = nodes gst' /\
    failed_nodes gst = failed_nodes gst' /\
    timeouts gst = timeouts gst' /\
    sigma gst = sigma gst' /\
    msgs gst' = ms /\
    trace gst = trace gst'.
Proof using.
  intros; subst; tauto.
Qed.

Lemma global_state_eq_ext :
  forall gst gst',
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    timeouts gst = timeouts gst' ->
    sigma gst = sigma gst' ->
    msgs gst = msgs gst' ->
    trace gst = trace gst' ->
    gst = gst'.
Proof using.
  intros.
  destruct gst, gst'.
  simpl in *.
  subst_max.
  tauto.
Qed.

Lemma app_eq_l :
  forall A (xs ys zs : list A),
    ys = zs ->
    xs ++ ys = xs ++ zs.
Proof using.
  intros.
  now find_rewrite.
Qed.

Lemma app_eq_r :
  forall A (xs ys zs : list A),
    xs = ys ->
    xs ++ zs = ys ++ zs.
Proof using.
  intros.
  now find_rewrite.
Qed.

Theorem chord_net_invariant :
  forall P net,
    chord_init_invariant P ->

    chord_start_invariant P ->
    chord_fail_invariant P ->
    chord_tick_invariant P ->
    chord_keepalive_invariant P ->
    chord_rectify_invariant P ->
    chord_request_invariant P ->
    chord_handle_msg_invariant P ->
    chord_do_delayed_queries_invariant P ->

    chord_input_invariant P ->
    chord_output_invariant P ->

    reachable_st net ->
    P net.
Proof using.
  intros.
  match goal with
  | [H : reachable_st net |- _] => induction H
  end.
  - eapply_prop chord_init_invariant.
  - break_step.
    + eapply_prop chord_start_invariant; eauto.
    + eapply_prop chord_fail_invariant; eauto.
    + unfold timeout_handler, fst in *; break_let.
      find_eapply_lem_hyp timeout_handler_eff_definition; expand_def.
      * eapply_prop chord_tick_invariant; eauto.
      * eapply_prop chord_keepalive_invariant; eauto.
      * eapply_prop chord_rectify_invariant; eauto.
      * eapply_prop chord_request_invariant; eauto.
    + unfold recv_handler in *.
      repeat break_let; subst_max.
      (* formulating intermediate states and proving they satisfy P *)
      match goal with
      | [ _ : context[handle_msg ?from ?to ?d ?p] |- _ ] =>
        remember (apply_handler_result
                    to
                    (handle_msg from to d p)
                    [e_recv m]
                    (update_msgs gst (xs ++ ys)))
          as gst0;
          assert (P gst0)
      end.
      { eapply_prop chord_handle_msg_invariant; eauto.
        * find_eapply_lem_hyp apply_handler_result_preserves_failed_nodes.
          now find_reverse_rewrite.
        * now repeat find_reverse_rewrite. }
      match goal with
      | [ _ : context[do_delayed_queries ?h ?st] |- _ ] =>
        remember (apply_handler_result h (do_delayed_queries h st) [] gst0) as gst1;
          assert (P gst1)
      end.
      { eapply_prop chord_do_delayed_queries_invariant; eauto.
        * repeat find_rewrite.
          eapply apply_handler_result_updates_sigma; eauto.
        * repeat find_eapply_lem_hyp apply_handler_result_preserves_nodes.
          now repeat find_reverse_rewrite.
        * repeat find_eapply_lem_hyp apply_handler_result_preserves_failed_nodes.
          now repeat find_reverse_rewrite. }

      (* proving the final intermediate state is gst *)
      match goal with
      | [ |- P ?gst ] => assert (gst = gst1)
      end.
      { apply global_state_eq_ext.
        * repeat find_eapply_lem_hyp apply_handler_result_preserves_nodes.
          now repeat find_reverse_rewrite.
        * repeat find_eapply_lem_hyp apply_handler_result_preserves_failed_nodes.
          now repeat find_reverse_rewrite.
        * repeat find_rewrite.
          tuple_inversion.
          apply FunctionalExtensionality.functional_extensionality => x.
          destruct (addr_eq_dec (fst (snd m)) x); subst; simpl.
          -- repeat rewrite update_same.
             repeat rewrite <- app_assoc.
             apply app_eq_l.
             repeat rewrite remove_all_app_r.
             repeat rewrite remove_all_app_l.
             repeat rewrite app_assoc.
             rewrite remove_all_del_comm.
             apply app_eq_l.
             reflexivity.
          -- now repeat rewrite update_diff.
        * repeat find_rewrite.
          simpl.
          repeat rewrite update_overwrite.
          now tuple_inversion.
        * repeat find_rewrite.
          simpl.
          tuple_inversion.
          repeat rewrite map_app.
          repeat (rewrite app_assoc; try reflexivity).
        * repeat find_rewrite.
          unfold apply_handler_result; simpl.
          repeat (break_let; simpl).
          now rewrite app_nil_r. }
      now repeat find_rewrite.
    + eapply_prop chord_input_invariant; eauto.
    + eapply_prop chord_output_invariant; eauto.
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
