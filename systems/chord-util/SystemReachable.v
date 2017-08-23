Require Import Arith.
Require FunctionalExtensionality.
Require Import List.
Import List.ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
Set Bullet Behavior "Strict Subproofs".

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.

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

Definition connected_appendages (gst : global_state) : Prop :=
  forall a, live_node gst a ->
       exists r, ring_member gst r /\ reachable gst a r.

Definition state_invariant (gst : global_state) : Prop :=
  sufficient_principals gst /\
  live_node_in_succ_lists gst.

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
Proof.
(*
This is difficult to prove because we need to know that we're never given our
own address as a successor by another node. It will require the full Zave
invariant. Once we have that it shouldn't be so bad.

DIFFICULTY: Ryan.
USED: In the proof of query_state_net_inductive below.
*)
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
(*
This seems important to prove but...

DIFFICULTY: Ryan
USED: nowhere at all!
*)
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
