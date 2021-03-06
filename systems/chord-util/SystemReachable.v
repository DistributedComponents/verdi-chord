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
| reachableInit :
    forall gst,
      initial_st gst ->
      reachable_st gst
| reachableStep :
    forall gst gst',
    reachable_st gst ->
    step_dynamic gst gst' ->
    reachable_st gst'.

Ltac induct_reachable_st :=
  match goal with
  | [H : reachable_st _ |- _ ] => prep_induction H; induction H
  end.

Inductive intermediate_reachable_st : global_state -> Prop :=
| intReachableInit :
    forall gst,
      initial_st gst ->
      intermediate_reachable_st gst
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
  induct_reachable_st; econstructor; now eauto.
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

Definition chord_init_invariant (P : global_state -> Prop) :=
  forall gst,
    initial_st gst ->
    P gst.
Hint Unfold chord_init_invariant.

Definition chord_start_pre_post (P Q : global_state -> Prop) : Prop :=
  forall h gst gst' k st ms nts,
    reachable_st gst ->
    step_dynamic gst gst' ->

    ~ In h (nodes gst) ->
    ~ client_addr h ->
    start_constraint gst h ->
    In k (nodes gst) ->
    ~ In k (failed_nodes gst) ->
    start_handler h [k] = (st, ms, nts) ->

    nodes gst' = h :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' = update addr_eq_dec (timeouts gst) h nts ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st) ->
    msgs gst' = map (send h) ms ++ msgs gst ->
    trace gst' = trace gst ++ map e_send (map (send h) ms) ->

    P gst ->
    Q gst'.
Hint Unfold chord_start_pre_post.

Definition chord_start_invariant (P : global_state -> Prop) : Prop :=
  chord_start_pre_post P P.
Hint Unfold chord_start_invariant.

Definition chord_fail_pre_post (P Q : global_state -> Prop) : Prop :=
  forall h gst gst',
    reachable_st gst ->
    step_dynamic gst gst' ->

    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    failure_constraint gst h gst' ->

    nodes gst' = nodes gst ->
    failed_nodes gst' = h :: failed_nodes  gst ->
    timeouts gst' = timeouts gst ->
    sigma gst' = sigma gst ->
    msgs gst' = msgs gst ->
    trace gst' = trace gst ->

    P gst ->
    Q gst'.
Hint Unfold chord_fail_pre_post.

Definition chord_fail_invariant (P : global_state -> Prop) : Prop :=
  chord_fail_pre_post P P.
Hint Unfold chord_fail_invariant.

Definition chord_tick_pre_post (P Q : global_state -> Prop) : Prop :=
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
    timeouts gst' = update addr_eq_dec (timeouts gst) h
                           (nts ++ remove_all timeout_eq_dec cts
                                (remove timeout_eq_dec Tick (timeouts gst h))) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = (map (send h) ms) ++ msgs gst ->
    trace gst' = trace gst ++ [e_timeout h Tick] ->

    P gst ->
    Q gst'.
Hint Unfold chord_tick_pre_post.

Definition chord_tick_invariant (P : global_state -> Prop) : Prop :=
  chord_tick_pre_post P P.
Hint Unfold chord_tick_invariant.

Definition chord_keepalive_pre_post (P Q : global_state -> Prop) : Prop :=
  forall gst gst' h st st' ms nts cts eff,
    reachable_st gst ->
    step_dynamic gst gst' ->

    In KeepaliveTick (timeouts gst h) ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    keepalive_handler st = (st', ms, nts, cts, eff) ->

    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' = update addr_eq_dec (timeouts gst) h
                           (nts ++ remove_all timeout_eq_dec cts
                                (remove timeout_eq_dec KeepaliveTick (timeouts gst h))) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = (map (send h) ms) ++ msgs gst ->
    trace gst' = trace gst ++ [e_timeout h KeepaliveTick] ->

    P gst ->
    Q gst'.
Hint Unfold chord_keepalive_pre_post.

Definition chord_keepalive_invariant (P : global_state -> Prop) : Prop :=
  chord_keepalive_pre_post P P.
Hint Unfold chord_keepalive_invariant.

Definition chord_rectify_pre_post (P Q : global_state -> Prop) :=
  forall gst gst' h st st' ms nts cts eff,
    reachable_st gst ->
    step_dynamic gst gst' ->

    In RectifyTick (timeouts gst h) ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    do_rectify h st = (st', ms, nts, cts, eff) ->

    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' = update addr_eq_dec (timeouts gst) h
                           (nts ++ remove_all timeout_eq_dec cts
                                (remove timeout_eq_dec RectifyTick (timeouts gst h))) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = (map (send h) ms) ++ msgs gst ->
    trace gst' = trace gst ++ [e_timeout h RectifyTick] ->

    P gst ->
    Q gst'.
Hint Unfold chord_rectify_pre_post.

Definition chord_rectify_invariant (P : global_state -> Prop) :=
  chord_rectify_pre_post P P.
Hint Unfold chord_rectify_invariant.

Definition chord_request_pre_post (P Q : global_state -> Prop) : Prop :=
  forall gst gst' h st st' ms nts cts eff t dst req,
    reachable_st gst ->
    step_dynamic gst gst' ->

    t = Request dst req ->
    timeout_constraint gst h t ->
    In t (timeouts gst h) ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    request_timeout_handler h st dst req = (st', ms, nts, cts, eff) ->

    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' = update addr_eq_dec (timeouts gst) h
                           (nts ++ remove_all timeout_eq_dec cts
                                (remove timeout_eq_dec t (timeouts gst h))) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = (map (send h) ms) ++ msgs gst ->
    trace gst' = trace gst ++ [e_timeout h t] ->

    P gst ->
    Q gst'.
Hint Unfold chord_request_pre_post.

Definition chord_request_invariant (P : global_state -> Prop) : Prop :=
  chord_request_pre_post P P.
Hint Unfold chord_request_invariant.

Definition chord_recv_handler_pre_post (P Q : global_state -> Prop) : Prop :=
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
    timeouts gst' = update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (timeouts gst h)) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = (map (send h) ms) ++ xs ++ ys ->
    trace gst' = trace gst ++ [e_recv (src, (h, p))] ->

    P gst ->
    Q gst'.
Hint Unfold chord_recv_handler_pre_post.

Definition chord_recv_handler_invariant (P : global_state -> Prop) : Prop :=
  chord_recv_handler_pre_post P P.
Hint Unfold chord_recv_handler_invariant.

Definition chord_input_pre_post (P Q : global_state -> Prop) :=
  forall gst gst' h i to m,
    reachable_st gst ->
    step_dynamic gst gst' ->

    gst' = update_msgs_and_trace gst (m :: msgs gst) (e_send m) ->
    client_addr h ->
    client_payload i ->
    m = send h (to, i) ->
    P gst ->
    Q gst'.
Hint Unfold chord_input_pre_post.

Definition chord_input_invariant (P : global_state -> Prop) :=
  chord_input_pre_post P P.
Hint Unfold chord_input_invariant.

Definition chord_output_pre_post (P Q : global_state -> Prop) :=
  forall gst gst' h xs m ys,
    reachable_st gst ->
    step_dynamic gst gst' ->

    gst' = update_msgs_and_trace gst (xs ++ ys) (e_recv m) ->
    client_addr h ->
    msgs gst = xs ++ m :: ys ->
    h = fst (snd m) ->
    P gst ->
    Q gst'.
Hint Unfold chord_output_pre_post.

Definition chord_output_invariant (P : global_state -> Prop) :=
  chord_output_pre_post P P.
Hint Unfold chord_output_invariant.

Theorem chord_net_invariant :
  forall P,
    chord_init_invariant P ->

    chord_start_invariant P ->
    chord_fail_invariant P ->

    chord_tick_invariant P ->
    chord_keepalive_invariant P ->
    chord_rectify_invariant P ->
    chord_request_invariant P ->

    chord_recv_handler_invariant P ->
    chord_input_invariant P ->
    chord_output_invariant P ->

    forall gst,
      reachable_st gst ->
      P gst.
Proof using.
  intros.
  match goal with
  | [H : reachable_st _ |- _] => induction H
  end.
  - now eapply_prop chord_init_invariant.
  - inv_prop step_dynamic; eauto.
    + destruct (start_handler _ _) as [[? ?] ?] eqn:?; eauto.
    + destruct t; unfold timeout_handler, timeout_handler_eff in *.
      * destruct (tick_handler _ _) as [[[? ?] ?] ?] eqn:?.
        simpl in *; tuple_inversion; eauto.
      * destruct (do_rectify _ _) as [[[? ?] ?] ?] eqn:?.
        simpl in *; tuple_inversion; eauto.
      * destruct (keepalive_handler _) as [[[? ?] ?] ?] eqn:?.
        simpl in *; tuple_inversion; eauto.
      * destruct (request_timeout_handler _ _ _ _) as [[[? ?] ?] ?] eqn:?.
        simpl in *; tuple_inversion; eauto.
    + destruct m as [? [? ?]]; eauto.
Qed.

Lemma chord_fail_pre_post_conj :
  forall Pre P Q,
    chord_fail_pre_post Pre P ->
    chord_fail_pre_post Pre Q ->
    chord_fail_pre_post Pre (fun gst => P gst /\ Q gst).
Proof.
  eauto.
Qed.
Hint Resolve chord_fail_pre_post_conj.

Lemma chord_fail_pre_post_weaken_l :
  forall Pre P Q,
    chord_fail_pre_post Pre (fun gst => P gst /\ Q gst) ->
    chord_fail_pre_post Pre P.
Proof.
  autounfold; intros.
  cut (P gst' /\ Q gst'); [tauto|eauto].
Qed.
Hint Resolve chord_fail_pre_post_weaken_l.

Lemma chord_fail_pre_post_weaken_r :
  forall Pre P Q,
    chord_fail_pre_post Pre (fun gst => P gst /\ Q gst) ->
    chord_fail_pre_post Pre Q.
Proof.
  autounfold; intros.
  cut (P gst' /\ Q gst'); [tauto|eauto].
Qed.
Hint Resolve chord_fail_pre_post_weaken_r.

Lemma chord_fail_pre_post_strengthen_l :
  forall P Q Post,
    chord_fail_pre_post P Post ->
    chord_fail_pre_post (fun gst => P gst /\ Q gst) Post.
Proof.
  autounfold; intros; intuition eauto.
Qed.
Hint Resolve chord_fail_pre_post_strengthen_l.

Lemma chord_fail_pre_post_strengthen_r :
  forall P Q Post,
    chord_fail_pre_post Q Post ->
    chord_fail_pre_post (fun gst => P gst /\ Q gst) Post.
Proof.
  autounfold; intros; intuition eauto.
Qed.
Hint Resolve chord_fail_pre_post_strengthen_r.

Lemma chord_start_pre_post_conj :
  forall Pre P Q,
    chord_start_pre_post Pre P ->
    chord_start_pre_post Pre Q ->
    chord_start_pre_post Pre (fun gst => P gst /\ Q gst).
Proof.
  eauto.
Qed.
Hint Resolve chord_start_pre_post_conj.

Lemma chord_start_pre_post_weaken_l :
  forall Pre P Q,
    chord_start_pre_post Pre (fun gst => P gst /\ Q gst) ->
    chord_start_pre_post Pre P.
Proof.
  autounfold; intros.
  cut (P gst' /\ Q gst'); [tauto|eauto].
Qed.
Hint Resolve chord_start_pre_post_weaken_l.

Lemma chord_start_pre_post_weaken_r :
  forall Pre P Q,
    chord_start_pre_post Pre (fun gst => P gst /\ Q gst) ->
    chord_start_pre_post Pre Q.
Proof.
  autounfold; intros.
  cut (P gst' /\ Q gst'); [tauto|eauto].
Qed.
Hint Resolve chord_start_pre_post_weaken_r.

Lemma chord_start_pre_post_strengthen_l :
  forall P Q Post,
    chord_start_pre_post P Post ->
    chord_start_pre_post (fun gst => P gst /\ Q gst) Post.
Proof.
  autounfold; intros; intuition eauto.
Qed.
Hint Resolve chord_start_pre_post_strengthen_l.

Lemma chord_start_pre_post_strengthen_r :
  forall P Q Post,
    chord_start_pre_post Q Post ->
    chord_start_pre_post (fun gst => P gst /\ Q gst) Post.
Proof.
  autounfold; intros; intuition eauto.
Qed.
Hint Resolve chord_start_pre_post_strengthen_r.

Lemma chord_init_invariant_weaken_l :
  forall P Q,
    chord_init_invariant (fun gst => P gst /\ Q gst) ->
    chord_init_invariant P.
Proof.
  simpl; autounfold; intros; find_apply_hyp_hyp; tauto.
Qed.
Hint Resolve chord_init_invariant_weaken_l.

Lemma chord_init_invariant_weaken_r :
  forall P Q,
    chord_init_invariant (fun gst => P gst /\ Q gst) ->
    chord_init_invariant Q.
Proof.
  simpl; autounfold; intros; find_apply_hyp_hyp; tauto.
Qed.
Hint Resolve chord_init_invariant_weaken_r.

Lemma recv_handler_post_conj :
  forall Pre P Q,
    chord_recv_handler_pre_post Pre P ->
    chord_recv_handler_pre_post Pre Q ->
    chord_recv_handler_pre_post Pre (fun gst => P gst /\ Q gst).
Proof.
  autounfold; eauto.
Qed.
Hint Resolve recv_handler_post_conj.

Lemma recv_handler_pre_strengthen_l :
  forall P Q Post,
    chord_recv_handler_pre_post P Post ->
    chord_recv_handler_pre_post (fun gst => P gst /\ Q gst) Post.
Proof.
  autounfold; intuition eauto.
Qed.
Hint Resolve recv_handler_pre_strengthen_l.

Lemma recv_handler_pre_strengthen_r :
  forall P Q Post,
    chord_recv_handler_pre_post P Post ->
    chord_recv_handler_pre_post (fun gst => Q gst /\ P gst) Post.
Proof.
  autounfold; intuition eauto.
Qed.
Hint Resolve recv_handler_pre_strengthen_r.
