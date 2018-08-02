Require Import List.
Import ListNotations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.
Require Import Chord.SuccessorNodesAlwaysValid.
Require Import Chord.PtrCorrectInvariant.

Set Bullet Behavior "Strict Subproofs".

Theorem stabilize2_param_matches :
  forall gst,
    reachable_st gst ->
    forall h s s' st p,
      sigma gst h = Some st ->
      cur_request st = Some (s, Stabilize2 s', p) ->
      s = s'.
Proof.
  induction 1; intros.
  - unfold initial_st in *.
    find_apply_lem_hyp sigma_initial_st_start_handler; eauto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; congruence.
  - inversion H0; subst; eauto.
    + subst. simpl in *.
      update_destruct; subst; rewrite_update; simpl in *; eauto.
      find_inversion. simpl in *. congruence.
    + simpl in *.
      update_destruct; subst; rewrite_update; simpl in *; eauto.
      repeat (handler_def || handler_simpl).
    + repeat (handler_def || handler_simpl;
              try (update_destruct; subst; rewrite_update);
              repeat find_rewrite;
              repeat find_inversion; simpl in *; eauto; try congruence).
Qed.

Theorem join2_unreachable :
  forall gst,
    reachable_st gst ->
    forall h st dstp j req,
      sigma gst h = Some st ->
      cur_request st = Some (dstp, Join2 j, req) ->
      False.
Proof.
  intros until 1.
  pattern gst.
  eapply chord_net_invariant; try assumption; clear H gst;
    do 2 autounfold; intros.
  - inv_prop initial_st; expand_def.
    destruct (In_dec addr_eq_dec h (nodes gst));
      [|find_apply_hyp_hyp; congruence].
    destruct (start_handler h (nodes gst)) as [[? ?] ?] eqn:?.
    copy_eapply_prop_hyp start_handler nodes; eauto; break_and.
    rewrite start_handler_init_state_preset in *;
      try (pose proof succ_list_len_lower_bound; omega).
    repeat (find_rewrite || find_injection).
    simpl in *; congruence.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      unfold start_handler in *; simpl in *; find_injection.
      simpl in *; congruence.
    + eauto.
  - repeat find_rewrite; eauto.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      repeat handler_def; simpl in *;
        solve [congruence
              |eauto
              |repeat find_rewrite; try find_injection; eauto].
    + eauto.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      repeat handler_def; simpl in *;
        solve [congruence
              |eauto
              |repeat find_rewrite; try find_injection; eauto].
    + eauto.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      repeat handler_def; simpl in *;
        solve [congruence
              |eauto
              |repeat find_rewrite; try find_injection; eauto].
    + eauto.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      repeat handler_def; simpl in *;
        solve [congruence
              |eauto
              |repeat find_rewrite; try find_injection; eauto].
    + eauto.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      repeat handler_def;
        simpl in *;
        try solve [congruence
                  |eauto].
    + eauto.
  - repeat find_rewrite; eauto.
  - repeat find_rewrite; eauto.
Qed.

Theorem join2_param_matches :
  forall gst,
    reachable_st gst ->
    forall dst h st ns p,
      sigma gst h = Some st ->
      cur_request st = Some (dst, Join2 ns, p) ->
      dst = ns.
Proof.
  intros; exfalso; eauto using join2_unreachable.
Qed.

Lemma sigma_some_in_nodes :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    In h (nodes gst).
Proof.
  intros.
  induct_reachable_st; intros.
  - unfold initial_st in *.
    intuition.
    destruct (in_dec addr_eq_dec h (nodes gst)); auto.
    eapply_prop_hyp In In. congruence.
  - invcs H0; simpl in *; eauto;
      update_destruct; subst; rewrite_update; simpl in *; eauto.
Qed.

Definition all_states (P : data -> Prop) (sigma : addr -> option data) : Prop :=
  forall h st,
    sigma h = Some st ->
    P st.
Local Hint Unfold all_states.

Definition all_msgs (P : addr -> addr -> payload -> Prop) (ms : list msg) :=
  forall src dst p,
    In (src, (dst, p)) ms ->
    P src dst p.
Local Hint Unfold all_msgs.

Definition all_succs_state (P : pointer -> Prop) (sigma : addr -> option data): Prop :=
  all_states (fun st => forall s, In s (succ_list st) -> P s) sigma.
Local Hint Unfold all_succs_state.

Definition all_succs_net (P : pointer -> Prop) (ms : list msg) : Prop :=
  all_msgs (fun src dst p =>
              forall succs s,
                succs_msg p succs ->
                In s succs ->
                P s)
           ms.
Local Hint Unfold all_succs_net.

Definition all_preds_state (P : pointer -> Prop) (sigma : addr -> option data): Prop :=
  all_states (fun st => forall p, pred st = Some p -> P p) sigma.
Local Hint Unfold all_preds_state.

Definition all_preds_net (P : pointer -> Prop) (ms : list msg) : Prop :=
  all_msgs (fun src dst p =>
              forall pred succs,
                p = GotPredAndSuccs (Some pred) succs ->
                P pred)
           ms.
Local Hint Unfold all_preds_net.

Definition all_self_ptr (P : pointer -> Prop) : (addr -> option data) -> Prop :=
  all_states (fun st => P (ptr st)).
Local Hint Unfold all_self_ptr.

Definition all_rectify_with (P : pointer -> Prop) (sigma : addr -> option data) : Prop :=
  all_states (fun st => forall rw, rectify_with st = Some rw -> P rw) sigma.
Local Hint Unfold all_rectify_with.

Definition all_cur_request (P : pointer -> query -> Prop) (sigma : addr -> option data) : Prop :=
  all_states (fun st => forall dstp q m,
                  cur_request st = Some (dstp, q, m) ->
                  P dstp q)
             sigma.
Local Hint Unfold all_cur_request.

Inductive query_ptr : query -> pointer -> Prop :=
| QPRectify : forall p, query_ptr (Rectify p) p
| QPStabilize2 : forall p, query_ptr (Stabilize2 p) p
| QPJoin : forall p, query_ptr (Join p) p
| QPJoin2 : forall p, query_ptr (Join2 p) p.
Local Hint Constructors query_ptr.

Definition all_query_ptr (P : pointer -> Prop) (sigma : addr -> option data) : Prop :=
  all_cur_request (fun _ q => forall p, query_ptr q p -> P p) sigma.
Local Hint Unfold all_query_ptr.

Definition all_lookup_results (P : pointer -> Prop) : list msg -> Prop :=
  all_msgs (fun _ _ p => forall res, p = GotBestPredecessor res -> P res).
Local Hint Unfold all_lookup_results.

Inductive all_ptrs P (gst : global_state) :=
| AllPtrs :
    all_succs_state P (sigma gst) ->
    all_succs_net P (msgs gst) ->
    all_preds_state P (sigma gst) ->
    all_preds_net P (msgs gst) ->
    all_rectify_with P (sigma gst) ->
    all_cur_request (fun p _ => P p) (sigma gst) ->
    all_query_ptr P (sigma gst) ->
    all_lookup_results P (msgs gst) ->
    all_self_ptr P (sigma gst) ->
    all_ptrs P gst.

Theorem all_msgs_app :
  forall P xs ys,
    all_msgs P xs ->
    all_msgs P ys ->
    all_msgs P (xs ++ ys).
Proof.
  autounfold; in_crush.
Qed.
Local Hint Resolve all_msgs_app.

Theorem all_msgs_split :
  forall P l m xs ys,
    l = xs ++ m :: ys ->
    all_msgs P l ->
    all_msgs P (xs ++ ys).
Proof.
  autounfold; in_crush.
Qed.
Local Hint Resolve all_msgs_split.

Theorem all_msgs_cons :
  forall (P : addr -> addr -> payload -> Prop) src dst p xs,
    P src dst p ->
    all_msgs P xs ->
    all_msgs P ((src, (dst, p)) :: xs).
Proof.
  autounfold; in_crush; congruence.
Qed.
Local Hint Resolve all_msgs_cons.

Theorem all_states_update :
  forall P h st' sigma,
    all_states P sigma ->
    P st' ->
    all_states P (update addr_eq_dec sigma h (Some st')).
Proof.
  autounfold.
  intros.
  destruct_update; rewrite_update.
  - congruence.
  - eauto.
Qed.
Local Hint Resolve all_states_update.

Lemma cons_make_succs :
  forall p succs,
    make_succs p succs = p :: firstn (SUCC_LIST_LEN - 1) succs.
Proof.
  pose proof succ_list_len_lower_bound.
  unfold make_succs, chop_succs.
  intros; simpl.
  destruct SUCC_LIST_LEN; try omega.
  simpl.
  replace (n - 0) with n by omega.
  auto.
Qed.

Local Hint Resolve make_pointer_wf.

Lemma recv_handler_succs_msg_accurate :
  forall src dst st p st' ms nts cts h m succs,
  recv_handler src dst st p = (st', ms, nts, cts) ->
  In (h, m) ms ->
  succs_msg m succs ->
  succs = succ_list st'.
Proof.
  intros; inv_prop succs_msg.
  - handler_def.
    find_apply_lem_hyp in_app_or; break_or_hyp.
    + find_eapply_lem_hyp handle_delayed_queries_GotSuccList_response_accurate; eauto.
    + handler_def;
      repeat match goal with
             | H: False |- _ => elim H
             | H: _ \/ _ |- _ => destruct H
             | H: (_, _) = (_, _) |- _ => injc H; try congruence
             | |- _ => progress simpl in *
             | |- _ => handler_def
             end;
      eapply handle_query_req_GotSuccList_response_accurate; eauto.
  - eapply recv_handler_GotPredAndSuccs_response_accurate; eauto.
Qed.

Lemma best_predecessor_in_succs_or_ptr :
  forall self succs x p,
    x = best_predecessor self succs p ->
    In x (self :: succs).
Proof.
  intros; subst.
  unfold best_predecessor, hd.
  break_match.
  in_crush.
  simpl; right.
  apply in_rev.
  eapply In_filter_In; eauto.
  in_crush.
Qed.

Lemma handle_query_req_GotBestPredecessor_in_succs_or_ptr :
  forall src st r h p pt succs,
    In (h, GotBestPredecessor r) (handle_query_req st src p) ->
    pt = ptr st ->
    succs = succ_list st ->
    r = pt \/ In r succs.
Proof.
  unfold handle_query_req.
  intros.
  subst.
  cut (In r (ptr st :: succ_list st)).
  { simpl; intuition congruence. }
  break_match; try solve [exfalso; subst; in_crush; congruence].
  eapply best_predecessor_in_succs_or_ptr.
  subst; in_crush.
  find_injection.
  eauto.
Qed.

Lemma recv_handler_lookup_response_in_succs :
  forall src dst st p st' ms nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    forall h p,
      In (h, GotBestPredecessor p) ms ->
      p = ptr st \/ In p (succ_list st').
Proof.
  intros.
  repeat handler_def
  || handler_simpl
  || (unfold handle_delayed_query in *)
  || in_crush
  || (try find_eapply_lem_hyp in_concat; expand_def).
  all:repeat break_match.
  all:try solve [eapply handle_query_req_GotBestPredecessor_in_succs_or_ptr; eauto].
  change (x8 = p0 \/ In p0 x11) with (In p0 (x8 :: x11)).
  eapply handle_query_req_GotBestPredecessor_in_succs_or_ptr; eauto.
Qed.

Theorem pointers_wf_recv :
  chord_recv_handler_invariant (all_ptrs wf_ptr).
Proof.
  do 2 autounfold_one.
  intros.
  inv_prop all_ptrs.
  (* We'll prove the state cases separately so we can use them in the message cases. *)
  assert (all_succs_state wf_ptr (update addr_eq_dec (sigma gst) h (Some st'))).
  {
    apply all_states_update; eauto; intros.
    repeat handler_def;
      try solve [repeat handler_simpl].
    - simpl in *; repeat find_rewrite || find_injection.
      rewrite cons_make_succs in *; in_crush.
      find_apply_lem_hyp in_firstn.
      find_eapply_prop all_succs_net; eauto; in_crush.
    - simpl in *; repeat find_rewrite || find_injection.
      rewrite cons_make_succs in *; in_crush.
      find_apply_lem_hyp in_firstn.
      find_eapply_prop all_succs_net; eauto; in_crush.
    - simpl in *; repeat find_rewrite || find_injection.
      rewrite cons_make_succs in *; in_crush.
      find_apply_lem_hyp in_firstn.
      find_eapply_prop all_succs_net; eauto; in_crush.
    - simpl in *; repeat find_rewrite || find_injection.
      rewrite cons_make_succs in *; in_crush.
      + find_eapply_prop all_query_ptr; eauto.
      + find_apply_lem_hyp in_firstn.
        find_eapply_prop all_succs_net; [in_crush| |]; eauto.
    - simpl in *; repeat find_rewrite || find_injection.
      find_eapply_prop all_succs_net; [in_crush| |]; eauto.
    - simpl in *; repeat find_rewrite || find_injection.
      rewrite cons_make_succs in *; in_crush.
      + find_eapply_prop all_query_ptr; eauto.
      + find_apply_lem_hyp in_firstn.
        find_eapply_prop all_succs_net; [in_crush| |]; eauto.
  }
  assert (all_preds_state wf_ptr (update addr_eq_dec (sigma gst) h (Some st'))).
  {
    apply all_states_update; eauto; intros.
    repeat handler_def || handler_simpl.
  }
  constructor;
    repeat match goal with
           | H: _ |- _ => rewrite H
           end.
  - assumption.
  - apply all_msgs_app; [|eauto using all_msgs_split].
    unfold send.
    autounfold_one; intros.
    find_apply_lem_hyp in_map_iff; expand_def.
    intros.
    find_eapply_lem_hyp recv_handler_succs_msg_accurate; eauto.
    subst.
    find_eapply_prop all_succs_state; rewrite_update; eauto.
  - assumption.
  - apply all_msgs_app; [|eauto using all_msgs_split].
    unfold send.
    autounfold_one; intros.
    find_apply_lem_hyp in_map_iff; expand_def.
    intros; subst.
    find_eapply_lem_hyp recv_handler_GotPredAndSuccs_response_accurate; eauto.
    find_eapply_prop all_preds_state; rewrite_update; intuition.
  - apply all_states_update; eauto; intros.
    repeat handler_def || handler_simpl.
  - apply all_states_update; eauto; intros.
    repeat handler_def; try solve [repeat handler_simpl].
    all:repeat find_rewrite || find_injection || simpl in *.
    + find_eapply_prop all_preds_net; in_crush.
    + find_eapply_prop all_lookup_results; in_crush.
    + find_eapply_prop all_lookup_results; in_crush.
  - apply all_states_update; eauto; intros.
    repeat match goal with
           | H: context[handle_query_res] |- _ => idtac
           | _ => handler_def
           end;
      match goal with
      | H: context[handle_query_res] |- _ => idtac
      | _ => repeat handler_simpl
      end.
    find_apply_lem_hyp cur_request_preserved_by_do_delayed_queries.
    repeat find_rewrite.
    repeat handler_def;
      try solve [repeat handler_simpl].
    repeat find_rewrite || find_injection || simpl in *.
    inv_prop query_ptr.
    find_eapply_prop all_preds_net; in_crush.
  - apply all_msgs_app; [|eauto using all_msgs_split].
    autounfold; intros.
    subst.
    unfold send in *; find_apply_lem_hyp in_map_iff; expand_def.
    find_eapply_lem_hyp recv_handler_lookup_response_in_succs; eauto.
    break_or_hyp; auto.
    + find_eapply_prop all_self_ptr; eauto.
    + find_eapply_prop all_succs_state; rewrite_update; eauto.
  - apply all_states_update; auto; intros.
    replace (ptr st') with (make_pointer h); eauto.
    symmetry; eapply ptr_correct;
      [eapply reachableStep; eauto
      |repeat find_rewrite; rewrite_update; auto].
Qed.

Lemma hd_error_in :
  forall X (l : list X) x,
    hd_error l = Some x ->
    In x l.
Proof.
  intros. unfold hd_error in *.
  break_match; try congruence.
  find_inversion. in_crush.
Qed.

Lemma pointers_wf_init :
  chord_init_invariant (all_ptrs wf_ptr).
Proof.
  autounfold_one. intuition.
  constructor.
  - do 2 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush.
    find_apply_lem_hyp in_firstn.
    match goal with
    | H : In ?s ?l, H' : ?l' = _ :: ?l |- _ => assert (In s l') by (repeat find_rewrite; in_crush)
    end. find_apply_lem_hyp in_sort_by_between. in_crush.
  - do 2 autounfold_one; simpl. intros.
    unfold initial_st in *. intuition. repeat find_rewrite. in_crush.
  - do 2 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush; try congruence.
    find_apply_lem_hyp hd_error_in.
    find_apply_lem_hyp in_rev.
    find_reverse_rewrite. find_apply_lem_hyp in_sort_by_between.
    in_crush.
  - do 2 autounfold_one; simpl. intros.
    unfold initial_st in *. intuition. repeat find_rewrite. in_crush.
  - do 2 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush; try congruence.
  - do 2 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush; try congruence.
    find_inversion.
    match goal with
    | _ : ?l = [?x] |- _ => assert (In x l) by (repeat find_rewrite; in_crush)
    end.
    find_apply_lem_hyp in_sort_by_between. in_crush.
  - do 3 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush; try congruence.
    find_inversion.
    inv_prop query_ptr.
    match goal with
    | _ : ?l = [?x] |- _ => assert (In x l) by (repeat find_rewrite; in_crush)
    end.
    find_apply_lem_hyp in_sort_by_between. in_crush.
  - do 2 autounfold_one; simpl. intros.
    unfold initial_st in *. intuition. repeat find_rewrite. in_crush.
  - do 2 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush; try congruence.
Qed.

Lemma pointers_wf_start :
  chord_start_invariant (all_ptrs wf_ptr).
Proof.
  do 2 autounfold_one.
  intuition.
  find_rewrite_lem start_handler_with_single_known.
  repeat (handler_def || handler_simpl).
  inv_prop all_ptrs.
  constructor; repeat find_rewrite.
  - apply all_states_update; eauto.
    intros.
    repeat handler_simpl; intuition.
  - apply all_msgs_cons; auto.
    intros. inv_prop succs_msg.
  - apply all_states_update; eauto.
    intros.
    repeat handler_simpl; intuition.
  - apply all_msgs_cons; auto.
    intros. congruence.
  - apply all_states_update; eauto.
    intros.
    repeat handler_simpl; intuition.
  - apply all_states_update; eauto.
    intros.
    repeat handler_simpl; intuition.
  - apply all_states_update; eauto.
    intros.
    repeat handler_simpl; intuition.
    inv_prop query_ptr; eauto.
  - apply all_msgs_cons; auto.
    intros. congruence.
  - apply all_states_update; eauto.
    intros.
    repeat handler_simpl; intuition.
Qed.

Lemma pointers_wf_tick:
  chord_tick_invariant (all_ptrs wf_ptr).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpl); intuition.
    find_apply_lem_hyp option_map_Some.
    break_exists; intuition. find_inversion.
    unfold send in *. find_inversion. inv_prop succs_msg.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpl); intuition.
    find_apply_lem_hyp option_map_Some.
    break_exists; intuition. find_inversion.
    unfold send in *. find_inversion.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
    find_apply_lem_hyp option_map_Some.
    break_exists. intuition. find_inversion.
    eauto using hd_error_in.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
    inv_prop query_ptr.
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpl); intuition.
    find_apply_lem_hyp option_map_Some.
    break_exists; intuition. find_inversion.
    unfold send in *. find_inversion.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
Qed.

Lemma pointers_wf_keepalive :
  chord_keepalive_invariant (all_ptrs wf_ptr).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpl); intuition.
    in_crush. unfold send_keepalives in *.
    in_crush. unfold send in *. find_inversion.
    inv_prop succs_msg.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpl); intuition.
    subst.
    in_crush. unfold send_keepalives in *.
    in_crush. unfold send in *. find_inversion.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpl); intuition.
    subst.
    in_crush. unfold send_keepalives in *.
    in_crush. unfold send in *. find_inversion.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
Qed.

Lemma pointers_wf_rectify :
  chord_rectify_invariant (all_ptrs wf_ptr).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpl); intuition.
    find_apply_lem_hyp option_map_Some. break_exists. intuition.
    find_inversion.
    unfold send in *. find_inversion.
    inv_prop succs_msg.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpl); intuition.
    find_apply_lem_hyp option_map_Some. break_exists. intuition.
    find_inversion.
    unfold send in *. find_inversion.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
    find_apply_lem_hyp option_map_Some. break_exists. intuition.
    find_inversion. eauto.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
    inv_prop query_ptr. eauto.
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpl); intuition.
    subst.
    find_apply_lem_hyp option_map_Some. break_exists. intuition.
    find_inversion.
    unfold send in *. find_inversion.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpl).
Qed.

Ltac handler_simpler :=
  discriminate ||
  solve [eauto] ||
  match goal with
  | H : In _ [] |- _ =>
    invcs H
  | H : In _ (concat _) |- _ =>
    apply in_concat in H; break_exists; intuition
  | H : In _ (handle_delayed_query _ _ _) |- _ =>
    unfold handle_delayed_query, handle_query_req in *
  | H : option_map _ _ = Some _ |- _ =>
    apply option_map_Some in H; break_exists
  | H : succs_msg _ _ |- _ =>
    invcs H
  | H : In ?x ?l, _ : ?l' = _ :: ?l, _ : In ?x ?l' |- _ =>
    idtac
  | H : In ?x ?l, _ : ?l' = _ :: ?l |- _ =>
    assert (In x l') by (repeat find_rewrite; in_crush)
  | H : hd_error _ = Some _ |- _ =>
    apply hd_error_in in H
  | H : ptr _ = ?x |- context [?x] =>
    symmetry in H; rewrite H
  | |- context [best_predecessor ?x ?l ?p] =>
    pose proof (best_predecessor_in_succs_or_ptr x l (best_predecessor x l p) p);
    in_crush
  end ||
  break_match ||
  in_crush ||
  handler_simpl.
                

Lemma pointers_wf_request :
  chord_request_invariant (all_ptrs wf_ptr).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpler).
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpler).
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpler).
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpler).
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpler).
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpler).
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpler).
  - apply all_msgs_app; eauto; intros; simpl in *.
    repeat (handler_def || handler_simpler).
  - apply all_states_update; eauto; intros.
    repeat (handler_def || handler_simpler).
Qed.

Lemma pointers_wf_input :
  chord_input_invariant (all_ptrs wf_ptr).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_ptrs.
  constructor; repeat find_rewrite; simpl in *; eauto.
  - apply all_msgs_cons; eauto. intros.
    inv_prop succs_msg; inv_prop client_payload.
  - apply all_msgs_cons; eauto. intros. subst.
    inv_prop client_payload.
  -  apply all_msgs_cons; eauto. intros. subst.
    inv_prop client_payload.
Qed.

Lemma pointers_wf_output :
  chord_output_invariant (all_ptrs wf_ptr).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_ptrs.
  constructor; repeat find_rewrite; simpl in *; eauto.
Qed.

Lemma pointers_wf_fail :
  chord_fail_invariant (all_ptrs wf_ptr).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_ptrs.
  constructor; repeat find_rewrite; simpl in *; eauto.
Qed.


Theorem pointers_wf :
  forall gst,
    reachable_st gst -> 
    all_ptrs wf_ptr gst.
Proof.
  intros until 1. pattern gst.
  eapply chord_net_invariant.
  (* TODO(doug) need more theorems for each case here *)
  all:(try exact pointers_wf_recv; try exact pointers_wf_init; try exact pointers_wf_start;
       try exact pointers_wf_fail; try exact pointers_wf_tick; try exact pointers_wf_rectify;
       try exact pointers_wf_keepalive; try exact pointers_wf_request;
       try exact pointers_wf_input; try exact pointers_wf_output); auto.
Qed.

Inductive query_joined_ptr : pointer -> query -> pointer -> Prop :=
| QJPRectifyH : forall h p, query_joined_ptr h (Rectify p) h
| QJPRectifyP : forall h p, query_joined_ptr h (Rectify p) p
| QPJStabilize : forall h, query_joined_ptr h Stabilize h
| QJPStabilize2H : forall h p, query_joined_ptr h (Stabilize2 p) h
| QJPStabilize2P : forall h p, query_joined_ptr h (Stabilize2 p) p
| QJPJoin2H : forall h p, query_joined_ptr h (Join2 p) h
| QJPJoin2P : forall h p, query_joined_ptr h (Join2 p) p.

Local Hint Constructors query_joined_ptr.

Definition all_joined_query_ptr (P : pointer -> Prop) (sigma : addr -> option data) : Prop :=
  all_cur_request (fun h q => forall p, query_joined_ptr h q p -> P p) sigma.

Local Hint Unfold all_joined_query_ptr.

Inductive joined_sender_msg : payload -> Prop :=
| JSMNotify : joined_sender_msg Notify
| JSMGotPredAndSuccs : forall p s, joined_sender_msg (GotPredAndSuccs p s)
(*| JSMGotSuccList : forall s, joined_sender_msg (GotSuccList s)*)
.

Local Hint Constructors joined_sender_msg.

Definition all_joined_senders_net (P : pointer -> Prop) ms :=
  all_msgs (fun src _ p => joined_sender_msg p -> (P (make_pointer src))) ms.

Local Hint Unfold all_joined_senders_net.

Inductive joined_receiver_msg : payload -> Prop :=
| JSRGetPredAndSuccs : joined_receiver_msg GetPredAndSuccs
(*| JSMGotSuccList : forall s, joined_sender_msg (GotSuccList s)*)
.

Local Hint Constructors joined_receiver_msg.
  
Definition all_joined_receivers_net (P : pointer -> Prop) ms :=
  all_msgs (fun _ dst p => joined_receiver_msg p -> (P (make_pointer dst))) ms.

Local Hint Unfold all_joined_receivers_net.

Definition all_joined_receivers_delayed_queries_state (P : pointer -> Prop) sigma :=
  all_states (fun st => forall h p, In (h, p) (delayed_queries st) -> joined_receiver_msg p -> P (ptr st))
             sigma.

Local Hint Unfold all_joined_receivers_delayed_queries_state.

Inductive joined_query : _query -> Prop :=
| JRStabilize : joined_query Stabilize
| JRStabilize2 : forall p, joined_query (Stabilize2 p).

Local Hint Constructors joined_query.

Definition all_joined_cur_request_state (P : pointer -> Prop) sigma :=
  all_states (fun st => forall dstp q m, cur_request st = Some (dstp, q, m) -> joined_query q -> P (ptr st))
             sigma.

Local Hint Unfold all_joined_cur_request_state.

Inductive all_joined_ptrs P (gst : global_state) :=
| AllJoinedPtrs :
    all_succs_state (P gst) (sigma gst) ->
    all_succs_net (P gst) (msgs gst) ->
    all_preds_state (P gst) (sigma gst) ->
    all_preds_net (P gst) (msgs gst) ->
    all_rectify_with (P gst) (sigma gst) ->
    all_joined_senders_net (P gst) (msgs gst) ->
    all_joined_receivers_net (P gst) (msgs gst) ->
    all_joined_receivers_delayed_queries_state (P gst) (sigma gst) ->
    all_joined_cur_request_state (P gst) (sigma gst) ->
    all_joined_query_ptr (P gst) (sigma gst) ->
    all_joined_ptrs P gst.
  
Definition pointer_joined gst p :=
  In (addr_of p) (nodes gst) /\
  exists st,
    sigma gst (addr_of p) = Some st /\
    joined st = true.

Lemma pointer_joined_stable :
  forall gst gst' p,
    reachable_st gst ->
    step_dynamic gst gst' ->
    pointer_joined gst p ->
    pointer_joined gst' p.
Proof.
  intros. unfold pointer_joined in *. inv_prop step_dynamic; intuition.
  - unfold update_for_start. simpl. intuition.
  - unfold update_for_start. simpl. update_destruct; subst; rewrite_update; intuition.
  - break_exists. intuition.
    find_apply_lem_hyp timeout_handler_definition.
    break_exists.
    find_apply_lem_hyp joined_preserved_by_timeout_handler_eff.
    unfold apply_handler_result. simpl.
    update_destruct; subst; rewrite_update; intuition eauto.
    eexists; intuition eauto. congruence.
  - break_exists. intuition.
    unfold apply_handler_result. simpl.
    update_destruct; subst; rewrite_update; intuition eauto.
    find_apply_lem_hyp joined_preserved_by_recv_handler; eauto.
    congruence.
Qed.

Lemma initial_st_joined :
  forall gst h,
    initial_st gst ->
    In h (nodes gst) ->
    pointer_joined gst (make_pointer h).
Proof.
  intros.
  find_copy_apply_lem_hyp in_nodes_sigma_some; auto.
  unfold pointer_joined. simpl. intuition.
  break_exists_exists. intuition.
  unfold initial_st in *. intuition.
  specialize (H8 h); intuition.
  destruct (start_handler h (nodes gst)) eqn:?.
  destruct p.
  pose proof succ_list_len_lower_bound.
  find_apply_lem_hyp initial_start_handler_st_joined; try omega.
  specialize (H10 d l0 l); intuition. repeat find_rewrite. congruence.
Qed.

Local Hint Resolve initial_st_joined.

Lemma pointer_joined_ptr_h :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    pointer_joined gst (ptr st) ->
    pointer_joined gst (make_pointer h).
Proof.
  intros. erewrite <- ptr_correct; eauto.
Qed.

Local Hint Resolve pointer_joined_ptr_h.

Lemma pointers_joined_init :
  chord_init_invariant (all_joined_ptrs pointer_joined).
Proof.
  autounfold_one. intuition.
  constructor.
  - do 2 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush.
    find_apply_lem_hyp in_firstn.
    match goal with
    | H : In ?s ?l, H' : ?l' = _ :: ?l |- _ => assert (In s l') by (repeat find_rewrite; in_crush)
    end. find_apply_lem_hyp in_sort_by_between. in_crush.
  - do 2 autounfold_one; simpl. intros.
    unfold initial_st in *. intuition. repeat find_rewrite. in_crush.
  - do 2 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush; try congruence.
    find_apply_lem_hyp hd_error_in.
    find_apply_lem_hyp in_rev.
    find_reverse_rewrite. find_apply_lem_hyp in_sort_by_between.
    in_crush.
  - do 2 autounfold_one; simpl. intros.
    unfold initial_st in *. intuition. repeat find_rewrite. in_crush.
  - do 2 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush; try congruence.
  - do 2 autounfold_one; simpl. intros.
    unfold initial_st in *. intuition. repeat find_rewrite. in_crush.
  - do 2 autounfold_one; simpl. intros.
    unfold initial_st in *. intuition. repeat find_rewrite. in_crush.
  - do 2 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush; try congruence.
  - do 2 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush; try congruence.
    find_inversion. solve_by_inversion.
  - do 3 autounfold_one; simpl.
    intros.
    find_eapply_lem_hyp sigma_initial_st_start_handler; auto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; in_crush; try congruence.
    exfalso.
    match goal with
    | _ : sort_by_between ?h (_ _ ?l) = _ |- _ =>
      pose proof sorted_knowns_same_length h l
    end.
    repeat find_rewrite. simpl in *.
    unfold initial_st in *. intuition.
    pose proof succ_list_len_lower_bound.
    (* yikes *)
    unfold addr in *.
    unfold ChordIDParams.name in *.
    omega.
Qed.

Local Hint Resolve pointer_joined_stable.

Lemma pointer_joined_make_pointer :
  forall gst h,
    pointer_joined gst h ->
    pointer_joined gst (make_pointer (addr_of h)).
Proof.
  unfold pointer_joined. simpl in *. intuition.
Qed.

Local Hint Resolve pointer_joined_make_pointer.

Lemma in_partition :
  forall A (l : list A) xs a ys,
    l = xs ++ a :: ys ->
    In a l.
Proof.
  intros. in_crush.
Qed.
Hint Resolve in_partition.

Lemma in_partition_if1 :
  forall A (x : A) xs y ys,
    In x xs ->
    In x (xs ++ y :: ys).
Proof. in_crush. Qed.

Local Hint Resolve in_partition_if1.

Lemma in_partition_if2 :
  forall A (x : A) xs y ys,
    In x ys ->
    In x (xs ++ y :: ys).
Proof. in_crush. Qed.

Local Hint Resolve in_partition_if2.

Ltac handler_simpler_joined :=
  discriminate ||
  solve [eauto] ||
  match goal with
  | H : In _ [] |- _ =>
    invcs H
  | H : In _ (concat _) |- _ =>
    apply in_concat in H; break_exists; intuition
  | H : In _ (handle_delayed_query _ _ _) |- _ =>
    unfold handle_delayed_query, handle_query_req in *
  | H : In _ (handle_query_req _ _ _) |- _ =>
    unfold handle_query_req in *
  | H : option_map _ _ = Some _ |- _ =>
    apply option_map_Some in H; break_exists
  | H : succs_msg _ _ |- _ =>
    invcs H
  | H:In ?x ?l, _:?l' = _ :: ?l |- _ =>
        match goal with
        | _:In x l' |- _ => fail 1
        | _ =>
          assert (In x l') by (repeat find_rewrite; in_crush)
        end
  | H : hd_error _ = Some _ |- _ =>
    apply hd_error_in in H
  | H : ptr _ = ?x |- context [?x] =>
    symmetry in H; rewrite H
  | |- context [best_predecessor ?x ?l ?p] =>
    pose proof (best_predecessor_in_succs_or_ptr x l (best_predecessor x l p) p);
    in_crush
  | H : joined_sender_msg _ |- _ =>
    try solve [inversion H]
  | H : joined_receiver_msg _ |- _ =>
    try solve [inversion H]
  | H : query_joined_ptr _ _ _ |- _ =>
    try solve [inversion H; subst; eauto]
  end ||
  break_match ||
  in_crush ||
  handler_simpl.

Lemma pointer_h_ptr_joined :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    pointer_joined gst (make_pointer h) ->
    pointer_joined gst (ptr st).
Proof.
  intros. erewrite ptr_correct; eauto.
Qed.
    
Local Hint Resolve pointer_h_ptr_joined.

Local Hint Resolve in_dedup_was_in.


Lemma pointers_joined_recv :
  chord_recv_handler_invariant (all_joined_ptrs pointer_joined).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_joined_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - repeat (handler_def || handler_simpler_joined);
      try solve
        [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto].
  - Time (repeat (handler_def || handler_simpler_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simpler_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simpler_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simpler_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simpler_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simpler_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simpler_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto];
      try solve
         [repeat find_rewrite; in_crush]).
  - Time (repeat (handler_def || handler_simpler_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simpler_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
Qed.

Ltac handler_simplerer_joined :=
  discriminate ||
  solve [eauto] ||
  match goal with
  | H : In _ [] |- _ =>
    invcs H
  | H : In _ (concat _) |- _ =>
    apply in_concat in H; break_exists; intuition
  | H : In _ (handle_delayed_query _ _ _) |- _ =>
    unfold handle_delayed_query, handle_query_req in *
  | H : In _ (handle_query_req _ _ _) |- _ =>
    unfold handle_query_req in *
  | H : option_map _ _ = Some _ |- _ =>
    apply option_map_Some in H; break_exists
  | H : succs_msg _ _ |- _ =>
    invcs H
  | H:In ?x ?l, _:?l' = _ :: ?l |- _ =>
        match goal with
        | _:In x l' |- _ => fail 1
        | _ =>
          assert (In x l') by (repeat find_rewrite; in_crush)
        end
  | H : hd_error _ = Some _ |- _ =>
    apply hd_error_in in H
  | H : ptr _ = ?x |- context [?x] =>
    symmetry in H; rewrite H
  | |- context [best_predecessor ?x ?l ?p] =>
    pose proof (best_predecessor_in_succs_or_ptr x l (best_predecessor x l p) p);
    in_crush
  | H : joined_sender_msg _ |- _ =>
    try solve [inversion H]
  | H : joined_receiver_msg _ |- _ =>
    try solve [inversion H]
  | H : joined_query _ |- _ =>
    try solve [inversion H]
  | H : query_joined_ptr _ _ _ |- _ =>
    try solve [inversion H; subst; eauto]
  end ||
  break_match ||
  in_crush ||
  handler_simpl.

Lemma pointers_joined_start :
  chord_start_invariant (all_joined_ptrs pointer_joined).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_joined_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - repeat (handler_def || handler_simplerer_joined);
      try solve
        [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto].
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto];
      try solve
         [repeat find_rewrite; in_crush]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
Qed.

Local Hint Unfold send_keepalives.

Lemma pointers_joined_keepalive :
  chord_keepalive_invariant (all_joined_ptrs pointer_joined).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_joined_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - repeat (handler_def || handler_simplerer_joined);
      try solve
        [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto].
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto];
      try solve
         [repeat find_rewrite; in_crush]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
Qed.

Lemma pointers_joined_tick :
  chord_tick_invariant (all_joined_ptrs pointer_joined).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_joined_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - repeat (handler_def || handler_simplerer_joined);
      try solve
        [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto].
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto];
      try solve
         [repeat find_rewrite; in_crush]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
    eapply pointer_joined_stable; eauto.
    eapply pointer_h_ptr_joined; eauto.
    unfold pointer_joined.
    simpl. intuition eauto.
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
Qed.


Lemma pointers_joined_fail :
  chord_fail_invariant (all_joined_ptrs pointer_joined).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_joined_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - repeat (handler_def || handler_simplerer_joined);
      try solve
        [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto].
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto];
      try solve
         [repeat find_rewrite; in_crush]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
Qed.


Lemma pointers_joined_rectify :
  chord_rectify_invariant (all_joined_ptrs pointer_joined).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_joined_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - repeat (handler_def || handler_simplerer_joined);
      try solve
        [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto].
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto];
      try solve
         [repeat find_rewrite; in_crush]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
Qed.


Lemma pointers_joined_request :
  chord_request_invariant (all_joined_ptrs pointer_joined).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_joined_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - repeat (handler_def || handler_simplerer_joined);
      try solve
        [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto].
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto];
      try solve
         [repeat find_rewrite; in_crush]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
Qed.


Lemma pointers_joined_input :
  chord_input_invariant (all_joined_ptrs pointer_joined).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_joined_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - repeat (handler_def || handler_simplerer_joined);
      try solve
        [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto].
  - Time (repeat (handler_def || handler_simplerer_joined);
            match goal with
            | H : client_payload _ |- _ =>
              try solve [inversion H]
            end).
  - Time (repeat (handler_def || handler_simplerer_joined);
            match goal with
            | H : client_payload _ |- _ =>
              try solve [inversion H]
            end).
  - Time (repeat (handler_def || handler_simplerer_joined);
            match goal with
            | H : client_payload _ |- _ =>
              try solve [inversion H]
            end).
  - Time (repeat (handler_def || handler_simplerer_joined);
            match goal with
            | H : client_payload _ |- _ =>
              try solve [inversion H]
            end).
  - repeat (handler_def || handler_simplerer_joined);
    match goal with
    | H : joined_sender_msg _ |- _ =>
      invcs H; solve_by_inversion
    | H : joined_receiver_msg _ |- _ =>
      invcs H; solve_by_inversion
    end.
  - repeat (handler_def || handler_simplerer_joined);
    match goal with
    | H : joined_sender_msg _ |- _ =>
      invcs H; solve_by_inversion
    | H : joined_receiver_msg _ |- _ =>
      invcs H; solve_by_inversion
    end.
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
Qed.


Lemma pointers_joined_output :
  chord_output_invariant (all_joined_ptrs pointer_joined).
Proof.
  do 2 autounfold_one. intros; simpl in *.
  inv_prop all_joined_ptrs.
  constructor; repeat find_rewrite; simpl in *.
  - repeat (handler_def || handler_simplerer_joined);
      try solve
        [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto].
  - Time (repeat (handler_def || handler_simplerer_joined);
            match goal with
            | H : client_payload _ |- _ =>
              try solve [inversion H]
            end).
  - Time (repeat (handler_def || handler_simplerer_joined);
            match goal with
            | H : client_payload _ |- _ =>
              try solve [inversion H]
            end).
  - Time (repeat (handler_def || handler_simplerer_joined);
            match goal with
            | H : client_payload _ |- _ =>
              try solve [inversion H]
            end).
  - Time (repeat (handler_def || handler_simplerer_joined);
            match goal with
            | H : client_payload _ |- _ =>
              try solve [inversion H]
            end).
  - repeat (handler_def || handler_simplerer_joined);
    match goal with
    | H : joined_sender_msg _ |- _ =>
      invcs H; solve_by_inversion
    | H : joined_receiver_msg _ |- _ =>
      invcs H; solve_by_inversion
    end.
  - repeat (handler_def || handler_simplerer_joined);
    match goal with
    | H : joined_sender_msg _ |- _ =>
      invcs H; solve_by_inversion
    | H : joined_receiver_msg _ |- _ =>
      invcs H; solve_by_inversion
    end.
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
  - Time (repeat (handler_def || handler_simplerer_joined);
      try solve
          [find_apply_lem_hyp in_firstn; in_crush; simpl; eauto]).
Qed.

Theorem pointers_joined :
  forall gst,
    reachable_st gst -> 
    all_joined_ptrs pointer_joined gst.
Proof.
  intros until 1. pattern gst.
  eapply chord_net_invariant.
  (* TODO(doug) need more theorems for each case here *)
  all:(try exact pointers_joined_recv; try exact pointers_joined_init; try exact pointers_joined_start;
       try exact pointers_joined_fail; try exact pointers_joined_tick; try exact pointers_joined_rectify;
       try exact pointers_joined_keepalive; try exact pointers_joined_request;
       try exact pointers_joined_input; try exact pointers_joined_output); auto.
Qed.


Lemma find_pred_in :
  forall h p l,
    find_pred h l = Some p ->
    In p l.
Proof.
  induction l using List.rev_ind.
  - unfold find_pred. simpl. intuition. congruence.
  - unfold find_pred. simpl.
    rewrite rev_unit. simpl.
    in_crush. find_inversion. auto.
Qed.


Lemma in_make_succs :
  forall p s l,
    In p (make_succs s l) ->
    p = s \/ In p l.
Proof.
  unfold make_succs. intros.
  find_apply_lem_hyp in_firstn.
  in_crush.
Qed.

Lemma best_predecessor_elim :
  forall h l h',
    best_predecessor h l h' = h \/
    In (best_predecessor h l h') l.
Proof.
  intros. unfold best_predecessor, hd.
  break_match; intuition.
  right.
  apply in_rev.
  eapply filter_In. rewrite Heql0. in_crush.
Qed.

Theorem stabilize_target_joined :
  forall gst h st dst m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, Stabilize, m) ->
    exists st__d,
      sigma gst (addr_of dst) = Some st__d /\
      joined st__d = true.
Proof.
  intros.
  assert (pointer_joined gst dst) by
      (find_eapply_lem_hyp pointers_joined; eauto).
  unfold pointer_joined in *. intuition eauto.
Qed.

Theorem stabilize2_target_joined :
  forall gst h st dst sdst m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, Stabilize2 sdst, m) ->
    exists st__d,
      sigma gst (addr_of dst) = Some st__d /\
      joined st__d = true.
Proof.
  intros.
  assert (pointer_joined gst dst) by
      (find_eapply_lem_hyp pointers_joined; eauto).
  unfold pointer_joined in *. intuition eauto.
Qed.

Theorem join2_target_joined :
  forall gst h st dst jdst m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, Join2 jdst, m) ->
    exists st__d,
      sigma gst (addr_of dst) = Some st__d /\
      joined st__d = true.
Proof.
  intros.
  exfalso; eauto using join2_unreachable.
Qed.

Lemma first_elem_in :
  forall A (P Q : A -> Prop) l,
    (forall y, In y l -> P y \/ Q y) ->
    (forall y, In y l -> Q y -> ~ P y) ->
    (forall y, In y l -> P y -> ~ Q y) ->
    forall x,
    In x l ->
    P x ->
    exists y xs ys,
      l = xs ++ y :: ys /\
      (forall z, In z xs -> Q z) /\
      P y.
Proof.
  induction l; intros; try solve_by_inversion.
  in_crush.
  - exists x. exists []. exists l. intuition.
    solve_by_inversion.
  - assert (P a \/ Q a); intuition.
    + exists a. exists []. exists l. intuition. solve_by_inversion.
    + repeat conclude_using in_crush.
      forward IHl; [firstorder|]. concludes.
      forward IHl; [firstorder|]. concludes.
      specialize (IHl x). intuition.
      break_exists_name y. exists y.
      break_exists_name xs. exists (a :: xs).
      break_exists_exists.
      intuition; simpl; try congruence.
      in_crush.
Qed.

Lemma live_node_not_dead_node :
  forall gst x,
    live_node gst x -> ~ dead_node gst x.
Proof.
  unfold live_node, dead_node. intuition.
Qed.

Lemma dead_node_not_live_node :
  forall gst x,
    dead_node gst x -> ~ live_node gst x.
Proof.
  unfold live_node, dead_node. intuition.
Qed.

Theorem live_node_in_succs_best_succ :
  forall gst h st l,
    reachable_st gst ->
    sigma gst h = Some st ->
    live_node gst l ->
    live_node gst h ->
    In l (map addr_of (succ_list st)) ->
    exists s, best_succ gst h s.
Proof.
  intros.
  pose proof (first_elem_in _ (live_node gst) (dead_node gst) (map addr_of (succ_list st))).
  forwards.
  {
    intros. 
    find_apply_lem_hyp in_map_iff.
    break_exists. intuition. subst.
    find_apply_lem_hyp successor_nodes_always_valid.
    eapply_prop_hyp successor_nodes_valid In; conclude_using eauto.
    intuition.
    unfold live_node, dead_node.
    destruct (in_dec addr_eq_dec (addr_of x) (failed_nodes gst)); intuition.
    right. intuition. 
    break_exists_exists. intuition.
  } repeat conclude_using ltac:(eauto using live_node_not_dead_node, dead_node_not_live_node).
  clear H5. eapply_prop_hyp In In; eauto.
  break_exists_exists.
  unfold best_succ. exists st. break_exists_exists.
  intuition.
Qed.

Lemma delayed_query_sources_active :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    forall src m,
      In (src, m) (delayed_queries st) ->
      In src (nodes gst).
Proof.
Admitted.