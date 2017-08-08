Require Import List.
Import ListNotations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import InfSeqExt.infseq.
Require Import Chord.Measure.
Require Import Chord.InfSeqTactics.

Require Import Chord.Chord.
Require Import Chord.ChordPromises.

Require Import Chord.ChordHandlerLemmas.
Require Import Chord.ChordSystemLemmas.
Require Import Chord.ChordSystemReachable.
Require Import Chord.ChordLabeled.

Require Import Chord.ChordQueryInvariant.
Require Import Chord.LiveNodesStayLive.
Require Import Chord.ChordDeadNodesGoQuiet.
Require Import Chord.ChordValidPointersInvariant.

Set Bullet Behavior "Strict Subproofs".
Open Scope nat_scope.

Definition has_dead_first_succ (gst : global_state) (h : addr) (s : pointer) :=
  exists st,
    sigma gst h = Some st /\
    exists rest,
      succ_list st = s :: rest /\
      In (addr_of s) (failed_nodes gst).

Lemma has_dead_first_succ_intro :
  forall gst h s st rest,
    sigma gst h = Some st ->
    succ_list st = s :: rest ->
    In (addr_of s) (failed_nodes gst) ->
    has_dead_first_succ gst h s.
Proof.
  firstorder eauto.
Qed.

(* cf. zave page 11 *)
Definition first_succ_is_best_succ (gst : global_state) (h : addr) :=
  exists st s rest,
    sigma gst h = Some st /\
    succ_list st = s :: rest /\
    best_succ gst h (addr_of s).

Definition all_first_succs_best (gst : global_state) :=
  forall h,
    live_node gst h ->
    first_succ_is_best_succ gst h.

Definition phase_one (o : occurrence) : Prop :=
  all_first_succs_best (occ_gst o).

(* Defining the error for phase one: the norm approach *)
Fixpoint succ_list_leading_failed_nodes (failed : list addr) (succs : list pointer) : nat :=
  match succs with
  | h :: rest =>
    if In_dec addr_eq_dec (addr_of h) failed
    then S (succ_list_leading_failed_nodes failed rest)
    else 0
  | [] => 0
  end.

(* The local error measure for phase one. *)
Definition leading_failed_succs (h : addr) (gst : global_state) : nat :=
  match sigma gst h with
  | Some st =>
    succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st)
  | None =>
    0
  end.

Lemma leading_failed_succs_st :
  forall h gst st,
    sigma gst h = Some st ->
    leading_failed_succs h gst = succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st).
Proof.
  unfold leading_failed_succs.
  intros.
  break_match; congruence.
Qed.

Definition phase_one_error : global_state -> nat :=
  global_measure leading_failed_succs.

Lemma successor_nodes_valid_inv :
  forall gst h p st,
    In p (succ_list st) ->
    successor_nodes_valid gst ->
    sigma gst h = Some st ->
    In (addr_of p) (nodes gst) /\
    exists pst, sigma gst (addr_of p) = Some pst /\
           joined pst = true.
Proof.
  eauto.
Qed.

Lemma successor_nodes_valid_live_are_joined :
  forall gst h st p,
    live_node gst (addr_of p) ->
    wf_ptr p ->
    successor_nodes_valid gst ->
    sigma gst h = Some st ->
    In p (succ_list st) ->
    live_node gst (addr_of p).
Proof.
  intros.
  now inv_prop live_node.
Qed.

Lemma zero_leading_failed_nodes_leading_node_live :
  forall gst h st s rest,
    succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st) = 0 ->
    reachable_st gst ->
    sigma gst h = Some st ->
    succ_list st = s :: rest ->
    wf_ptr s ->
    wf_ptr s /\ live_node gst (addr_of s).
Proof.
  intros.
  repeat find_rewrite.
  simpl in *.
  break_if; try congruence.
  unfold succ_list_leading_failed_nodes.
  find_apply_lem_hyp successor_nodes_always_valid.
  assert (In s (succ_list st)).
  {
    find_rewrite.
    apply in_eq.
  }
  find_eapply_lem_hyp successor_nodes_valid_inv; eauto; repeat (break_exists_name pst || break_and).
  eauto using live_node_characterization.
Qed.

Lemma maybe_count_failed_nodes_Some :
  forall gst h st n,
    leading_failed_succs h gst = n ->
    sigma gst h = Some st ->
    succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st) = n.
Proof.
  unfold leading_failed_succs.
  intros.
  break_match; congruence.
Qed.

Lemma zero_failed_nodes_total_implies_zero_locally :
  forall gst h st,
    phase_one_error gst = 0 ->
    live_node gst h ->
    sigma gst h = Some st ->
    succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st) = 0.
Proof.
  unfold phase_one_error in *.
  intros.
  cut (leading_failed_succs h gst = 0);
    eauto using maybe_count_failed_nodes_Some.
  find_eapply_lem_hyp local_all_zero_global_zero.
  find_eapply_lem_hyp Forall_forall; eauto.
  inv_prop live_node; break_and.
  eauto using in_nodes_not_failed_in_active.
Qed.

Lemma zero_leading_failed_nodes_best_succ :
  forall gst h st s rest,
    succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st) = 0 ->
    reachable_st gst ->
    sigma gst h = Some st ->
    succ_list st = s :: rest ->
    wf_ptr s ->
    live_node gst h ->
    best_succ gst h (addr_of s).
Proof.
  unfold best_succ.
  intros.
  exists st.
  exists [].
  exists (map addr_of rest).
  simpl.
  intuition.
  - repeat find_rewrite.
    apply map_cons.
  - eapply successor_nodes_valid_live_are_joined; eauto.
    + find_copy_eapply_lem_hyp zero_leading_failed_nodes_leading_node_live;
        eauto; tauto.
    + apply successor_nodes_always_valid.
      assumption.
    + repeat find_rewrite.
      apply in_eq.
Qed.

Theorem zero_leading_failed_nodes_implies_all_first_succs_best :
  forall gst,
    reachable_st gst ->
    (* total leading failed nodes says nothing about the length of successor lists *)
    nonempty_succ_lists gst ->
    phase_one_error gst = 0 ->
    all_first_succs_best gst.
Proof.
  unfold all_first_succs_best, first_succ_is_best_succ, phase_one_error.
  intros.
  find_copy_apply_lem_hyp local_all_zero_global_zero;
    rewrite Forall_forall in *.
  inv_prop live_node;
    repeat (break_and; break_exists_exists).
  unfold nonempty_succ_lists in *.
  find_copy_apply_hyp_hyp.
  destruct (succ_list _) as [| p rest] eqn:?H; [firstorder congruence|].
  exists p. exists rest.
  repeat split; auto.

  (* need an (easy) invariant *)
  assert (wf_ptr p) by eauto using wf_ptr_succ_list_invariant.

  assert (live_node gst h) by eauto.
  find_copy_apply_lem_hyp zero_failed_nodes_total_implies_zero_locally; auto.
  eapply zero_leading_failed_nodes_best_succ; eauto.
Qed.

Lemma zero_error_implies_phase_one :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    now (measure_zero phase_one_error) ex ->
    now phase_one ex.
Proof.
  intros.
  destruct ex.
  simpl in *.
  eapply zero_leading_failed_nodes_implies_all_first_succs_best; eauto.
  eapply nodes_have_nonempty_succ_lists; eauto.
Qed.

Theorem continuously_zero_total_leading_failed_nodes_implies_phase_one :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    infseq.continuously (now (measure_zero phase_one_error)) ex ->
    continuously (now phase_one) ex.
Proof.
  intros.
  pose proof zero_error_implies_phase_one.
  unfold continuously in *.
  prep_always_monotonic.
  eapply eventually_monotonic_simple.
  eapply always_monotonic; eauto.
  eapply continuously_and_tl; eauto.
  apply E0.
  eapply reachable_st_always; eauto.
Qed.

Lemma succ_list_leading_failed_nodes_nonzero_means_dead_succ :
  forall failed succs,
    succ_list_leading_failed_nodes failed succs > 0 ->
    exists p rest,
      succs = p :: rest /\
      In (addr_of p) failed.
Proof.
  unfold succ_list_leading_failed_nodes.
  destruct succs; intros.
  - omega.
  - break_if.
    + eexists; eauto.
    + omega.
Qed.

Lemma leading_failed_succs_nonzero_means_dead_succ :
  forall h gst,
    leading_failed_succs h gst > 0 ->
    exists s,
      has_dead_first_succ gst h s.
Proof.
  unfold leading_failed_succs, has_dead_first_succ.
  intros.
  break_match; [|omega].
  find_apply_lem_hyp succ_list_leading_failed_nodes_nonzero_means_dead_succ.
  expand_def.
  eexists; eauto.
Qed.

Lemma phase_one_error_nonzero_means_dead_succ :
  forall gst,
    phase_one_error gst > 0 ->
    exists h,
      In h (nodes gst) /\
      ~ In h (failed_nodes gst) /\
      exists s,
        has_dead_first_succ gst h s.
Proof.
  intros.
  find_apply_lem_hyp sum_nonzero_implies_addend_nonzero.
  break_exists; break_and.
  find_eapply_lem_hyp Coqlib.list_in_map_inv.
  break_exists_exists.
  firstorder using in_active_in_nodes, in_active_not_failed.
  apply leading_failed_succs_nonzero_means_dead_succ; omega.
Qed.

Definition open_stabilize_request_to (gst : global_state) (h : addr) (dst : addr) : Prop :=
  In GetPredAndSuccs (channel gst h dst) /\
  open_request_to gst h dst GetPredAndSuccs.

Definition open_stabilize_request (gst : global_state) (h : addr) : Prop :=
  exists p,
    open_stabilize_request_to gst h (addr_of p) /\
    wf_ptr p.

(** If h is a valid node with a first successor s in gst, then h has an open
    stabilize request to s in gst. *)
Definition open_stabilize_request_to_first_succ (gst : global_state) (h : addr) : Prop :=
  forall st dst rest,
    sigma gst h = Some st ->
    succ_list st = dst :: rest ->
    open_stabilize_request_to gst h (addr_of dst).

Lemma timeout_handler_eff_StartStabilize :
  forall h st r eff,
    timeout_handler_eff h st Tick = (r, eff) ->
    joined st = true /\ cur_request st = None <->
    eff = StartStabilize.
Proof.
  intros.
  destruct (timeout_handler_eff _ _ _) as [[[[?st' ?ms] ?nts] ?cts] ?eff] eqn:?H.
  find_apply_lem_hyp timeout_handler_eff_definition; expand_def;
    repeat find_rewrite; try congruence.
  find_eapply_lem_hyp tick_handler_definition; expand_def;
    repeat find_rewrite; firstorder congruence.
Qed.

Lemma timeout_handler_eff_is_timeout_handler_l :
  forall h st t res eff,
    timeout_handler_eff h st t = (res, eff) <->
    timeout_handler_l h st t = (res, Timeout h t eff).
Proof.
  intros.
  unfold timeout_handler_l.
  break_let.
  split; intros; solve_by_inversion.
Qed.

Lemma loaded_Tick_enabled_when_cur_request_None :
  forall gst h st,
    reachable_st gst ->
    live_node gst h ->
    sigma gst h = Some st ->
    cur_request st = None ->
    In Tick (timeouts gst h) ->
    enabled (Timeout h Tick StartStabilize) gst.
Proof.
  intros.
  break_live_node.
  (* replace x from live_node with st *)
  repeat find_rewrite; find_injection.
  destruct (timeout_handler_eff h st Tick) as [[[[st' ms] nts] cts] eff] eqn:?H.
  assert (eff = StartStabilize)
    by (eapply timeout_handler_eff_StartStabilize; eauto).
  subst.
  exists (apply_handler_result h (st', ms, nts, Tick :: cts) [e_timeout h Tick] gst).
  eapply LTimeout; eauto.
  - now apply timeout_handler_eff_is_timeout_handler_l.
  - now constructor.
Qed.

Lemma always_busy_or_not_busy :
  forall h occ,
    not_busy_if_live h occ \/ busy_if_live h occ.
Proof.
  intros.
  unfold not_busy_if_live, busy_if_live.
  destruct (sigma (occ_gst occ) h) as [d|];
   [destruct (cur_request d) eqn:?H|];
   firstorder congruence.
Qed.

Lemma not_busy_inf_often :
  forall h ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    always (~_ (now circular_wait)) ex ->
    inf_often (now (not_busy_if_live h)) ex.
Proof.
  intro.
  pose proof (always_busy_or_not_busy h) as H_bnb.
  cofix c.
  intros.
  constructor.
  - pose proof (H_bnb (hd ex)).
    destruct ex.
    break_or_hyp.
    + constructor.
      assumption.
    + apply queries_eventually_stop; auto.
  - destruct ex.
    simpl.
    eapply c.
    + eapply lb_execution_invar; eauto.
    + destruct ex.
      eapply reachable_st_lb_execution_cons; eauto.
    + eapply strong_local_fairness_invar; eauto.
    + inv_lb_execution.
      eapply live_node_invariant; eauto.
    + eapply always_invar; eauto.
Qed.

Lemma loaded_Tick_enabled_if_now_not_busy_if_live :
  forall h ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    now (not_busy_if_live h) ex ->
    now (l_enabled (Timeout h Tick StartStabilize)) ex.
Proof.
  intros.
  destruct ex.
  find_copy_apply_lem_hyp live_node_has_Tick_in_timeouts; eauto.
  simpl in *.
  find_copy_apply_lem_hyp live_node_joined; break_exists; break_and.
  unfold not_busy_if_live in *; find_copy_apply_hyp_hyp.
  eapply loaded_Tick_enabled_when_cur_request_None; eauto.
Qed.

Lemma loaded_Tick_inf_enabled :
  forall h ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    always (~_ (now circular_wait)) ex ->
    inf_enabled (Timeout h Tick StartStabilize) ex.
Proof.
  intros h.
  pose proof (always_busy_or_not_busy h) as H_bnb.
  intros.
  unfold inf_enabled.
  find_copy_apply_lem_hyp not_busy_inf_often; eauto.
  lift_inf_often (loaded_Tick_enabled_if_now_not_busy_if_live h);
    invar_eauto.
Qed.

Lemma loaded_Tick_inf_often :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    always (~_ (now circular_wait)) ex ->
    inf_occurred (Timeout h Tick StartStabilize) ex.
Proof.
  auto using loaded_Tick_inf_enabled.
Qed.

Lemma get_open_stabilize_request_to_first_succ_from_req_to :
  forall gst h st dst rest,
    open_stabilize_request_to gst h (addr_of dst) ->
    sigma gst h = Some st ->
    succ_list st = dst :: rest ->
    open_stabilize_request_to_first_succ gst h.
Proof.
  unfold open_stabilize_request_to_first_succ.
  intros.
  now repeat (find_injection || find_rewrite).
Qed.

Lemma option_map_Some :
  forall A B (f : A -> B) a b,
    option_map f a = Some b ->
    exists a', a = Some a' /\
          f a' = b.
Proof.
  intros.
  destruct a; simpl in *; try congruence.
  find_injection.
  eexists; eauto.
Qed.

Lemma option_map_None :
  forall A B (f : A -> B) a,
    option_map f a = None ->
    a = None.
Proof.
  intros.
  destruct a; simpl in *; congruence.
Qed.

Lemma make_request_Stabilize_needs_succ_list :
  forall h st dst m,
    make_request h st Stabilize = Some (dst, m) ->
    exists rest,
      succ_list st = dst :: rest.
Proof.
  intros.
  unfold make_request in *; simpl in *.
  find_apply_lem_hyp option_map_Some; break_exists; break_and.
  find_copy_apply_lem_hyp hd_error_some_nil.
  destruct (succ_list st) eqn:?H; [discriminate|].
  simpl in *.
  tuple_inversion.
  find_injection.
  eexists; eauto.
Qed.

Lemma make_request_Stabilize_None :
  forall h st,
    make_request h st Stabilize = None ->
    succ_list st = [].
Proof.
  intros.
  unfold make_request in *; simpl in *.
  simpl in *.
  find_eapply_lem_hyp option_map_None.
  destruct (succ_list st) eqn:?H; simpl in *; congruence.
Qed.

Lemma succ_list_preserved_by_Tick :
  forall gst gst' h st st',
    labeled_step_dynamic gst (Timeout h Tick StartStabilize) gst' ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    succ_list st' = succ_list st.
Proof.
  intros.
  inv_labeled_step; clean_up_labeled_step_cases.
  find_apply_lem_hyp timeout_handler_l_definition; expand_def.
  find_apply_lem_hyp timeout_handler_eff_definition; expand_def;
    try congruence.
  find_injection.
  find_apply_lem_hyp tick_handler_definition; expand_def;
    try congruence.
  rewrite sigma_ahr_updates in *; find_injection.
  destruct (start_query _ _ _) as [[[?st' ?ms] ?nts] ?cts] eqn:?H.
  find_eapply_lem_hyp add_tick_definition; expand_def.
  find_apply_lem_hyp start_query_definition; expand_def;
    repeat find_rewrite; solve_by_inversion.
Qed.

Lemma effective_Tick_sends_request :
  forall gst gst' h st s1 rest,
    sigma gst h = Some st ->
    succ_list st = s1 :: rest ->
    labeled_step_dynamic gst (Timeout h Tick StartStabilize) gst' ->
    open_stabilize_request_to gst' h (addr_of s1).
Proof.
  intros.
  inv_labeled_step; clean_up_labeled_step_cases.
  find_apply_lem_hyp timeout_handler_l_definition; expand_def.
  find_apply_lem_hyp timeout_handler_eff_definition; expand_def;
    try congruence.
  find_injection.
  find_apply_lem_hyp tick_handler_definition; expand_def;
    try congruence.
  unfold add_tick in *; repeat break_let;
    find_apply_lem_hyp start_query_definition; expand_def.
  - find_apply_lem_hyp option_map_Some; expand_def.
    find_apply_lem_hyp hd_error_tl_exists; expand_def.
    repeat (find_rewrite; repeat find_injection).
    simpl in *.
    repeat split;
      try apply channel_contents; simpl in *;
      rewrite_update; repeat eexists;
        eauto using StabilizeMsg with datatypes.
  - simpl in *.
    find_rewrite.
    find_injection.
    repeat find_rewrite.
    discriminate.
Qed.

Lemma effective_Tick_sends_request' :
  forall gst gst' h st s1 rest,
    sigma gst' h = Some st ->
    succ_list st = s1 :: rest ->
    labeled_step_dynamic gst (Timeout h Tick StartStabilize) gst' ->
    open_stabilize_request_to gst' h (addr_of s1).
Proof.
  intros.
  inv_labeled_step; clean_up_labeled_step_cases.
  find_apply_lem_hyp timeout_handler_l_definition; expand_def.
  find_apply_lem_hyp timeout_handler_eff_definition; expand_def;
    try congruence.
  find_injection.
  find_apply_lem_hyp tick_handler_definition; expand_def;
    try congruence.
  destruct (start_query _ _ _) as [[[?st' ?ms] ?nts] ?cts] eqn:?H.
  find_copy_eapply_lem_hyp succ_list_preserved_by_Tick; eauto.
  repeat find_rewrite.
  find_eapply_lem_hyp start_query_definition; expand_def.
  - find_copy_apply_lem_hyp make_request_Stabilize_needs_succ_list; break_exists.
    repeat find_rewrite.
    find_injection.
    eauto using effective_Tick_sends_request.
  - find_eapply_lem_hyp make_request_Stabilize_None.
    repeat find_rewrite.
    congruence.
Qed.

Lemma effective_Tick_occurred_sent_request :
  forall h ex,
    lb_execution ex ->
    now (occurred (Timeout h Tick StartStabilize)) ex ->
    next (now (fun o => open_stabilize_request_to_first_succ (occ_gst o) h)) ex.
Proof.
  intros.
  do 2 destruct ex.
  simpl in *.
  inv_lb_execution.
  unfold occurred in *.
  repeat find_reverse_rewrite.
  find_copy_apply_lem_hyp timeout_implies_state_exists_after; break_exists_name st'.
  find_copy_apply_lem_hyp timeout_implies_state_exists; break_exists_name st.
  destruct (succ_list st') eqn:?H.
  - congruence.
  - eapply get_open_stabilize_request_to_first_succ_from_req_to; eauto.
    eapply effective_Tick_sends_request'; eauto.
Qed.

Lemma start_stabilize_with_first_successor_eventually :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->

    live_node (occ_gst (hd ex)) h ->

    eventually (now (fun o => open_stabilize_request_to_first_succ o.(occ_gst) h)) ex.
Proof.
  intros.
  find_copy_apply_lem_hyp loaded_Tick_inf_often; auto.
  inv_prop inf_occurred.
  eapply eventually_next.
  lift_eventually (effective_Tick_occurred_sent_request h).
  invar_eauto.
Qed.

Lemma stabilize_timeout_means_successor_dead :
  forall ex h dst,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    now (occurred (Timeout h (Request dst GetPredAndSuccs) DetectFailure)) ex ->
    exists s,
      addr_of s = dst /\
      has_dead_first_succ ex.(hd).(occ_gst) h s.
Proof.
  intros.
  destruct ex as [o [o' ex]].
  simpl in *.
  unfold occurred in *.
  inv_prop lb_execution.
  repeat find_reverse_rewrite.
  inv_labeled_step; clean_up_labeled_step_cases.
  find_apply_lem_hyp timeout_handler_l_definition; expand_def;
    try congruence.
  find_apply_lem_hyp timeout_handler_eff_definition; expand_def;
    try congruence.
  repeat find_rewrite; find_injection.
  inv_prop timeout_constraint.
  find_eapply_lem_hyp stabilize_only_with_first_succ; eauto; break_exists_exists.
  firstorder.
  eexists; firstorder eauto.
  find_apply_lem_hyp hd_error_tl_exists; break_exists_exists; firstorder.
  now find_rewrite.
Qed.

Lemma stabilize_Request_timeout_removes_succ :
  forall ex h st s rest dst p,
    lb_execution ex ->
    sigma ex.(hd).(occ_gst) h = Some st ->
    succ_list st = s :: rest ->
    open_stabilize_request_to ex.(hd).(occ_gst) h dst ->
    now (occurred (Timeout h (Request dst p) DetectFailure)) ex ->
    next
      (now
         (fun occ =>
            exists st, sigma occ.(occ_gst) h = Some st /\
                  succ_list st = rest))
      ex.
Proof.
  intros.
  unfold open_stabilize_request, open_stabilize_request_to in *; break_exists; break_and.
  do 2 destruct ex.
  match goal with
  | [ H : lb_execution _ |- _ ] =>
    inv H; simpl in *
  end.
  unfold occurred in *.
  repeat find_reverse_rewrite.
  invc_labeled_step; simpl in *.

  (* This should be a lemma about timeout_handler_l. *)
  assert (h0 = h).
  {
    find_apply_lem_hyp timeout_handler_l_definition; expand_def.
    now find_injection.
  }
  subst_max.
  repeat find_rewrite; simpl.
  rewrite update_same.
  eexists; split; eauto.
  find_injection.

  find_apply_lem_hyp timeout_handler_l_definition; expand_def.
  repeat find_reverse_rewrite.
  find_injection.

  inv_prop open_request_to; expand_def.
  inv_prop request_msg_for_query.
  simpl in *.

  find_apply_lem_hyp request_timeout_handler_definition; expand_def; try congruence.
  find_eapply_lem_hyp handle_query_timeout_definition; expand_def; try congruence.
  repeat find_rewrite; repeat find_injection.
  (* Should use a definition lemma about start_query here. *)
  unfold start_query, update_query in *.
  simpl in *.
  repeat break_match;
    simpl in *;
    tuple_inversion;
    reflexivity.
Qed.

Lemma removing_head_decreases_failed_node_count :
  forall gst l gst' s rest,
    labeled_step_dynamic gst l gst' ->
    In (addr_of s) (failed_nodes gst) ->
    succ_list_leading_failed_nodes (failed_nodes gst') rest <
    succ_list_leading_failed_nodes (failed_nodes gst) (s :: rest).
Proof.
  intros.
  erewrite <- failed_nodes_eq; eauto.
  simpl.
  break_if;
    [|exfalso];
    auto with arith.
Qed.

Lemma stabilize_Request_timeout_decreases_error :
  forall ex h dst,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->

    open_stabilize_request_to ex.(hd).(occ_gst) h dst ->
    now (occurred (Timeout h (Request dst GetPredAndSuccs) DetectFailure)) ex ->
    consecutive (measure_decreasing (leading_failed_succs h)) ex.
Proof.
  intros.
  find_copy_eapply_lem_hyp stabilize_timeout_means_successor_dead; eauto.
  break_exists_name s; break_and.
  inv_prop has_dead_first_succ; expand_def.
  destruct ex as [o [o' ex]].
  find_copy_eapply_lem_hyp stabilize_Request_timeout_removes_succ; eauto.
  simpl in *; break_exists; break_and.
  unfold measure_decreasing.
  erewrite !leading_failed_succs_st; eauto.
  repeat find_rewrite.
  inv_prop lb_execution.
  eapply removing_head_decreases_failed_node_count; eauto.
Qed.

Lemma open_stabilize_request_until_timeout :
  forall ex h dst,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->

    open_stabilize_request_to ex.(hd).(occ_gst) h dst ->
    weak_until (now (fun occ => open_stabilize_request_to (occ_gst occ) h dst) /\_
                ~_ now (occurred (Timeout h (Request dst GetPredAndSuccs) DetectFailure)))
               (now (fun occ => open_stabilize_request_to (occ_gst occ) h dst) /\_
                now (occurred (Timeout h (Request dst GetPredAndSuccs) DetectFailure)))
               ex.
Proof.
Admitted.

Lemma open_stabilize_request_eventually_decreases_error :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->

    live_node (occ_gst (hd ex)) h ->

    leading_failed_succs h (occ_gst (hd ex)) > 0 ->
    open_stabilize_request_to_first_succ (occ_gst (hd ex)) h ->

    forall dst,
      has_dead_first_succ (occ_gst (hd ex)) h dst ->
      channel (occ_gst (hd ex)) (addr_of dst) h = [] ->
      eventually (consecutive (measure_decreasing (leading_failed_succs h))) ex.
Proof.
  intros.
  find_copy_apply_lem_hyp leading_failed_succs_nonzero_means_dead_succ; expand_def.
  unfold open_stabilize_request_to_first_succ in *.
  invc_prop has_dead_first_succ; expand_def.
  inv_prop has_dead_first_succ; expand_def.
  find_copy_apply_hyp_hyp.
  inv_prop open_stabilize_request_to.
  find_copy_eapply_lem_hyp open_stabilize_request_until_timeout; eauto.
  find_copy_apply_lem_hyp request_eventually_fires;
    eauto using strong_local_fairness_weak.
  find_copy_apply_lem_hyp eventually_weak_until_cumul; eauto.
  find_copy_apply_lem_hyp reachable_st_always; auto.
  - eapply eventually_monotonic; [| | eauto | eauto]; intros.
    + invar_eauto.
    + invc_prop always.
      unfold and_tl in *; break_and.
      invcs_prop weak_until; break_and;
        destruct s;
        eapply stabilize_Request_timeout_decreases_error; eauto.
  - eapply weak_until_latch_eventually; eauto.
Qed.

Lemma nonzero_phase_one_error_eventually_drops_dead_quiet :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now no_msgs_from_dead_nodes) ex ->

    live_node (occ_gst (hd ex)) h ->
    leading_failed_succs h (occ_gst (hd ex)) > 0 ->

    eventually (consecutive (measure_decreasing (leading_failed_succs h))) ex.
Proof.
  intros.
  find_copy_eapply_lem_hyp start_stabilize_with_first_successor_eventually; eauto.
  induction 0 as [ex|o ex].
  - find_copy_apply_lem_hyp leading_failed_succs_nonzero_means_dead_succ; expand_def.
    destruct ex.
    eapply open_stabilize_request_eventually_decreases_error; simpl in *; eauto.
    inv_prop has_dead_first_succ; expand_def.
    inv_prop no_msgs_from_dead_nodes; simpl in *.
    eapply no_msgs_from_dead_nodes_elim; eauto.
  - destruct ex as [o' ex].
    destruct (leading_failed_succs h (occ_gst o')) eqn:?H.
    + apply E0.
      simpl in *.
      unfold measure_decreasing.
      omega.
    + apply E_next.
      apply IHeventually; invar_eauto.
      simpl in *; omega.
Qed.

Lemma nonzero_phase_one_error_eventually_drops :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->

    live_node (occ_gst (hd ex)) h ->
    leading_failed_succs h (occ_gst (hd ex)) > 0 ->

    eventually (consecutive (measure_decreasing (leading_failed_succs h))) ex.
Proof.
  intros.
  find_copy_eapply_lem_hyp dead_nodes_go_quiet; eauto.
  induction 0 as [ex | o [o' ex]].
  - eauto using nonzero_phase_one_error_eventually_drops_dead_quiet.
  - destruct (leading_failed_succs h (occ_gst o')) eqn:?H.
    + apply E0; simpl in *.
      unfold measure_decreasing; omega.
    + apply E_next.
      apply IHeventually; invar_eauto.
      simpl in *; omega.
Qed.

Lemma nonempty_succ_list_implies_joined :
  forall gst h st s rest,
    reachable_st gst ->
    sigma gst h = Some st ->
    succ_list st = s :: rest ->
    joined st = true.
Proof.
  intros.
  destruct (joined st) eqn:?H;
    [|find_apply_lem_hyp nodes_not_joined_have_no_successors; auto];
    congruence.
Qed.

Lemma has_dead_first_succ_implies_error_nonzero :
  forall gst h s,
    has_dead_first_succ gst h s ->
    leading_failed_succs h gst > 0.
Proof.
  unfold has_dead_first_succ.
  intros.
  expand_def.
  unfold leading_failed_succs, succ_list_leading_failed_nodes.
  repeat find_rewrite.
  break_if; [|exfalso];
    auto with arith.
Qed.

Theorem phase_one_nonzero_error_causes_measure_drop :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (nonzero_error_causes_measure_drop leading_failed_succs) ex.
Proof.
  cofix c.
  intros.
  destruct ex.
  constructor.
  - intro.
    find_copy_apply_lem_hyp phase_one_error_nonzero_means_dead_succ.
    break_exists_exists; expand_def.
    split; auto using in_nodes_not_failed_in_active.
    inv_prop has_dead_first_succ; expand_def.
    eapply nonzero_phase_one_error_eventually_drops; eauto.
    + find_eapply_lem_hyp nonempty_succ_list_implies_joined;
        eauto using live_node_characterization.
    + eauto using has_dead_first_succ_intro, has_dead_first_succ_implies_error_nonzero.
  - apply c; invar_eauto.
Qed.

Theorem phase_one_error_continuously_nonincreasing :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    continuously (local_measures_nonincreasing leading_failed_succs) ex.
Proof.
Admitted.

Theorem phase_one_continuously :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    continuously (now phase_one) ex.
Proof.
  intros.
  eapply continuously_zero_total_leading_failed_nodes_implies_phase_one; eauto.
  eapply local_measure_causes_measure_zero_continuosly; eauto.
  - eapply phase_one_error_continuously_nonincreasing; eauto.
  - eauto using always_continuously, phase_one_nonzero_error_causes_measure_drop.
Qed.
