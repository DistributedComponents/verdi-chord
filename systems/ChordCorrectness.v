Require Import List.
Import ListNotations.
Require Import Omega.

Require Verdi.Coqlib.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.
Require Import InfSeqExt.infseq.
Require Import Chord.InfSeqTactics.
Require Import Chord.Measure.

Require Import Chord.Chord.
Import Chord.Chord.Chord.
Import ChordIDSpace.
Require Import Chord.ChordProof.
Require Import Chord.ChordSemantics.
Import ChordSemantics.
Import ConstrainedChord.
Require Import Chord.ChordValidPointersInvariant.
Require Import Chord.ChordLabeled.
Require Import Chord.ChordPromises.
Require Import Chord.ChordDefinitionLemmas.

Set Bullet Behavior "Strict Subproofs".
Open Scope nat_scope.

Definition reachable_after_churn gst :=
  exists ex,
    reachable_st (occ_gst (infseq.hd ex)) /\
    lb_execution ex /\
    infseq.eventually (fun ex' => gst = (occ_gst (infseq.hd ex'))) ex.

Definition live_addr (gst : global_state) (a : addr) :=
  In a (nodes gst) /\
  ~ In a (failed_nodes gst) /\
  exists st, sigma gst a = Some st.

Definition live_addr_dec :
  forall gst a,
    {live_addr gst a} + {~ live_addr gst a}.
Admitted.

Lemma live_node_is_live_addr :
  forall gst h,
    live_node gst h ->
    live_addr gst h.
Proof.
  intros.
  unfold live_addr.
  repeat split;
    eauto using live_node_joined,
                live_node_in_nodes,
                live_node_not_in_failed_nodes,
                live_node_means_state_exists.
Qed.

Definition live (gst : global_state) (p : pointer) :=
  live_addr gst (addr_of p) /\
  wf_ptr p.

Definition live_dec :
  forall gst p,
    {live gst p} + {~ live gst p}.
Proof.
  unfold live.
  intros.
  destruct (live_addr_dec gst (addr_of p));
    destruct (wf_ptr_dec p);
    tauto.
Defined.

Lemma live_live_addr :
  forall gst p,
    wf_ptr p ->
    live gst p <-> live_addr gst (addr_of p).
Proof.
  now unfold live.
Qed.

Lemma live_addr_intro :
  forall gst a st,
    In a (nodes gst) ->
    ~ In a (failed_nodes gst) ->
    sigma gst a = Some st ->
    live_addr gst a.
Proof.
  unfold live_addr.
  eauto.
Qed.

Lemma live_intro :
  forall gst p st,
    wf_ptr p ->
    In (addr_of p) (nodes gst) ->
    ~ In (addr_of p) (failed_nodes gst) ->
    sigma gst (addr_of p) = Some st ->
    live gst p.
Proof.
  unfold live.
  eauto using live_addr_intro.
Qed.

Lemma live_addr_inv :
  forall gst a,
    live_addr gst a ->
    In a (nodes gst) /\
    ~ In a (failed_nodes gst) /\
    exists st, sigma gst a = Some st.
Proof.
  easy.
Qed.

Lemma live_inv :
  forall gst p,
    live gst p ->
    wf_ptr p /\
    In (addr_of p) (nodes gst) /\
    ~ In (addr_of p) (failed_nodes gst) /\
    exists st, sigma gst (addr_of p) = Some st.
Proof.
  unfold live.
  intros.
  break_and.
  auto using live_addr_inv.
Qed.

Ltac live_addr_inv :=
  match goal with
  | [ H_live : live_addr ?gst ?a |- _ ] =>
    apply live_addr_inv in H_live;
      destruct H_live as [?H [?H ?H]];
      match goal with
      | [ H_st : exists st, sigma gst a = Some st |- _ ] =>
        destruct H_st as [?st]
      end
  end.

Ltac live_inv :=
  match goal with
  | [ H_live : live ?gst ?p |- _ ] =>
    apply live_inv in H_live;
      destruct H_live as [?H [?H [?H ?H]]];
      match goal with
      | [ H_st : exists st, sigma gst (addr_of p) = Some st |- _ ] =>
        destruct H_st as [?st]
      end
  end.

Definition live_addrs (gst : global_state) : list addr :=
  filter (fun a => Coqlib.proj_sumbool (live_addr_dec gst a))
         (nodes gst).

Definition live_ptrs (gst : global_state) : list pointer :=
  map make_pointer (live_addrs gst).

Definition live_ptrs_with_states (gst : global_state) : list (pointer * data) :=
  FilterMap.filterMap (fun p =>
                         match sigma gst (addr_of p) with
                         | Some st => Some (p, st)
                         | None => None
                         end)
                      (live_ptrs gst).

Definition full_succs (gst : global_state) (h : pointer) (succs : list pointer) : Prop :=
  length succs = Chord.SUCC_LIST_LEN.

(* cf. zave page 11 *)
Definition first_succ_is_best_succ (gst : global_state) (h : addr) :=
  exists st s rest,
    sigma gst h = Some st /\
    succ_list st = s :: rest /\
    best_succ gst h (addr_of s).

Definition all_first_succs_best (gst : global_state) :=
  forall h,
    live gst h ->
    first_succ_is_best_succ gst (addr_of h).

Definition circular_wait : occurrence -> Prop.
Admitted.

Definition phase_one (ex : infseq.infseq occurrence) :=
  lb_execution ex ->
  reachable_st (occ_gst (infseq.hd ex)) ->
  always (~_ (now circular_wait)) ex ->
  infseq.continuously (lift_gpred_to_ex all_first_succs_best) ex.

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

Definition phase_one_error : global_state -> nat :=
  global_measure leading_failed_succs.

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

Definition nonempty_succ_lists (gst : global_state) : Prop :=
  forall h st,
    sigma gst h = Some st ->
    succ_list st <> [].

Definition successor_nodes_valid (gst : global_state) : Prop :=
  forall h p st,
    In p (succ_list st) ->
    sigma gst h = Some st ->
    In (addr_of p) (nodes gst) /\
    exists pst, sigma gst (addr_of p) = Some pst /\
           joined pst = true.

Lemma successor_nodes_valid_state :
  forall gst h p st,
    In p (succ_list st) ->
    successor_nodes_valid gst ->
    sigma gst h = Some st ->
    exists pst, sigma gst (addr_of p) = Some pst /\
           joined pst = true.
Proof.
  intros.
  eapply_prop_hyp successor_nodes_valid @eq; eauto.
  now break_and.
Qed.

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
    live gst p ->
    successor_nodes_valid gst ->
    sigma gst h = Some st ->
    In p (succ_list st) ->
    live_node gst (addr_of p).
Proof.
  intros.
  live_inv.
  find_eapply_lem_hyp successor_nodes_valid_inv;
    eauto; repeat (break_and; break_exists).
  eapply live_node_characterization; eauto.
Qed.

Lemma successor_nodes_always_valid :
  forall gst,
    reachable_after_churn gst ->
    successor_nodes_valid gst.
Proof.
Admitted.

Lemma nonempty_succ_lists_always_belong_to_joined_nodes :
  forall gst h st,
    reachable_after_churn gst ->
    sigma gst h = Some st ->
    succ_list st <> [] ->
    joined st = true.
Admitted.

Lemma zero_leading_failed_nodes_leading_node_live :
  forall gst h st s rest,
    succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st) = 0 ->
    reachable_after_churn gst ->
    sigma gst h = Some st ->
    succ_list st = s :: rest ->
    wf_ptr s ->
    live gst s.
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
  eapply live_intro; eauto.
Qed.

Lemma zero_leading_failed_nodes_best_succ :
  forall gst h st s rest,
    succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st) = 0 ->
    reachable_after_churn gst ->
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
    + find_copy_eapply_lem_hyp zero_leading_failed_nodes_leading_node_live; eauto.
    + apply successor_nodes_always_valid.
      assumption.
    + repeat find_rewrite.
      apply in_eq.
Qed.

Lemma zero_failed_nodes_total_implies_zero_locally :
  forall gst h st,
    phase_one_error gst = 0 ->
    live_addr gst h ->
    sigma gst h = Some st ->
    succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st) = 0.
Proof.
  unfold phase_one_error in *.
  intros.
  cut (leading_failed_succs h gst = 0);
    eauto using maybe_count_failed_nodes_Some.
  find_eapply_lem_hyp local_all_zero_global_zero.
  find_eapply_lem_hyp Forall_forall; eauto.
  now inv_prop live_addr.
Qed.

Theorem zero_leading_failed_nodes_implies_all_first_succs_best :
  forall gst,
    reachable_after_churn gst ->
    (* total leading failed nodes says nothing about the length of successor lists *)
    nonempty_succ_lists gst ->
    phase_one_error gst = 0 ->
    all_first_succs_best gst.
Proof.
  unfold all_first_succs_best, first_succ_is_best_succ, phase_one_error.
  intros.
  find_copy_apply_lem_hyp local_all_zero_global_zero;
    rewrite Forall_forall in *.
  find_apply_lem_hyp live_inv;
    break_and;
    break_exists_exists.
  unfold nonempty_succ_lists in *.
  find_copy_apply_hyp_hyp.
  destruct (succ_list _) as [| p rest] eqn:?H; [congruence|].
  exists p. exists rest.
  repeat split; auto.

  (* need an (easy) invariant *)
  assert (wf_ptr p) by admit.

  assert (live gst h) by eauto using live_intro.
  find_copy_apply_lem_hyp live_live_addr; auto.
  find_copy_apply_lem_hyp zero_failed_nodes_total_implies_zero_locally; auto.
  eapply zero_leading_failed_nodes_best_succ; eauto.
  eapply live_node_characterization; eauto.
  eapply nonempty_succ_lists_always_belong_to_joined_nodes; eauto.
Admitted.

Lemma always_reachable_after_churn :
  forall ex,
    reachable_st (occ_gst (infseq.hd ex)) ->
    infseq.always (lift_gpred_to_ex reachable_after_churn) ex.
Proof.
Admitted.

(*
if head of succ list is dead
then we set
cur_request
Request dst (message?)
with cur_request = (make_pointer dst, q, _)
with q = Stabilize
with q = Stabilize2
*)

Definition open_stabilize_request_to (gst : global_state) (h : addr) (dst : addr) : Prop :=
  In (Request dst GetPredAndSuccs) (timeouts gst h) /\
  In (h, (dst, GetPredAndSuccs)) (msgs gst) /\
  exists st dstp,
    sigma gst h = Some st /\
    addr_of dstp = dst /\
    cur_request st = Some (dstp, Stabilize, GetPredAndSuccs).

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
  find_apply_lem_hyp timeout_handler_definition; expand_def;
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

Definition busy_if_live (h : addr) (occ : occurrence) :=
  forall st,
    live_node (occ_gst occ) h ->
    sigma (occ_gst occ) h = Some st ->
    cur_request st <> None.

Definition not_busy_if_live (h : addr) (occ : occurrence) :=
  forall st,
    live_node (occ_gst occ) h ->
    sigma (occ_gst occ) h = Some st ->
    cur_request st = None.

(** the big assumption for inf_often stabilization *)
Theorem queries_eventually_stop :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    busy_if_live h (hd ex) ->
    always (~_ (now circular_wait)) ex ->
    eventually (now (not_busy_if_live h)) ex.
Proof.
  (*         -____-   *)
Admitted.

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

Lemma live_node_has_Tick_in_timeouts :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    live_node (occ_gst (hd ex)) h ->
    In Tick (timeouts (occ_gst (hd ex)) h).
Admitted.

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

Lemma lb_execution_step_structural :
  forall o o' ex,
    lb_execution (Cons o (Cons o' ex)) ->
    labeled_step_dynamic (occ_gst o) (occ_label o) (occ_gst o').
Proof.
  intros.
  now inv_lb_execution.
Qed.

Lemma lb_execution_step_one_cons :
  forall o ex,
    lb_execution (Cons o ex) ->
    labeled_step_dynamic (occ_gst o) (occ_label o) (occ_gst (hd ex)).
Proof.
  intros.
  destruct ex.
  eauto using lb_execution_step_structural.
Qed.

Lemma lb_execution_two_cons :
  forall ex,
    lb_execution ex ->
    labeled_step_dynamic (occ_gst (hd ex)) (occ_label (hd ex)) (occ_gst (hd (tl ex))).
Proof.
  intros.
  do 2 destruct ex.
  eauto using lb_execution_step_structural.
Qed.

Ltac invar_eauto :=
  eauto using
        lb_execution_invar,
        strong_local_fairness_invar,
        live_node_invariant,
        labeled_step_is_unlabeled_step,
        reachableStep,
        lb_execution_step_one_cons.

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
  find_apply_lem_hyp timeout_handler_definition; expand_def;
    try congruence.
  find_injection.
  find_apply_lem_hyp tick_handler_definition; expand_def;
    try congruence.
  unfold add_tick in *; repeat break_let;
    find_apply_lem_hyp start_query_definition; expand_def.
  - simpl in *.
    repeat find_rewrite.
    find_injection.
    repeat find_rewrite.
    simpl in *.
    find_injection.
    repeat split; simpl in *;
      try rewrite update_same in *;
      eauto with datatypes.
  - simpl in *.
    find_rewrite.
    find_injection.
    repeat find_rewrite.
    discriminate.
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
  find_apply_lem_hyp timeout_handler_definition; expand_def;
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
  find_apply_lem_hyp timeout_handler_definition; expand_def;
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

Lemma leading_failed_succs_st :
  forall h gst st,
    sigma gst h = Some st ->
    leading_failed_succs h gst = succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st).
Proof.
  unfold leading_failed_succs.
  intros.
  break_match; congruence.
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

  (* This should be a lemma about timeout_handler_l *)
  find_apply_lem_hyp timeout_handler_l_definition; expand_def.
  repeat find_reverse_rewrite.
  find_injection.

  assert (st0 = x0)
    by (repeat find_rewrite; now find_injection);
    subst.

  simpl in *.
  unfold request_timeout_handler in *.
  repeat find_rewrite.
  repeat find_rewrite.
  simpl in *.
  break_if; [|congruence].
  repeat find_rewrite.
  (* Should use a definition lemma about start_query here. *)
  unfold start_query, update_query in *.
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

Lemma stablize_Request_timeout_decreases_error :
  forall ex h st s rest dst p,
    lb_execution ex ->
    In (addr_of s) (failed_nodes (occ_gst (hd ex))) ->
    sigma ex.(hd).(occ_gst) h = Some st ->
    succ_list st = s :: rest ->
    open_stabilize_request_to ex.(hd).(occ_gst) h dst ->
    now (occurred (Timeout h (Request dst p) DetectFailure)) ex ->
    consecutive (measure_decreasing (leading_failed_succs h)) ex.
Proof.
  intros.
  destruct ex as [o [o' ex]].
  find_copy_eapply_lem_hyp stabilize_Request_timeout_removes_succ; eauto.
  simpl in *; break_exists; break_and.
  unfold measure_decreasing.
  erewrite !leading_failed_succs_st; eauto.
  repeat find_rewrite.
  inv_prop lb_execution.
  eapply removing_head_decreases_failed_node_count; eauto.
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

(* This belongs in ChordLabeled.v *)
Lemma Timeout_enabled_when_open_stabilize_request_to_dead_node :
  forall occ h st dst,
    live_node (occ_gst occ) h ->
    sigma (occ_gst occ) h = Some st ->
    open_stabilize_request_to (occ_gst occ) h dst ->
    In dst (failed_nodes (occ_gst occ)) ->
    (forall m, ~ In (dst, (h, m)) (msgs (occ_gst occ))) ->
    l_enabled (Timeout h (Request dst GetPredAndSuccs) DetectFailure) occ.
Proof.
  intros.
  break_live_node.
  unfold open_stabilize_request_to in *; break_and; repeat break_exists.
  destruct (timeout_handler_l h st (Request dst GetPredAndSuccs))
    as [[[[st' ms] nts] cts] l] eqn:H_thl.
  copy_apply timeout_handler_l_definition H_thl; expand_def.
  assert (x2 = DetectFailure).
  {
    find_copy_apply_lem_hyp timeout_handler_definition; expand_def; try congruence.
    find_apply_lem_hyp request_timeout_handler_definition; expand_def.
    - now find_injection.
    - repeat find_rewrite.
      repeat find_injection.
      simpl in *.
      congruence.
    - congruence.
  }
  subst.
  repeat find_rewrite.

  eexists; repeat find_reverse_rewrite; eapply LTimeout; eauto.
  eapply Request_needs_dst_dead_and_no_msgs; eauto.
Qed.

Lemma timeout_Request_to_dead_node_eventually_fires :
  forall ex h dst,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    weak_local_fairness ex ->
    In dst (failed_nodes (occ_gst (hd ex))) ->
    now (fun occ =>
           exists st,
             sigma (occ_gst occ) h = Some st /\
             open_stabilize_request_to (occ_gst occ) h dst)
        ex ->
    exists p,
      until (next (now (fun occ => forall st,
                      In dst (failed_nodes (occ_gst occ)) ->
                      sigma (occ_gst occ) h = Some st ->
                      open_stabilize_request_to (occ_gst occ) h dst)))
            (now (occurred (Timeout h (Request dst p) DetectFailure)))
            ex.
Proof.
  intros.
  destruct ex; simpl in *; break_exists; break_and.
  unfold open_stabilize_request_to in *; break_and.
  exists GetPredAndSuccs.
  match goal with
  | [ |- until ?P ?Q ?ex ] =>
    cut (weak_until P Q ex)
  end.
  - intros.
    find_apply_lem_hyp classical.weak_until_until_or_always.
    break_or_hyp; [assumption|].
    exfalso.
    cut ((cont_enabled (Timeout h (Request dst GetPredAndSuccs) DetectFailure)) ex).
    + intros.
      find_apply_lem_hyp weak_local_fairness_invar.
      unfold weak_local_fairness in *.
      find_apply_hyp_hyp.
      unfold inf_occurred, inf_often in *.
      destruct ex.
      find_apply_lem_hyp always_now.
      specialize (H1 (Timeout h (Request dst GetPredAndSuccs) DetectFailure)).
      find_eapply_lem_hyp lb_execution_invar.
      find_eapply_lem_hyp always_Cons; break_and.
      induction H7.
      * do 2 destruct s.
        find_copy_apply_lem_hyp always_Cons.
        break_and.
        find_copy_apply_lem_hyp always_now.
        simpl in *.
        do 2 match goal with
        | [ H : (lb_execution _) |- _ ] =>
          inv H
        end.
        match goal with
        | [ H : occurred ?t ?occ |- _ ] =>
          unfold occurred in H
        end.
        repeat find_reverse_rewrite.
        match goal with
        | [ H : labeled_step_dynamic _ (Timeout _ _ _) _ |- _ ] =>
          invc H; clean_up_labeled_step_cases
        end.
        admit.
      * apply IHeventually; eauto using lb_execution_invar.
        -- admit.
        -- find_apply_lem_hyp always_Cons; tauto.
        -- find_apply_lem_hyp always_Cons; tauto.
    + admit.
      (* can get this by showing that eventually all messages from a dead node
      are delivered and that we can then use
      Timeout_enabled_when_open_stabilize_request_to_dead_node. *)
  - admit.
Admitted.

Lemma dead_successor_eventually_removed :
  forall ex h st s rest,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    weak_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    sigma (occ_gst (hd ex)) h = Some st ->
    succ_list st = s :: rest ->
    In (addr_of s) (failed_nodes (occ_gst (hd ex))) ->
    eventually
      (now
         (fun occ =>
            forall st', sigma (occ_gst occ) h = Some st' ->
                   succ_list st' = rest))
      ex.
Proof.
  intros.
  find_copy_eapply_lem_hyp start_stabilize_with_first_successor_eventually; eauto.
Admitted.

Lemma recv_handler_label_is_RecvMsg :
  forall h st src m res l,
    recv_handler_l h src st m = (res, l) ->
    l = RecvMsg h src m.
Proof.
  unfold recv_handler_l.
  congruence.
Qed.

Theorem continuously_zero_total_leading_failed_nodes_implies_phase_one :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    infseq.continuously
      (now (measure_zero phase_one_error) /\_
       lift_gpred_to_ex nonempty_succ_lists)
      ex ->
    phase_one ex.
Proof.
Admitted.

(** In phase two we want to talk about the existence and number of better
    predecessors and better first successors to a node. We do this with the
    following functions.
    - better_* : Prop, which holds if a node is closer to h.
    - better_*_bool : bool, which is true if some live node is a better pointer for h.
    - *_correct : Prop, which holds if the pointer is globally correct.
    - *_error : nat, which counts the number of better options for the pointer.
    We prove that error = 0 <-> correct so we can use an argument about the
    metric to prove eventual correctness.
 *)

Definition counting_opt_error (gst : global_state) (p : option pointer) (better_bool : pointer -> pointer -> bool) : nat :=
  match p with
  | Some p0 =>
    if live_dec gst p0
    then length (filter (better_bool p0) (live_ptrs gst))
    else length (live_ptrs gst) + 1
  | None => length (live_ptrs gst) + 1
  end.

Lemma counting_opt_error_zero_implies_correct :
  forall gst p better_bool,
    counting_opt_error gst p better_bool = 0 ->
    exists p0,
      p = Some p0 /\
      forall p',
        live gst p' ->
        better_bool p0 p' = false.
Proof.
  unfold counting_opt_error.
  intros.
  repeat break_match.
Admitted.

(** Predecessor phase two definitions *)
Definition better_pred (gst : global_state) (h p p' : pointer) : Prop :=
  live gst p' /\ ptr_between p p' h.

Definition better_pred_bool (h p p' : pointer) : bool :=
  ptr_between_bool p p' h.

Definition pred_correct (gst : global_state) (h : pointer) (p : option pointer) : Prop :=
  exists p0,
    p = Some p0 /\
    forall p',
      ~ better_pred gst h p0 p'.

Definition pred_error (gst : global_state) (h : pointer) (p : option pointer) : nat :=
  counting_opt_error gst p (better_pred_bool h).

(** First successor phase two definitions *)
Definition better_succ (gst : global_state) (h s s' : pointer) : Prop :=
  live gst s' /\ ptr_between h s' s.

Definition better_succ_bool (h s s' : pointer) : bool :=
  ptr_between_bool h s' s.

Definition first_succ_correct (gst : global_state) (h : pointer) (p : option pointer) : Prop :=
  exists p0,
    p = Some p0 /\
    forall p', ~ better_succ gst h p0 p'.

Definition first_succ_error (gst : global_state) (h : pointer) (s : option pointer) : nat :=
  counting_opt_error gst s (better_succ_bool h).

(** First successor and predecessor combined phase two definitions *)
Definition pred_and_first_succ_correct (gst : global_state) (h : pointer) (st : data) : Prop :=
  pred_correct gst h (pred st) /\
  first_succ_correct gst h (hd_error (succ_list st)).

Definition pred_and_first_succ_error (gst : global_state) (h : pointer) (st : data) : nat :=
  pred_error gst h (pred st) + first_succ_error gst h (hd_error (succ_list st)).

Definition preds_and_first_succs_correct (gst : global_state) : Prop :=
  forall h st,
    live gst h ->
    sigma gst (addr_of h) = Some st ->
    pred_and_first_succ_correct gst h st.

Definition total_measure (local_measure : pointer -> data -> nat) (gst : global_state) :=
  sum (map (fun pair => let '(h, st) := pair in
                     local_measure h st)
           (live_ptrs_with_states gst)).

Definition total_pred_and_first_succ_error (gst : global_state) : nat :=
  total_measure (pred_and_first_succ_error gst) gst.

Lemma phase_two_zero_error_locally_correct :
  forall gst h st,
    live gst h ->
    sigma gst (addr_of h) = Some st ->
    pred_and_first_succ_error gst h st = 0 ->
    pred_and_first_succ_correct gst h st.
Proof.
Admitted.
Lemma live_addr_In_live_addrs :
  forall gst h,
    live_addr gst h ->
    In h (live_addrs gst).
Proof.
  unfold live_addrs.
  intros.
  apply filter_In; split.
  - unfold live_addr in *; break_and; auto.
  - auto using Coqlib.proj_sumbool_is_true.
Qed.

Lemma live_In_live_ptrs :
  forall gst h,
    live gst h ->
    wf_ptr h ->
    In h (live_ptrs gst).
Proof.
  unfold live_ptrs, live.
  intros.
  rewrite (wf_ptr_eq h); auto.
  apply in_map.
  now apply live_addr_In_live_addrs.
Qed.

Lemma live_In_live_ptrs_with_states :
  forall gst h st,
    wf_ptr h ->
    live gst h ->
    sigma gst (addr_of h) = Some st ->
    In (h, st) (live_ptrs_with_states gst).
Proof.
  unfold live_ptrs_with_states.
  intros.
  apply FilterMap.filterMap_In with (a:=h).
  - by find_rewrite.
  - by apply live_In_live_ptrs.
Qed.

Lemma phase_two_zero_error_correct :
  forall gst,
    total_pred_and_first_succ_error gst = 0 ->
    preds_and_first_succs_correct gst.
Proof.
  unfold total_pred_and_first_succ_error, preds_and_first_succs_correct.
  intros.
  apply phase_two_zero_error_locally_correct; eauto.
  eapply sum_of_nats_zero_means_all_zero; eauto.
  eapply in_map_iff; exists (h, st); split.
  - auto.
  - apply live_In_live_ptrs_with_states; auto.
    now live_inv.
Qed.

(* This is really an invariant. *)
Lemma phase_two_error_stable :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    continuously
      (consecutive
         (measure_nonincreasing total_pred_and_first_succ_error))
      ex.
Proof.
Admitted.

(* This is the hard part. *)
Lemma phase_two_error_decreasing :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (zero_or_eventually_decreasing total_pred_and_first_succ_error) ex.
Proof.
Admitted.

Lemma phase_two :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    continuously (lift_gpred_to_ex preds_and_first_succs_correct) ex.
Proof.
  intros.
  find_copy_apply_lem_hyp phase_two_error_stable; auto.
  find_copy_apply_lem_hyp phase_two_error_decreasing; auto.
  find_copy_apply_lem_hyp measure_decreasing_to_zero_continuously; auto.
  unfold lift_gpred_to_ex.
  eapply continuously_monotonic.
  - eapply now_monotonic; intros.
    apply phase_two_zero_error_correct.
    eauto using measure_zero_elim.
  - assumption.
Qed.

(** Phase three: all successors become correct. *)
Definition all_in_dec
           {A : Type}
           (A_eq_dec : forall x y : A, {x = y} + {x <> y})
           (l1 l2 : list A) :=
  Forall_dec _ (fun a => In_dec A_eq_dec a l2) l1.

(* doesn't deal with possiblity of length of the successor list being longer
   than SUCC_LIST_LEN *)
Fixpoint succs_error_helper (gst : global_state) (h : pointer) (xs ys : list pointer) (suffix_len : nat) :=
  match ys with
  | [] => suffix_len
  | s :: ys' =>
    let xs' := filter (better_succ_bool h s) (live_ptrs gst) in
    if all_in_dec pointer_eq_dec xs' xs
    then succs_error_helper gst h (s :: xs) ys' (suffix_len - 1)
    else suffix_len
  end.

Definition succs_error (gst : global_state) (h : pointer) (st : data) :=
  succs_error_helper gst h [] (succ_list st) Chord.SUCC_LIST_LEN.

Definition total_succs_error (gst : global_state) :=
  total_measure (succs_error gst) gst.

Definition correct_succs (gst : global_state) (h : pointer) (st : data) : Prop :=
  forall s xs ys s',
    succ_list st = xs ++ s :: ys ->
    ptr_between h s' s ->
    live gst s' ->
    In s' xs.

Definition all_succs_correct (gst : global_state) : Prop :=
  forall h st,
    sigma gst (addr_of h) = Some st ->
    live gst h ->
    correct_succs gst h st /\
    length (succ_list st) = Chord.SUCC_LIST_LEN.

Lemma succs_error_zero_locally_correct :
  forall gst h st,
    succs_error gst h st = 0 ->
    correct_succs gst h st.
Proof.
Admitted.

Theorem phase_three :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    continuously (lift_gpred_to_ex all_succs_correct) ex.
Proof.
Admitted.

Definition ideal (gst : global_state) : Prop :=
  forall h st,
    live gst h ->
    sigma gst (addr_of h) = Some st ->
    correct_succs gst h st /\
    length (succ_list st) = Chord.SUCC_LIST_LEN /\
    pred_correct gst h (pred st).

Theorem phases_locally_sufficient :
  forall gst,
    preds_and_first_succs_correct gst ->
    all_succs_correct gst ->
    ideal gst.
Proof.
  intros gst H_preds H_succs.
  unfold ideal; intros h st.
  specialize (H_preds h st).
  specialize (H_succs h st).
  unfold pred_and_first_succ_correct in *.
  intuition.
Qed.

Definition gpred_and (P Q : global_state -> Prop) (gst : global_state) : Prop :=
  P gst /\ Q gst.

Lemma and_tl_gpred_and_comm :
  forall (P Q : global_state -> Prop) ex,
    lift_gpred_to_ex (gpred_and P Q) ex <->
    (and_tl (lift_gpred_to_ex P) (lift_gpred_to_ex Q)) ex.
Proof.
  unfold lift_gpred_to_ex, lift_gpred_to_occ, gpred_and, and_tl.
  split; intros; destruct ex; simpl in *; tauto.
Qed.

Theorem phases_sufficient :
  forall ex,
    lift_gpred_to_ex
      (gpred_and preds_and_first_succs_correct
                 all_succs_correct)
      ex ->
    lift_gpred_to_ex ideal ex.
Proof.
  unfold lift_gpred_to_ex, lift_gpred_to_occ.
  eapply now_monotonic.
  intros.
  match goal with
  | [ H : gpred_and _ _ _ |- _ ] =>
    destruct H
  end.
  now auto using phases_locally_sufficient.
Qed.

Theorem chord_stabilization :
  forall ex : infseq.infseq occurrence,
    reachable_st (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    continuously
      (lift_gpred_to_ex ideal)
      ex.
Proof.
  intros.
  find_copy_eapply_lem_hyp phase_two; eauto.
  find_copy_eapply_lem_hyp phase_three; eauto.
  eapply continuously_monotonic.
  eapply phases_sufficient.
  eapply continuously_monotonic.
  - intros.
    rewrite and_tl_gpred_and_comm.
    eauto.
  - now apply continuously_and_tl.
Qed.
