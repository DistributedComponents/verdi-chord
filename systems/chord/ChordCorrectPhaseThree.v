Require Import List.
Import ListNotations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import InfSeqExt.infseq.

Require Import Chord.InfSeqTactics.

Require Import Chord.Chord.

Require Import Chord.LabeledLemmas.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.
Require Import Chord.LabeledMeasures.

Require Import Chord.FirstSuccNeverSelf.
Require Import Chord.LiveNodesStayLive.
Require Import Chord.LiveNodesNotClients.
Require Import Chord.NodesHaveState.
Require Import Chord.PredNeverSelfInvariant.
Require Import Chord.PtrCorrectInvariant.
Require Import Chord.QueriesEventuallyStop.
Require Import Chord.QueryInvariant.
Require Import Chord.SuccessorNodesAlwaysValid.
Require Import Chord.ValidPointersInvariant.
Require Import Chord.WfPtrSuccListInvariant.
Require Import Chord.PtrsJoined.

Require Import Chord.ChordCorrectPhaseOne.
Require Import Chord.ChordCorrectPhaseTwo.

Set Bullet Behavior "Strict Subproofs".
Open Scope nat_scope.

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

Definition succs_error (h : addr) (gst : global_state) :=
  match sigma gst h with
  | Some st =>
    if joined st
    then succs_error_helper gst (make_pointer h) [] (succ_list st) Chord.SUCC_LIST_LEN
    else 0
  | None =>
    Chord.SUCC_LIST_LEN + 1
  end.

Definition phase_three_error : global_state -> nat :=
  max_measure succs_error.

Lemma phase_three_error_bounds_node_err :
  forall gst h k,
    In h (active_nodes gst) ->
    phase_three_error gst = k ->
    succs_error h gst <= k.
Proof.
  auto using max_measure_bounds_measures.
Qed.

Definition correct_succs (gst : global_state) (h : pointer) (st : data) : Prop :=
  forall s xs ys s',
    wf_ptr h ->
    succ_list st = xs ++ s :: ys ->
    ptr_between h s' s ->
    live_node gst (addr_of s') ->
    wf_ptr s' ->
    In s' xs.

Definition all_succs_correct (gst : global_state) : Prop :=
  forall h st,
    sigma gst (addr_of h) = Some st ->
    live_node gst (addr_of h) ->
    wf_ptr h ->
    correct_succs gst h st /\
    length (succ_list st) = Chord.SUCC_LIST_LEN.

Lemma length_tl :
  forall A (l : list A),
    length (List.tl l) = List.length l - 1.
Proof.
  intros. induction l; simpl; omega.
Qed.

Lemma succ_list_bounded_by_succ_list_len :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    length (succ_list st) <= SUCC_LIST_LEN.
Proof.
  pose proof succ_list_len_lower_bound.
  intros. induct_reachable_st; intros; simpl in *.
  - find_apply_lem_hyp sigma_initial_st_start_handler; auto.
    subst. unfold start_handler. repeat break_match; simpl; try omega.
    repeat break_match; eauto using length_chop_succs, length_tl.
  - concludes. inv_prop step_dynamic; simpl in *; eauto.
    + update_destruct; subst; rewrite_update; simpl in *; eauto.
      find_inversion. simpl. omega.
    + update_destruct; subst; rewrite_update; simpl in *; eauto.
      find_inversion.
      repeat (handler_def || handler_simpl);
        find_apply_hyp_hyp; repeat find_rewrite; simpl in *; omega.
    + update_destruct; subst; rewrite_update; simpl in *; eauto.
      repeat (handler_def || handler_simpl;
              eauto using length_chop_succs, length_tl).
Qed.

Lemma succs_error_helper_length:
  forall ys gst p xs x,
    x - (succs_error_helper gst p xs ys x) <= length ys.
Proof.
  induction ys; intros; simpl in *; try omega.
  break_if; simpl; try omega.
  match goal with
  | |- context [ succs_error_helper ?gst ?p ?xs ?ys ?x ] =>
    specialize (IHys gst p xs x)
  end. omega.
Qed.

Lemma succs_error_helper_correct_succs:
  forall gst h xs ys s acc x,
    wf_ptr h ->
    wf_ptr s ->
    x = length (xs ++ s :: ys) ->
    succs_error_helper gst h acc (xs ++ s :: ys) x <= 0 ->
    forall s',
      ptr_between h s' s ->
      wf_ptr s' ->
      live_node gst (addr_of s') ->
      (In s' xs \/ In s' acc).
Proof.
  induction xs; intros; simpl in *.
  - right.
    break_if; try omega.
    find_rewrite_lem Forall_forall.
    apply f.
    apply filter_In. intuition; eauto using live_In_live_ptrs.
    find_eapply_lem_hyp better_succ_intro;
      [| | | | eauto]; eauto.
    find_apply_lem_hyp better_succ_better_succ_bool_true. intuition.
  - subst. break_if; try omega. simpl in *.
    rewrite <- minus_n_O in *.
    eapply_prop_hyp succs_error_helper succs_error_helper; eauto. simpl in *. intuition.
Qed.

Lemma phase_three_error_sound :
  forall occ,
    reachable_st (occ_gst occ) ->
    measure_zero phase_three_error occ ->
    all_succs_correct (occ_gst occ).
Proof.
  unfold all_succs_correct. intros.
  unfold measure_zero in *.
  unfold phase_three_error in *.
  find_eapply_lem_hyp max_measure_bounds_measures; eauto using live_node_in_active.
  unfold succs_error in *. find_rewrite.
  find_copy_apply_lem_hyp live_node_joined.
  break_exists. break_and.
  repeat find_rewrite. find_inversion. repeat find_rewrite.
  match goal with
  | |- _ /\ ?len_goal =>
    assert len_goal by (find_apply_lem_hyp succ_list_bounded_by_succ_list_len; auto;
                        match goal with
                        | H : context [ succs_error_helper ?gst ?p ?xs ?ys ?x ] |- _ =>
                          pose proof (succs_error_helper_length ys gst p xs x)
                        end; omega)
  end.
  intuition.
  unfold correct_succs.
  intros. repeat find_rewrite.
  rewrite <- wf_ptr_eq in *; eauto.
  assert (wf_ptr s) by (eapply wf_ptr_succ_list_invariant'; eauto; repeat find_rewrite; in_crush).
  eapply_lem_prop_hyp succs_error_helper_correct_succs succs_error_helper; eauto.
  in_crush.
Qed.

Lemma phase_three_error_continuously_zero_sound :
  forall ex,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    continuously (now (measure_zero phase_three_error)) ex ->
    continuously (now (fun occ => all_succs_correct (occ_gst occ))) ex.
Proof.
  intros.
  induction 0.
  - apply E0.
    generalize dependent s.
    cofix c; intros; constructor; destruct s; cbn in *.
    + find_apply_lem_hyp always_Cons; break_and.
      auto using phase_three_error_sound.
    + apply c; invar_eauto.
  - apply E_next, IHeventually; invar_eauto.
Qed.

Lemma succs_error_nonincreasing :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_two) ex ->
    always (local_measures_nonincreasing succs_error) ex.
Proof.
Admitted.

Lemma phase_three_error_nonincreasing_Cons :
  forall o ex,
    lb_execution (Cons o ex) ->
    reachable_st (occ_gst o) ->
    strong_local_fairness (Cons o ex) ->
    always (~_ now circular_wait) (Cons o ex) ->
    always (now phase_one) (Cons o ex) ->
    always (now phase_two) (Cons o ex) ->
    phase_three_error (occ_gst (hd ex)) <= phase_three_error (occ_gst o).
Proof.
  (* use succs_error_nonincreasing *)
  intros.
  find_eapply_lem_hyp succs_error_nonincreasing; eauto.
  find_eapply_lem_hyp local_always_nonincreasing_causes_max_always_nonincreasing; eauto.
  eapply_lem_prop_hyp always_now succs_error.
  unfold measure_nonincreasing in *. destruct ex. simpl in *. auto.
Qed.

Lemma stabilize_adopt_succs :
  forall s h st p succs gst,
    reachable_st gst ->
    open_request_to gst h s GetPredAndSuccs ->
    sigma gst h = Some st ->
    ~ ptr_between (ptr st) p (make_pointer s) ->
    forall gst' st',
      labeled_step_dynamic gst (RecvMsg s h (GotPredAndSuccs (Some p) succs)) gst' ->
      sigma gst' h = Some st' ->
      succ_list st' = make_succs (make_pointer s) succs.
Proof.
  intros.
  inv_prop open_request_to; expand_def.
  find_copy_eapply_lem_hyp cur_request_valid; eauto.
  unfold valid_ptr in *.
  inv_prop query_request.
  rewrite <- wf_ptr_eq in * |- by tauto.
  invc_labeled_step.
  recover_msg_from_recv_step_equality.
  find_apply_lem_hyp recv_handler_labeling.
  repeat (find_rewrite; try find_injection).
  find_rewrite_lem sigma_ahr_updates; find_injection.
  eapply recv_handler_stabilize_response_pred_worse_sets_succs;
    try erewrite <- wf_ptr_eq by tauto;
    eauto using not_ptr_between.
Qed.

Lemma adopting_succs_decreases_succs_error :
  forall gst h s succs err,
    reachable_st gst ->
    wf_ptr s ->
    live_node gst h ->
    succs_error_helper gst s [] succs Chord.SUCC_LIST_LEN <= S err ->
    has_succs gst h (make_succs s succs) ->
    succs_error h gst <= err.
Proof.
  intros.
  cut (succs_error h gst <= S err - 1); try (intros; omega).
  inv_prop has_succs; break_and.
  unfold succs_error.
  repeat find_rewrite.
  find_apply_lem_hyp live_node_joined; expand_def.
  find_rewrite; find_injection; find_rewrite.
Admitted.

Lemma better_succ_same :
  forall gst l gst' h s s',
    labeled_step_dynamic gst l gst' ->
    better_succ gst h s s' ->
    better_succ gst' h s s'.
Proof.
  intros.
  unfold better_succ in *. intuition. eauto using live_node_invariant.
Qed.

Lemma first_succ_correct_invar :
  forall o ex h s,
    lb_execution (Cons o ex) ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) (Cons o ex) ->
    first_succ_correct (occ_gst o) h (Some s) ->
    first_succ_correct (occ_gst (hd ex)) h (Some s).
Proof.
  intros.
  inv_prop lb_execution. simpl in *. unfold first_succ_correct in *.
  break_exists_exists. intuition.
  find_apply_lem_hyp always_now. simpl in *.
  eapply_prop_hyp better_succ @eq; eauto using better_succ_same.
Qed.

Lemma succs_error_helper_invar :
  forall o ex h succs,
    lb_execution (Cons o ex) ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

    forall k,
      succs_error_helper (occ_gst o) h [] succs Chord.SUCC_LIST_LEN = k ->
      succs_error_helper (occ_gst (hd ex)) h [] succs Chord.SUCC_LIST_LEN = k.
Proof.
  (* relies on the fact that (live_ptrs gst) won't change *)
Admitted.

Lemma stabilize_res_on_wire_eventually_adopt_succs :
  forall s h p succs ex,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    weak_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    ~ ptr_between (make_pointer h) p (make_pointer s) ->
    open_request_to (occ_gst (hd ex)) h s GetPredAndSuccs ->
    In (GotPredAndSuccs (Some p) succs) (channel (occ_gst (hd ex)) s h) ->
    until
      (now (fun o =>
              open_request_to (occ_gst o) h s GetPredAndSuccs /\
              In (GotPredAndSuccs (Some p) succs) (channel (occ_gst o) s h)))
      (now (fun o =>
              has_succs (occ_gst o) h (make_succs (make_pointer s) succs)))
      ex.
Proof.
  intros.
  find_copy_apply_lem_hyp live_node_means_state_exists.
  match goal with
  | H: exists _, sigma (occ_gst (hd ex)) h = Some _ |- _ =>
    destruct H as [x Hst];
      find_copy_eapply_lem_hyp RecvMsg_eventually_occurred;
      eauto using live_node_in_nodes, live_node_not_in_failed_nodes, live_nodes_not_clients;
      assert (exists st, sigma (occ_gst (hd ex)) h = Some st) by eauto;
      clear x Hst
  end.
  match goal with
  | H: eventually _ _ |- _ =>
    induction H as [[o [o' s']]|o [o' s']]
  end.
  - break_exists.
    apply U_next, U0; simpl in *; try tauto.
    assert (live_node (occ_gst o') h)
      by (eapply live_node_invariant; invar_eauto).
    inv_prop occurred.
    inv_prop lb_execution.
    find_reverse_rewrite.
    find_copy_apply_lem_hyp live_node_means_state_exists.
    break_exists_exists; intuition.
    eapply stabilize_adopt_succs; eauto.
    erewrite ptr_correct; eauto.
  - inv_prop lb_execution.
    destruct (label_eq_dec (occ_label o) (RecvMsg s h (GotPredAndSuccs (Some p) succs))).
    + repeat find_rewrite.
      break_exists.
      apply U_next, U0; simpl in *; try tauto.
      assert (live_node (occ_gst o') h)
        by (eapply live_node_invariant; invar_eauto).
      find_copy_apply_lem_hyp live_node_means_state_exists.
      break_exists_exists; intuition.
      eapply stabilize_adopt_succs; eauto.
      erewrite ptr_correct; eauto.
    + apply U_next; simpl; eauto.
      assert (open_request_to (occ_gst o') h s GetPredAndSuccs).
      {
        cbn in *.
        find_eapply_lem_hyp open_request_with_response_on_wire_closed_or_preserved;
          eauto; try now constructor.
        expand_def; congruence.
      }
      assert (In (GotPredAndSuccs (Some p) succs) (channel (occ_gst o') s h)).
      {
        find_eapply_lem_hyp RecvMsg_stays_enabled_after_other_label;
          eauto using when_RecvMsg_enabled.
        inv_prop enabled.
        eauto using recv_implies_msg_in_before.
      }
      apply IHeventually; simpl; invar_eauto.
Qed.

Lemma succs_eventually_adopted_error_eventually_bounded :
  forall h s ex succs err,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    wf_ptr s ->
    live_node (occ_gst (hd ex)) h ->
    first_succ_correct (occ_gst (hd ex)) (make_pointer h) (Some s) ->
    succs_error_helper (occ_gst (hd ex)) s [] succs Chord.SUCC_LIST_LEN <= S err ->
    eventually (now (fun occ => has_succs (occ_gst occ) h (make_succs s succs))) ex ->
    eventually (now (fun occ => succs_error h (occ_gst occ) <= err)) ex.
Proof.
  intros.
  induction 0 as [[o ex]|? ex].
  - simpl in *.
    apply E0.
    eapply adopting_succs_decreases_succs_error; eauto.
  - apply E_next, IHeventually; invar_eauto.
    + eapply first_succ_correct_invar; invar_eauto.
    + erewrite succs_error_helper_invar; invar_eauto.
Qed.

Lemma stabilize_res_on_wire_eventually_err_bounded :
  forall ex,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    weak_local_fairness ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

    forall h p s err succs,
      live_node (occ_gst (hd ex)) h ->
      wf_ptr s ->

      (* for adoption of succ pointer to happen *)
      ~ ptr_between (make_pointer h) p s ->
      open_request_to (occ_gst (hd ex)) h (addr_of s) GetPredAndSuccs ->
      In (GotPredAndSuccs (Some p) succs) (channel (occ_gst (hd ex)) (addr_of s) h) ->

      (* for doing that to actually improve things *)
      first_succ_correct (occ_gst (hd ex)) (make_pointer h) (Some s) ->
      succs_error_helper (occ_gst (hd ex)) s [] succs Chord.SUCC_LIST_LEN <= S err ->

      eventually (now (fun occ => succs_error h (occ_gst occ) <= err)) ex.
Proof.
  intros.
  find_apply_lem_hyp stabilize_res_on_wire_eventually_adopt_succs; eauto;
    rewrite <- !wf_ptr_eq in *; auto.
  eapply succs_eventually_adopted_error_eventually_bounded;
    eauto using until_eventually.
Qed.

Lemma has_succ_has_pred_inv :
  forall gst h s,
    reachable_st gst ->
    preds_and_first_succs_correct gst ->
    wf_ptr h ->
    wf_ptr s ->
    has_first_succ gst (addr_of h) s ->
    has_pred gst (addr_of s) (Some h).
Proof.
  intros.
  unfold preds_and_first_succs_correct, preds_correct, first_succs_correct in *.
  break_and.
  assert (live_node gst (addr_of h)) by admit.
  assert (live_node gst (addr_of s)) by admit.
  assert (first_succ_correct gst h (Some s)).
  {
    inv_prop has_first_succ; break_and.
    repeat find_reverse_rewrite; eauto.
  }
  assert (pred_correct gst s (Some h)).
  {
    invcs_prop first_succ_correct.
    break_and; find_injection.
    exists h; split; auto.
    intuition eauto using better_succ_better_pred.
    eapply better_succ_better_pred; eauto.
    { admit. }
    destruct (pointer_eq_dec x p').
    - admit.
    - eauto.
  }
  unfold has_pred.
  inv_prop live_node; expand_def.
  eexists; split; eauto.
  assert (pred_correct gst s (pred x)) by eauto.
  destruct (pred x);
    try solve [inv_prop pred_correct; break_and; congruence].
  f_equal; symmetry; eapply correct_pred_unique; eauto.
  { admit. }
  inv_prop pred_correct; break_and.
  find_injection.
  admit.
Admitted.

Lemma stabilize_res_after_phase_two_now :
  forall gst err,
    reachable_st gst ->
    phase_three_error gst <= err ->
    preds_and_first_succs_correct gst ->
    forall h s,
      live_node gst (addr_of s) ->
      wf_ptr s ->
      has_first_succ gst h s ->
      open_request_to gst h (addr_of s) GetPredAndSuccs ->
      forall p succs,
        In (GotPredAndSuccs p succs) (channel gst (addr_of s) h) ->
        has_pred gst (addr_of s) p ->
        has_succs gst (addr_of s) succs ->
        exists succs,
          succs_error_helper gst s [] succs Chord.SUCC_LIST_LEN <= err /\
          open_request_to gst h (addr_of s) GetPredAndSuccs /\
          In (GotPredAndSuccs (Some (make_pointer h)) succs) (channel gst (addr_of s) h).
Proof.
  intros.
  simpl in *; expand_def.
  repeat find_apply_lem_hyp always_Cons; break_and.
  unfold phase_two in *; simpl in *.
  match goal with
  | H : has_first_succ _ h _ |- _ =>
    change h with (addr_of (make_pointer h)) in H;
      copy_eapply has_succ_has_pred_inv H;
      eauto using make_pointer_wf
  end.
  find_has_pred_eq; subst; simpl.
  eexists; intuition eauto.
  assert (succs_error (addr_of s) gst <= phase_three_error gst)
    by auto using live_node_in_active, phase_three_error_bounds_node_err.
  unfold succs_error in *.
  inv_prop live_node; expand_def.
  invcs_prop has_succs; expand_def.
  repeat (find_rewrite; try find_injection).
  rewrite <- !(wf_ptr_eq s) in * by assumption.
  omega.
Qed.

Lemma stabilize_res_after_phase_two :
  forall ex h s err,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    strong_local_fairness ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    always (now phase_one) ex ->
    always (now phase_two) ex ->
    always (~_ now circular_wait) ex ->

    live_node (occ_gst (hd ex)) h ->
    live_node (occ_gst (hd ex)) (addr_of s) ->
    wf_ptr s ->
    has_first_succ (occ_gst (hd ex)) h s ->
    (forall p succs, ~ In (GotPredAndSuccs p succs) (channel (occ_gst (hd ex)) (addr_of s) h)) ->

    open_request_to (occ_gst (hd ex)) h (addr_of s) GetPredAndSuccs ->
    phase_three_error (occ_gst (hd ex)) <= S err ->

    until
      (fun ex =>
         open_request_to (occ_gst (hd ex)) h (addr_of s) GetPredAndSuccs)
      (fun ex =>
         exists succs,
           succs_error_helper (occ_gst (hd ex)) s [] succs Chord.SUCC_LIST_LEN <= S err /\
           open_request_to (occ_gst (hd ex)) h (addr_of s) GetPredAndSuccs /\
           In (GotPredAndSuccs (Some (make_pointer h)) succs) (channel (occ_gst (hd ex)) (addr_of s) h))
      ex.
Proof.
  intros.
  find_copy_apply_lem_hyp open_stabilize_request_until_response; eauto.
  induction 0 as [[o ex]|o [o' ex]].
  - apply U0.
    simpl in *; expand_def.
    eapply stabilize_res_after_phase_two_now; eauto.
  - simpl in *.
    break_and.
    apply U_next; [tauto|].
    match goal with
    | H : until _ _ _ |- _ =>
      apply until_Cons in H;
        expand_def
    end.
    + apply U0.
      simpl in *; expand_def.
      eapply stabilize_res_after_phase_two_now; invar_eauto.
      find_apply_lem_hyp phase_three_error_nonincreasing_Cons; auto.
      simpl in *; omega.
    + apply IHuntil; invar_eauto.
      * eapply has_first_succ_stable; invar_eauto.
      * simpl in *; break_and; eauto.
      * simpl in *; break_and; eauto.
      * find_apply_lem_hyp phase_three_error_nonincreasing_Cons; invar_eauto.
        simpl in *; omega.
Qed.

Lemma first_succ_correct_phase_two :
  forall o h s,
    phase_two o ->
    has_first_succ (occ_gst o) h s ->
    live_node (occ_gst o) h ->
    first_succ_correct (occ_gst o) (make_pointer h) (Some s).
Proof.
  unfold phase_two, preds_and_first_succs_correct, first_succs_correct.
  intros.
  break_and.
  inv_prop has_first_succ; expand_def.
  find_reverse_rewrite.
  auto using make_pointer_wf.
Qed.

Lemma stabilize_res_after_phase_two_to_err_drop :
  forall ex h s err,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    strong_local_fairness ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    always (now phase_one) ex ->
    always (now phase_two) ex ->
    always (~_ now circular_wait) ex ->

    live_node (occ_gst (hd ex)) h ->
    live_node (occ_gst (hd ex)) (addr_of s) ->
    wf_ptr s ->
    has_first_succ (occ_gst (hd ex)) h s ->

    open_request_to (occ_gst (hd ex)) h (addr_of s) GetPredAndSuccs ->
    (forall p succs, ~ In (GotPredAndSuccs p succs) (channel (occ_gst (hd ex)) (addr_of s) h)) ->
    phase_three_error (occ_gst (hd ex)) <= S err ->

    eventually (now (fun occ => succs_error h (occ_gst occ) <= err)) ex.
Proof.
  intros.
  find_copy_apply_lem_hyp (stabilize_res_after_phase_two ex h s); auto.
  match goal with
  | H: context[~ In _ (channel _ _ _)] |- _ => clear H
  end.
  induction 0 as [[o ex]|o [o' ex]].
  - expand_def.
    eapply stabilize_res_on_wire_eventually_err_bounded;
      eauto using not_between_xxy, strong_local_fairness_weak.
    apply first_succ_correct_phase_two; eauto.
    change _ with (now phase_two (Cons o ex)).
    apply always_Cons; eauto.
  - apply E_next.
    find_apply_lem_hyp until_Cons; expand_def.
    + eapply stabilize_res_on_wire_eventually_err_bounded;
        eauto using not_between_xxy, strong_local_fairness_weak, weak_local_fairness_invar;
        invar_eauto.
      apply first_succ_correct_phase_two; invar_eauto.
      * change _ with (now phase_two (Cons o' ex)).
        apply always_Cons; invar_eauto.
      * eapply has_first_succ_stable; invar_eauto.
    + apply IHuntil; invar_eauto.
      * eapply has_first_succ_stable; invar_eauto.
      * find_apply_lem_hyp phase_three_error_nonincreasing_Cons; invar_eauto.
        simpl in *; omega.
Qed.

Lemma first_succs_correct_succs_nonempty :
  forall gst,
    first_succs_correct gst ->
    forall h,
      live_node gst h ->
      exists st_h s os,
        sigma gst h = Some st_h /\
        succ_list st_h = s :: os.
Proof.
  intros.
  assert (exists st, sigma gst h = Some st)
    by eauto using live_node_means_state_exists.
  break_exists_name st.
  assert (first_succ_correct gst (make_pointer h) (hd_error (succ_list st)))
    by auto using make_pointer_wf.
  inv_prop first_succ_correct; break_and.
  find_copy_apply_lem_hyp hd_error_tl_exists.
  break_exists.
  eauto.
Qed.

Lemma phase_two_first_succs_correct :
  forall o,
    phase_two o ->
    first_succs_correct (occ_gst o).
Proof.
  now unfold phase_two, preds_and_first_succs_correct.
Qed.

Lemma all_measures_drop_when_succs_error_nonzero :
  forall ex err,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_two) ex ->
    always (now phase_one) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    always (local_measures_nonincreasing succs_error) ex ->

    phase_three_error (occ_gst (hd ex)) = S err ->
    forall h,
      live_node (occ_gst (hd ex)) h ->
      eventually (now (fun occ => succs_error h (occ_gst occ) <= err)) ex.
Proof.
  intros.
  find_apply_lem_hyp Nat.eq_le_incl.
  find_copy_apply_lem_hyp start_stabilize_with_first_successor_eventually; auto.
  induction 0 as [[o ex]|o [o' ex]].
  - simpl in *.
    assert (exists st_h s os, sigma (occ_gst o) h = Some st_h /\ succ_list st_h = s :: os).
    {
      repeat find_apply_lem_hyp always_Cons;
        simpl in *.
      apply first_succs_correct_succs_nonempty;
        intuition eauto using always_Cons, phase_two_first_succs_correct.
    }
    break_exists_name st_h.
    break_exists_name s.
    break_exists_name old_succs.
    break_and.
    assert (has_first_succ (occ_gst o) h s).
    {
        eapply has_first_succ_intro; eauto.
        now repeat find_rewrite.
    }
    assert (live_node (occ_gst o) (addr_of s)).
    {
      repeat find_apply_lem_hyp always_Cons;
        simpl in *.
      intuition eauto using successors_are_live_nodes, phase_two_first_succs_correct.
    }
    assert (exists st_s s' succs, sigma (occ_gst o) (addr_of s) = Some st_s /\ succ_list st_s = s' :: succs).
    {
      repeat find_apply_lem_hyp always_Cons;
        simpl in *.
      intuition eauto using phase_two_first_succs_correct, first_succs_correct_succs_nonempty.
    }
    break_exists_name st_s.
    break_exists_name s'.
    break_exists_name succs.
    break_and.
    assert (wf_ptr s) by eauto using wf_ptr_succ_list_invariant.
    eapply (stabilize_res_after_phase_two_to_err_drop (Cons o ex) h s err);
      eauto.
    admit.
  - apply E_next, IHeventually; invar_eauto.
    find_apply_lem_hyp local_always_nonincreasing_causes_max_always_nonincreasing; invar_eauto.
    find_apply_lem_hyp always_now.
    unfold measure_nonincreasing in *.
    cbn in *.
    unfold phase_three_error in *.
    omega.
Admitted.

Lemma not_joined_zero_succs_error :
  forall gst h st,
    sigma gst h = Some st ->
    joined st = false ->
    succs_error h gst = 0.
Proof.
  unfold succs_error.
  intros.
  now repeat find_rewrite.
Qed.

Lemma always_all_measures_drop_when_succs_error_nonzero :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    always (now phase_two) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

    always (local_measures_nonincreasing succs_error) ex ->
    always (max_measure_nonzero_eventually_all_locals_below succs_error) ex.
Proof.
  cofix c; intros.
  constructor; destruct ex.
  - unfold max_measure_nonzero_eventually_all_locals_below in *.
    intros.
    find_copy_apply_lem_hyp in_active_in_nodes.
    find_eapply_lem_hyp nodes_have_state; invar_eauto.
    break_exists_name st.
    destruct (joined st) eqn:?.
    + eapply all_measures_drop_when_succs_error_nonzero; invar_eauto.
      eapply live_node_characterization; eauto using in_active_in_nodes, in_active_not_failed.
    + apply E0; simpl.
      replace (succs_error _ _) with 0;
        eauto using not_joined_zero_succs_error, eq_sym with arith.
  - eapply c; invar_eauto.
Qed.

Lemma phase_three_error_to_zero :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    always (now phase_two) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    continuously (now (measure_zero phase_three_error)) ex.
Proof.
  intros.
  eapply local_measure_causes_max_measure_zero;
    auto using always_all_measures_drop_when_succs_error_nonzero,
               succs_error_nonincreasing.
Qed.

Theorem phase_three_with_extra_hyps :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    always (now phase_two) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    continuously (now (fun occ => all_succs_correct (occ_gst occ))) ex.
Proof.
  intros.
  find_copy_apply_lem_hyp phase_three_error_to_zero; auto.
  apply phase_three_error_continuously_zero_sound; auto.
Qed.

Theorem phase_three :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    continuously (now (fun occ => all_succs_correct (occ_gst occ))) ex.
Proof.
  intros.
  find_copy_apply_lem_hyp phase_one_continuously; auto.
  find_copy_apply_lem_hyp phase_two_without_phase_one; auto.
  find_copy_apply_lem_hyp joins_stop; auto.
  repeat find_continuously_and_tl.
  induction 0.
  - repeat (rewrite -> !always_and_tl_eq in *;
            match goal with
            | H: (_ /\_ always _) _ |- _ => destruct H
            end).
    now apply phase_three_with_extra_hyps.
  - apply E_next, IHeventually;
      invar_eauto.
Qed.
