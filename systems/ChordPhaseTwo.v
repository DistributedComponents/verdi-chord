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
Require Import Chord.ChordQueryInvariant.
Require Import Chord.ChordLabeled.
Require Import Chord.ChordPromises.
Require Import Chord.ChordDefinitionLemmas.
Require Import Chord.ChordLocalProps.
Require Import Chord.ChordPhaseOne.

Set Bullet Behavior "Strict Subproofs".
Open Scope nat_scope.

Definition live_addrs (gst : global_state) : list addr :=
  filter (fun a => Coqlib.proj_sumbool (live_node_dec gst a))
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

Lemma nonempty_succ_lists_always_belong_to_joined_nodes :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    succ_list st <> [] ->
    joined st = true.
Proof.
Admitted.

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

Lemma live_node_has_Tick_in_timeouts :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    live_node (occ_gst (hd ex)) h ->
    In Tick (timeouts (occ_gst (hd ex)) h).
Proof.
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

(** In phase two we want to talk about the existence and number of better
    predecessors and better first successors to a node. We do this with the
    following functions.
    - better_* : Prop, which holds if a node is closer to h.
    - better_*_bool : bool, which is true if some live node is a better pointer for h.
    - *_correct : Prop, which holds if the pointer is globally correct.
    - *_error : nat, which counts the number of better options for the pointer.
    We prove that error = 0 <-> correct so we can use an argument about the
    measure to prove eventual correctness.
 *)
Definition counting_opt_error (gst : global_state) (p : option pointer) (better_bool : pointer -> pointer -> bool) : nat :=
  match p with
  | Some p0 =>
    if live_node_dec gst (addr_of p0)
    then length (filter (better_bool p0) (live_ptrs gst))
    else length (live_ptrs gst) + 1
  | None => length (live_ptrs gst) + 1
  end.

Lemma live_addr_In_live_addrs :
  forall gst h,
    live_node gst h ->
    In h (live_addrs gst).
Proof.
  unfold live_addrs.
  intros.
  apply filter_In; split.
  - unfold live_node in *; break_and; auto.
  - auto using Coqlib.proj_sumbool_is_true.
Qed.

Lemma In_live_addrs_live :
  forall gst h,
    In h (live_addrs gst) ->
    live_node gst h.
Proof.
  unfold live_addrs.
  intros.
  find_apply_lem_hyp filter_In; break_and.
  eapply Coqlib.proj_sumbool_true; eauto.
Qed.

Lemma live_In_live_ptrs :
  forall gst h,
    live_node gst (addr_of h) ->
    wf_ptr h ->
    In h (live_ptrs gst).
Proof.
  unfold live_ptrs, live_node.
  intros.
  rewrite (wf_ptr_eq h); auto.
  apply in_map.
  now apply live_addr_In_live_addrs.
Qed.

Lemma In_live_ptrs_live :
  forall gst h,
    In h (live_ptrs gst) ->
    live_node gst (addr_of h).
Proof.
  unfold live_ptrs.
  intros.
  apply In_live_addrs_live.
  now find_apply_lem_hyp in_map_iff; expand_def.
Qed.

Lemma not_in_filter_false :
  forall A (f : A -> bool) l x,
    In x l ->
    ~ In x (filter f l) ->
    f x = false.
Proof.
  intros.
  destruct (f x) eqn:?H; [|tauto].
  unfold not in *; find_false.
  now eapply filter_In.
Qed.

Lemma counting_opt_error_zero_implies_correct :
  forall gst p better_bool,
    counting_opt_error gst p better_bool = 0 ->
    exists p0,
      p = Some p0 /\
      forall p',
        live_node gst (addr_of p') ->
        wf_ptr p' ->
        better_bool p0 p' = false.
Proof.
  unfold counting_opt_error.
  intros.
  repeat break_match; try omega.
  eexists; split; eauto.
  find_apply_lem_hyp length_zero_iff_nil.
  intros.
  find_apply_lem_hyp live_In_live_ptrs; eauto.
  eapply not_in_filter_false; eauto.
  find_rewrite.
  apply in_nil.
Qed.

(** Predecessor phase two definitions *)
Definition better_pred (gst : global_state) (h p p' : pointer) : Prop :=
  wf_ptr h /\
  wf_ptr p /\
  wf_ptr p' /\
  live_node gst (addr_of p') /\
  ptr_between p p' h.

Definition better_pred_bool (h p p' : pointer) : bool :=
  ptr_between_bool p p' h.

Definition pred_correct (gst : global_state) (h : pointer) (p : option pointer) : Prop :=
  exists p0,
    p = Some p0 /\
    forall p',
      ~ better_pred gst h p0 p'.

Definition pred_error (gst : global_state) (h : addr) : nat :=
  match sigma gst h with
  | Some st =>
    counting_opt_error gst (pred st) (better_pred_bool (make_pointer h))
  | None =>
    length (active_nodes gst) + 1
  end.

(** First successor phase two definitions *)
Definition better_succ (gst : global_state) (h s s' : pointer) : Prop :=
  wf_ptr h /\
  wf_ptr s /\
  wf_ptr s' /\
  live_node gst (addr_of s') /\
  ptr_between h s' s.

Definition better_succ_bool (h s s' : pointer) : bool :=
  ptr_between_bool h s' s.

Definition first_succ_correct (gst : global_state) (h : pointer) (p : option pointer) : Prop :=
  exists p0,
    p = Some p0 /\
    forall p', ~ better_succ gst h p0 p'.

Definition first_succ_error (gst : global_state) (h : addr) : nat :=
  match sigma gst h with
  | Some st =>
    counting_opt_error gst (hd_error (succ_list st)) (better_succ_bool (make_pointer h))
  | None =>
    length (active_nodes gst) + 1
  end.

(** First successor and predecessor combined phase two definitions *)
Definition pred_and_first_succ_correct (gst : global_state) (h : pointer) (st : data) : Prop :=
  pred_correct gst h (pred st) /\
  first_succ_correct gst h (hd_error (succ_list st)).

Definition pred_and_first_succ_error (h : addr) (gst : global_state) : nat :=
  pred_error gst h + first_succ_error gst h.

Definition phase_two_error : global_state -> nat :=
  global_measure pred_and_first_succ_error.

Definition preds_correct (gst : global_state) : Prop :=
  forall h st,
    live_node gst (addr_of h) ->
    sigma gst (addr_of h) = Some st ->
    wf_ptr h ->
    pred_correct gst h (pred st).

Definition first_succs_correct (gst : global_state) : Prop :=
  forall h st,
    live_node gst (addr_of h) ->
    sigma gst (addr_of h) = Some st ->
    wf_ptr h ->
    first_succ_correct gst h (hd_error (succ_list st)).

Definition preds_and_first_succs_correct (gst : global_state) : Prop :=
  preds_correct gst /\ first_succs_correct gst.

Lemma preds_and_first_succs_correct_intro :
  forall gst,
    (forall h st,
        live_node gst (addr_of h) ->
        sigma gst (addr_of h) = Some st ->
        wf_ptr h ->
        pred_and_first_succ_correct gst h st) ->
    preds_and_first_succs_correct gst.
Proof.
  unfold preds_and_first_succs_correct, preds_correct, first_succs_correct, pred_and_first_succ_correct.
  intros; split;
    intros; find_apply_hyp_hyp; tauto.
Qed.

Definition phase_two (o : occurrence) : Prop :=
  preds_and_first_succs_correct (occ_gst o).

Lemma phase_two_zero_error_has_pred :
  forall gst h st,
    live_node gst (addr_of h) ->
    wf_ptr h ->
    sigma gst (addr_of h) = Some st ->
    pred_and_first_succ_error (addr_of h) gst = 0 ->
    exists p, pred st = Some p /\
         pred_error gst (addr_of h) = 0.
Proof.
  intros.
  rewrite (wf_ptr_eq h); auto.
  unfold pred_and_first_succ_error in *.
  find_apply_lem_hyp plus_is_O; break_and.
  destruct (pred ltac:(auto)) eqn:?H.
  - eexists; intuition eauto.
  - unfold pred_error in *.
    repeat find_rewrite.
    simpl in *; omega.
Qed.

Lemma phase_two_zero_error_has_first_succ :
  forall gst h st,
    live_node gst (addr_of h) ->
    wf_ptr h ->
    sigma gst (addr_of h) = Some st ->
    pred_and_first_succ_error (addr_of h) gst = 0 ->
    exists s rest,
      succ_list st = s :: rest /\
      first_succ_error gst (addr_of h) = 0.
Proof.
  intros.
  rewrite (wf_ptr_eq h); auto.
  unfold pred_and_first_succ_error in *.
  find_apply_lem_hyp plus_is_O; break_and.
  destruct (succ_list ltac:(auto)) eqn:?H.
  - unfold first_succ_error in *.
    repeat find_rewrite.
    simpl in *; omega.
  - repeat eexists; intuition eauto.
Qed.

Lemma better_pred_intro :
  forall gst h p p',
    wf_ptr h ->
    wf_ptr p ->
    wf_ptr p' ->
    live_node gst (addr_of p') ->
    ptr_between p p' h ->
    better_pred gst h p p'.
Proof.
  unfold better_pred.
  tauto.
Qed.

Lemma better_pred_elim :
  forall gst h p p',
    better_pred gst h p p' ->
    wf_ptr h /\
    wf_ptr p /\
    wf_ptr p' /\
    live_node gst (addr_of p') /\
    ptr_between p p' h.
Proof.
  unfold better_pred.
  tauto.
Qed.

Lemma better_pred_bool_true_better_pred :
  forall gst h p p',
    wf_ptr h ->
    wf_ptr p ->
    wf_ptr p' ->
    live_node gst (addr_of p') ->
    better_pred_bool h p p' = true ->
    better_pred gst h p p'.
Proof.
  unfold better_pred_bool.
  intros.
  apply better_pred_intro; auto.
  now apply between_between_bool_equiv.
Qed.

Lemma better_pred_better_pred_bool_true :
  forall gst h p p',
    better_pred gst h p p' ->
    wf_ptr h /\
    wf_ptr p /\
    wf_ptr p' /\
    live_node gst (addr_of p') /\
    better_pred_bool h p p' = true.
Proof.
  intros.
  find_apply_lem_hyp better_pred_elim; intuition.
  now apply between_between_bool_equiv.
Qed.

Lemma better_succ_better_succ_bool_true :
  forall gst h s s',
    better_succ gst h s s' ->
    wf_ptr h /\
    wf_ptr s /\
    wf_ptr s' /\
    live_node gst (addr_of s') /\
    better_succ_bool h s s' = true.
Proof.
  intros.
  inv_prop better_succ; intuition.
  now apply between_between_bool_equiv.
Qed.

Lemma between_bool_false_not_between :
  forall x y z,
    between_bool x y z = false ->
    ~ between x y z.
Proof.
  intuition.
  find_apply_lem_hyp between_between_bool_equiv.
  congruence.
Qed.

Lemma better_succ_bool_false_not_better_succ :
  forall gst h s s',
    better_succ_bool h s s' = false ->
    ~ better_succ gst h s s'.
Proof.
  unfold better_succ_bool, better_succ.
  intuition.
  find_eapply_lem_hyp between_bool_false_not_between; eauto.
Qed.

Lemma phase_two_zero_error_locally_correct :
  forall gst h st,
    live_node gst (addr_of h) ->
    wf_ptr h ->
    sigma gst (addr_of h) = Some st ->
    pred_and_first_succ_error (addr_of h) gst = 0 ->
    pred_and_first_succ_correct gst h st.
Proof.
  intros.
  unfold pred_and_first_succ_correct; split.
  - find_copy_apply_lem_hyp phase_two_zero_error_has_pred; auto.
    break_exists_exists; break_and; split; auto.
    unfold pred_error in *; break_match; try congruence.
    find_apply_lem_hyp counting_opt_error_zero_implies_correct; expand_def.
    find_injection.
    intuition.
    find_eapply_lem_hyp better_pred_better_pred_bool_true; break_and.
    repeat match goal with
           | [ H : forall x : ?T, _, y : ?T |- _ ] =>
             specialize (H y)
           end.
    rewrite <- wf_ptr_eq in *; auto.
    congruence.
  - find_copy_apply_lem_hyp phase_two_zero_error_has_first_succ; auto.
    break_exists_exists; expand_def; split; try find_rewrite; auto.
    unfold first_succ_error in *; break_match; try congruence.
    find_apply_lem_hyp counting_opt_error_zero_implies_correct; expand_def.
    find_injection.
    repeat find_rewrite.
    simpl in *; find_injection.
    intuition.
    find_eapply_lem_hyp better_succ_better_succ_bool_true; break_and.
    repeat match goal with
           | [ H : forall x : ?T, _, y : ?T |- _ ] =>
             specialize (H y)
           end.
    rewrite <- wf_ptr_eq in *; auto.
    congruence.
Qed.

Lemma phase_two_zero_error_correct :
  forall gst,
    phase_two_error gst = 0 ->
    preds_and_first_succs_correct gst.
Proof.
  intros.
  apply preds_and_first_succs_correct_intro; intros.
  apply phase_two_zero_error_locally_correct; eauto.
  eapply sum_of_nats_zero_means_all_zero; eauto.
  apply in_map_iff.
  eexists; split; eauto using live_node_in_active.
Qed.

Definition has_pred (gst : global_state) (h : addr) (p : option pointer) : Prop :=
  exists st,
    sigma gst h = Some st /\
    pred st = p.

Definition has_first_succ (gst : global_state) (h : addr) (s : pointer) : Prop :=
  exists st,
    sigma gst h = Some st /\
    hd_error (succ_list st) = Some s.

Lemma pred_error_bound :
  forall ex h st n,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    sigma (occ_gst (hd ex)) h = Some st ->
    pred_error (occ_gst (hd ex)) h = n ->
    always (now (fun occ => pred_error (occ_gst occ) h <= n)) ex.
Proof.
Admitted.

Lemma first_succ_error_bound :
  forall ex h st n,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    sigma (occ_gst (hd ex)) h = Some st ->
    first_succ_error (occ_gst (hd ex)) h = n ->
    always (now (fun occ => first_succ_error (occ_gst occ) h <= n)) ex.
Proof.
Admitted.

Theorem phase_two_error_continuously_nonincreasing :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    continuously (local_measures_nonincreasing pred_and_first_succ_error) ex.
Proof.
Admitted.

Lemma stabilize_with_better_pred_completes :
  forall ex h dst p succs,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    always (~_ (now circular_wait)) ex ->

    open_stabilize_request_to (occ_gst (hd ex)) h dst ->
    live_node (occ_gst (hd ex)) h ->
    live_node (occ_gst (hd ex)) dst ->

    In (GotPredAndSuccs (Some p) succs) (channel (occ_gst (hd ex)) dst h) ->

    live_node (occ_gst (hd ex)) (addr_of p) ->
    ptr_between (make_pointer h) p (make_pointer dst) ->

    eventually (now (fun occ =>
                       (* don't actually care about the Notify here *)
                       In Notify (channel (occ_gst occ) h (addr_of p)) /\
                       has_first_succ (occ_gst occ) h p))
               ex.
Proof.
Admitted.

Lemma stabilize_with_better_pred_completes' :
  forall ex h dst p succs,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    always (~_ (now circular_wait)) ex ->

    open_stabilize_request_to (occ_gst (hd ex)) h dst ->
    live_node (occ_gst (hd ex)) h ->
    live_node (occ_gst (hd ex)) dst ->

    In (GotPredAndSuccs (Some p) succs) (channel (occ_gst (hd ex)) dst h) ->

    live_node (occ_gst (hd ex)) (addr_of p) ->
    ptr_between (make_pointer h) p (make_pointer dst) ->

    eventually (now (fun occ => has_first_succ (occ_gst occ) h p)) ex.
Proof.
  intros.
  find_apply_lem_hyp stabilize_with_better_pred_completes; auto.
  eapply eventually_monotonic_simple; [|eauto].
  destruct s; now simpl.
Qed.

Lemma stabilize_with_worse_pred_completes :
  forall ex h dst p succs,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    always (~_ (now circular_wait)) ex ->

    open_stabilize_request_to (occ_gst (hd ex)) h dst ->
    live_node (occ_gst (hd ex)) h ->
    live_node (occ_gst (hd ex)) dst ->

    In (GotPredAndSuccs (Some p) succs) (channel (occ_gst (hd ex)) dst h) ->

    In (addr_of p) (failed_nodes (occ_gst (hd ex))) \/
    ~ ptr_between (make_pointer h) p (make_pointer dst) ->

    eventually (now (fun occ =>
                       In Notify (channel (occ_gst occ) h dst) /\
                       has_first_succ (occ_gst occ) h (make_pointer dst)))
               ex.
Proof.
Admitted.

Lemma notify_causes_rectify :
  forall ex h dst st p,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    always (~_ (now circular_wait)) ex ->

    live_node (occ_gst (hd ex)) h ->
    live_node (occ_gst (hd ex)) dst ->
    sigma (occ_gst (hd ex)) dst = Some st ->
    pred st = Some p ->

    ptr_between p (make_pointer h) (make_pointer dst) ->
    In Notify (channel (occ_gst (hd ex)) h dst) ->

    eventually
      (now
         (fun occ =>
            exists h',
              wf_ptr h' /\
              live_node (occ_gst occ) (addr_of h') /\
              better_pred (occ_gst occ) (make_pointer dst) (make_pointer h) h' /\
              open_request_to (occ_gst (hd ex)) dst (addr_of h') Ping))
      ex.
Proof.
Admitted.

Lemma rectify_with_live_pred_sets_pred :
  forall ex h dst st,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    always (~_ (now circular_wait)) ex ->

    live_node (occ_gst (hd ex)) h ->
    live_node (occ_gst (hd ex)) dst ->
    sigma (occ_gst (hd ex)) dst = Some st ->

    (forall p,
        pred st = Some p ->
        better_pred (occ_gst (hd ex)) (make_pointer dst) (make_pointer h) p) ->
    open_request_to (occ_gst (hd ex)) dst h Ping ->
    In Notify (channel (occ_gst (hd ex)) h dst) ->

    eventually
      (now
         (fun occ =>
            has_pred (occ_gst occ) dst (Some (make_pointer h))))
      ex.
Proof.
Admitted.

Definition merge_point (gst : global_state) (a b j : pointer) : Prop :=
  ptr_between a b j /\
  has_first_succ gst (addr_of a) j /\
  has_first_succ gst (addr_of b) j /\
  wf_ptr a /\
  wf_ptr b /\
  wf_ptr j /\
  live_node gst (addr_of a) /\
  live_node gst (addr_of b) /\
  live_node gst (addr_of j).

Definition pred_or_succ_improves (h : pointer) : infseq occurrence -> Prop :=
  consecutive (measure_decreasing (pred_and_first_succ_error (addr_of h))).

Lemma better_pred_eventually_improves_succ :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->

    forall h p s,
      has_first_succ (occ_gst (hd ex)) h s ->
      has_pred (occ_gst (hd ex)) (addr_of s) (Some p) ->
      ptr_between (make_pointer h) p s ->
      eventually (now (fun occ =>
                         open_request_to (occ_gst occ) h (addr_of s) GetPredAndSuccs /\
                         exists p' succs,
                           In (GotPredAndSuccs (Some p') succs) (channel (occ_gst occ) (addr_of s) h) /\
                           (ptr_between p p' s \/ p = p') /\
                           has_pred (occ_gst occ) (addr_of s) (Some p'))) ex ->
      eventually (pred_or_succ_improves (make_pointer h)) ex.
Proof.
Admitted.

Lemma open_stabilize_request_eventually_gets_response :
  forall ex h j,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    wf_ptr j ->
    has_first_succ (occ_gst (hd ex)) h j ->
    open_stabilize_request_to_first_succ (occ_gst (hd ex)) h ->
    eventually
      (now (fun occ =>
              open_request_to (occ_gst occ) h (addr_of j) GetPredAndSuccs /\
              (exists p succs,
                  In (GotPredAndSuccs (Some p) succs)
                     (channel (occ_gst occ) (addr_of j) h) /\
                  has_pred (occ_gst occ) (addr_of j) (Some p))))
      ex.
Proof.
Admitted.

Section MergePoint.
  Variables j a b : pointer.

  Notation "x <=? y" := (unroll_between_ptr (addr_of j) x y) (at level 70).
  Notation "x >=? y" := (unroll_between_ptr (addr_of j) y x) (at level 70).
  Notation "x <? y" := (negb (unroll_between_ptr (addr_of j) y x)) (at level 70).
  Notation "x >? y" := (negb (unroll_between_ptr (addr_of j) x y)) (at level 70).

  (* TODO(ryan): get these two proofs out of here *)
  Lemma unrolling_symmetry_cases :
    forall h x y,
      unroll_between h x y = true ->
      unroll_between h y x = false \/
      unroll_between h y x = true /\ x = y.
  Proof.
    intros.
    destruct (unroll_between h y x) eqn:?H;
      eauto using unrolling_antisymmetric.
  Qed.
  Lemma order_cases_le_gt :
    forall x y,
      x <=? y = true \/ x >? y = true.
  Proof.
    intros.
    unfold unroll_between_ptr in *.
    pose proof unrolling_total (ChordIDParams.hash (addr_of j)) (ptrId x) (ptrId y).
    break_or_hyp.
    - tauto.
    - find_copy_apply_lem_hyp unrolling_symmetry_cases.
      break_or_hyp.
      + right.
        now apply Bool.negb_true_iff.
      + tauto.
  Qed.

  Lemma no_pred_merge_point :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->

      forall st,
        merge_point (occ_gst (hd ex)) a b j ->
        sigma (occ_gst (hd ex)) (addr_of j) = Some st ->
        pred st = None ->
        eventually (pred_or_succ_improves j) ex.
  Proof.
  Admitted.

  Lemma counting_opt_error_depends_on_live_addrs :
    forall gst gst' p bb,
      live_addrs gst' = live_addrs gst ->
      wf_ptr p ->
      counting_opt_error gst (Some p) bb = counting_opt_error gst' (Some p) bb.
  Proof.
    intros.
    unfold counting_opt_error.
    assert (live_ptrs gst = live_ptrs gst')
      by (unfold live_ptrs; now f_equal).
    repeat find_rewrite.
    repeat break_match; try reflexivity.
    - find_apply_lem_hyp live_In_live_ptrs; auto.
      find_rewrite.
      find_apply_lem_hyp In_live_ptrs_live.
      tauto.
    - find_apply_lem_hyp live_In_live_ptrs; auto.
      find_reverse_rewrite.
      find_apply_lem_hyp In_live_ptrs_live.
      tauto.
  Qed.

  Lemma a_before_pred_merge_point_with_stabilize_request :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->

      forall st p,
        merge_point (occ_gst (hd ex)) a b j ->
        sigma (occ_gst (hd ex)) (addr_of j) = Some st ->
        pred st = Some p ->
        a <=? p = true ->
        eventually (pred_or_succ_improves a) ex.
  Proof.
  Admitted.

  Lemma now_hd :
    forall T (P : T -> Prop) ex,
      now P ex ->
      P (hd ex).
  Proof.
    now destruct ex.
  Qed.

  Lemma a_before_pred_merge_point :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->

      forall st p,
        merge_point (occ_gst (hd ex)) a b j ->
        sigma (occ_gst (hd ex)) (addr_of j) = Some st ->
        pred st = Some p ->
        a <=? p = true ->
        eventually (pred_or_succ_improves a) ex.
  Proof.
    intros.
    inv_prop merge_point; break_and.
    assert (has_pred (occ_gst (hd ex)) (addr_of j) (Some p))
      by (eexists; eauto).
    assert (always (now (fun occ => exists p', has_pred (occ_gst occ) (addr_of j) (Some p') /\
                                       (ptr_between p p' j \/ p = p'))) ex)
           by admit.
    assert (eventually (now (fun o => open_stabilize_request_to_first_succ (occ_gst o) (addr_of a))) ex)
      by auto using start_stabilize_with_first_successor_eventually.
    clear H6 H17.
    clear dependent b.
    clear dependent st.
    induction 0 as [ex | o [o' ex]].
    - inv_prop always.
      find_apply_lem_hyp now_hd.
      break_exists; break_and.
      eapply better_pred_eventually_improves_succ; eauto.
      (* something about the unrolling and the regular between relation *)
      { admit. }
      (* shouldn't have to do this *)
      replace (let (_, addr) := a in addr) with (addr_of a)
        by reflexivity.
      find_apply_lem_hyp open_stabilize_request_eventually_gets_response;
        try now destruct ex.
      eapply eventually_monotonic;
        [ | | eapply H18 | eapply H9];
        invar_eauto.
      intros.
      clear dependent ex.
      destruct s; simpl in *.
      repeat break_and.
      split; auto.
      break_exists_exists; break_and.
      split; auto.
      split; auto.
      inv_prop always; simpl in *.
      break_exists; break_and.
      admit.
    - assert (live_node (occ_gst o') (addr_of a))
        by (inv_prop lb_execution; invar_eauto).
      inv_prop live_node; break_and.
      break_exists_name a_st; break_and.
      destruct (hd_error (succ_list a_st)) as [s |] eqn:?H.
      + destruct (pointer_eq_dec s j); subst.
        * apply E_next.
          apply IHeventually;
            invar_eauto.
          eexists; eauto.
        * admit.
      + admit.
  Admitted.

  Lemma a_after_pred_merge_point :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->

      forall st p,
        merge_point (occ_gst (hd ex)) a b j ->
        sigma (occ_gst (hd ex)) (addr_of j) = Some st ->
        pred st = Some p ->
        a >? p = true ->
        eventually (pred_or_succ_improves j) ex.
  Proof.
  Admitted.

  Lemma error_decreases_at_merge_point :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->

      merge_point (occ_gst (hd ex)) a b j ->
      eventually (pred_or_succ_improves a) ex \/
      eventually (pred_or_succ_improves b) ex \/
      eventually (pred_or_succ_improves j) ex.
  Proof.
    intros.
    inv_prop merge_point; break_and.
    inv_prop (live_node (occ_gst (hd ex)) (addr_of j)); expand_def.
    destruct (pred ltac:(auto)) as [p |] eqn:?H.
    - pose proof (order_cases_le_gt a p); break_or_hyp;
        eauto using a_before_pred_merge_point, a_after_pred_merge_point.
    - eauto using no_pred_merge_point.
  Qed.

End MergePoint.

Lemma succ_error_means_merge_point :
  forall gst,
    reachable_st gst ->
    ~ first_succs_correct gst ->
    exists a b j,
      merge_point gst a b j.
Proof.
Admitted.

Definition wrong_pred (gst : global_state) (h : pointer) : Prop :=
  exists st p p',
    sigma gst (addr_of h) = Some st /\
    pred st = Some p /\
    better_pred gst h p p'.

Lemma error_decreases_when_succs_right :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->

    first_succs_correct (occ_gst (hd ex)) ->
    wrong_pred (occ_gst (hd ex)) h ->
    eventually (pred_or_succ_improves h) ex.
Proof.
Admitted.

Lemma error_means_merge_point_or_wrong_pred :
  forall gst,
    phase_two_error gst > 0 ->
    reachable_st gst ->
    all_first_succs_best gst ->

    first_succs_correct gst /\
    (exists h, live_node gst (addr_of h) /\
          wrong_pred gst h) \/
    exists a b j,
      merge_point gst a b j.
Proof.
Admitted.

Lemma continuously_zero_phase_two_error_phase_two :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    continuously (now (measure_zero phase_two_error)) ex ->
    continuously (now phase_two) ex.
Proof.
  intros until 2.
  apply continuously_monotonic.
  intros; destruct s; simpl in *.
  apply phase_two_zero_error_correct; auto.
Qed.

Lemma phase_two_nonzero_error_causes_measure_drop :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ now circular_wait) ex ->
    always (now phase_one) ex ->

    nonzero_error_causes_measure_drop pred_and_first_succ_error ex.
Proof.
  intros; intro.
  assert (all_first_succs_best (occ_gst (hd ex)))
    by (inv_prop always; destruct ex; auto).
  find_apply_lem_hyp error_means_merge_point_or_wrong_pred; auto.
  expand_def.
  - find_eapply_lem_hyp error_decreases_when_succs_right; eauto.
    eexists; eauto using live_node_is_active.
  - inv_prop merge_point; break_and.
    find_apply_lem_hyp error_decreases_at_merge_point; eauto.
    repeat break_or_hyp; eexists; eauto using live_node_is_active.
Qed.

Lemma phase_two_nonzero_error_continuous_drop :
  forall ex : infseq occurrence,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ now circular_wait) ex ->
    always (now phase_one) ex ->
    always (nonzero_error_causes_measure_drop pred_and_first_succ_error) ex.
Proof.
  cofix c.
  intros.
  intros.
  destruct ex.
  constructor.
  - apply phase_two_nonzero_error_causes_measure_drop; auto.
  - simpl.
    apply c; invar_eauto.
Qed.

Lemma phase_two_continuously :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    continuously (now phase_two) ex.
Proof.
  intros.
  eapply continuously_zero_phase_two_error_phase_two; eauto.
  eapply local_measure_causes_measure_zero_continuosly; eauto.
  - eapply phase_two_error_continuously_nonincreasing; eauto.
  - apply E0; eapply phase_two_nonzero_error_continuous_drop; eauto.
Qed.
