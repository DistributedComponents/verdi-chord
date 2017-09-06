Require Import List.
Import ListNotations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Update.

Require Import InfSeqExt.infseq.

Require Import Chord.InfSeqTactics.

Require Import Chord.Chord.

Require Import Chord.LabeledLemmas.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.
Require Import Chord.LabeledMeasures.

Require Import Chord.ValidPointersInvariant.
Require Import Chord.PredNeverSelfInvariant.
Require Import Chord.FirstSuccNeverSelf.
Require Import Chord.QueriesEventuallyStop.
Require Import Chord.QueryInvariant.

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
    succs_error_helper gst (make_pointer h) [] (succ_list st) Chord.SUCC_LIST_LEN
  | None =>
    Chord.SUCC_LIST_LEN + 1
  end.

Definition phase_three_error : global_state -> nat :=
  max_measure succs_error.

Definition correct_succs (gst : global_state) (h : pointer) (st : data) : Prop :=
  forall s xs ys s',
    wf_ptr h ->
    succ_list st = xs ++ s :: ys ->
    ptr_between h s' s ->
    live_node gst (addr_of s') ->
    In s' xs.

Definition all_succs_correct (gst : global_state) : Prop :=
  forall h st,
    sigma gst (addr_of h) = Some st ->
    live_node gst (addr_of h) ->
    wf_ptr h ->
    correct_succs gst h st /\
    length (succ_list st) = Chord.SUCC_LIST_LEN.

Lemma phase_three_error_sound :
  forall occ,
    reachable_st (occ_gst occ) ->
    measure_zero phase_three_error occ ->
    all_succs_correct (occ_gst occ).
Proof.
Admitted.

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

Definition has_succs (gst : global_state) (h : addr) (succs : list pointer) :=
  exists st,
    sigma gst h = Some st /\
    succ_list st = succs.

Lemma has_succs_intro :
  forall gst h succs st,
    sigma gst h = Some st ->
    succ_list st = succs ->
    has_succs gst h succs.
Proof.
  eexists; eauto.
Qed.

Lemma p_before_a_stabilization_adopts_succ_list :
  forall ex h s succs,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    always (now phase_two) ex ->
    has_first_succ (occ_gst (hd ex)) h s ->
    has_succs (occ_gst (hd ex)) (addr_of s) succs ->
    open_request_to (occ_gst (hd ex)) h (addr_of s) GetPredAndSuccs ->
    eventually (now (fun occ => has_succs (occ_gst occ) h (make_succs s succs))) ex.
Proof.
Admitted.

Lemma adopting_succs_decrements_error :
  forall gst h s succs err,
    reachable_st gst ->
    wf_ptr s ->
    wf_ptr h ->
    succs_error_helper gst s [] succs Chord.SUCC_LIST_LEN = err ->
    succs_error_helper gst h [] (make_succs s succs) Chord.SUCC_LIST_LEN = err - 1.
Proof.
Admitted.

Lemma adopting_succs_decreases_error_bound :
  forall gst h s succs err,
    reachable_st gst ->
    wf_ptr s ->
    wf_ptr h ->
    succs_error_helper gst s [] succs Chord.SUCC_LIST_LEN <= err ->
    succs_error_helper gst h [] (make_succs s succs) Chord.SUCC_LIST_LEN <= err - 1.
Proof.
  intros.
  erewrite adopting_succs_decrements_error by eauto.
  omega.
Qed.

Lemma all_measures_drop_when_succs_error_nonzero :
  forall ex err,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_two) ex ->
    phase_three_error (occ_gst (hd ex)) = S err ->
    forall h,
      live_node (occ_gst (hd ex)) h ->
      eventually (now (fun occ => succs_error h (occ_gst occ) <= err)) ex.
Proof.
  intros.
  find_copy_apply_lem_hyp start_stabilize_with_first_successor_eventually; auto.
  induction 0 as [[o ex]|].
  - simpl in *.
    assert (first_succ_is_best_succ (occ_gst o) h).
    {
      admit.
    }
    unfold first_succ_is_best_succ in *.
    break_exists_name st_h.
    break_exists_name s.
    break_exists_name old_succs.
    break_and.
    assert (first_succ_is_best_succ (occ_gst o) (addr_of s)).
    {
      admit.
    }
    break_exists_name st_s.
    break_exists_name s'.
    break_exists_name succs.
    break_and.
    pose proof (p_before_a_stabilization_adopts_succ_list (Cons o ex) h s succs) as Hadopts.
    specialize (Hadopts ltac:(eauto) H).
    forwards; eauto; concludes.
    forwards.
    eapply has_first_succ_intro; eauto.
    find_rewrite. reflexivity.
    concludes.
    forwards.
    eapply has_succs_intro; eauto.
    kjkj
    forwards; auto; concludes.

    forwards; auto; concludes.
    assert (succs_error 
    unfold open_stabilize_request_to_first_succ in *.
    find_copy_apply_lem_hyp live_node_means_state_exists.
    inv_prop live_node; expand_def.
    concludes.
  find_copy_apply_lem_hyp 
  find_copy_apply_lem_hyp (loaded_Tick_inf_often ex h); auto.

Admitted.

Lemma always_all_measures_drop_when_succs_error_nonzero :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (max_measure_nonzero_all_measures_drop succs_error) ex.
Proof.
  cofix c; intros.
  constructor; destruct ex.
  - unfold max_measure_nonzero_all_measures_drop.
    eauto using all_measures_drop_when_succs_error_nonzero.
  - eapply c; invar_eauto.
Qed.
Hint Resolve always_all_measures_drop_when_succs_error_nonzero.

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
Hint Resolve succs_error_nonincreasing.

Lemma phase_three_error_to_zero :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_two) ex ->
    continuously (now (measure_zero phase_three_error)) ex.
Proof.
  intros.
  eapply local_measure_causes_max_measure_zero; auto.
Qed.

Theorem phase_three_with_phase_two :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_two) ex ->
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
  find_copy_apply_lem_hyp phase_two_without_phase_one; auto.
  induction 0.
  - now apply phase_three_with_phase_two.
  - apply E_next, IHeventually; invar_eauto.
Qed.
