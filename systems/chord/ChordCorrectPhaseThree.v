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

Lemma adopting_succs_decreases_succs_error_helper :
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

Lemma adopting_succs_decreases_succs_error :
  forall gst h s succs err,
    reachable_st gst ->
    wf_ptr s ->
    succs_error_helper gst s [] succs Chord.SUCC_LIST_LEN <= S err ->
    has_succs gst h (make_succs s succs) ->
    succs_error h gst <= err.
Proof.
  intros.
  cut (succs_error h gst <= S err - 1); try (intros; omega).
  inv_prop has_succs; break_and.
  unfold succs_error.
  repeat find_rewrite.
  apply adopting_succs_decreases_succs_error_helper; eauto.
  apply make_pointer_wf.
Qed.

Lemma first_succ_correct_invar :
  forall o ex h s,
    lb_execution (Cons o ex) ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    first_succ_correct (occ_gst o) h (Some s) ->
    first_succ_correct (occ_gst (hd ex)) h (Some s).
Proof.
  (* relies on the fact that when nodes aren't joining, better_succ is preserved *)
Admitted.

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

Lemma succs_eventually_adopted_error_eventually_bounded :
  forall h s ex succs err,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    wf_ptr s ->
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

Lemma all_measures_drop_when_succs_error_nonzero :
  forall ex err,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_two) ex ->
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
    unfold first_succ_is_best_succ in *.
    break_exists_name st_s.
    break_exists_name s'.
    break_exists_name succs.
    break_and.
    assert (eventually (now (fun occ : occurrence => has_succs (occ_gst occ) h (make_succs s (s' :: succs)))) (Cons o ex)).
    {
      apply p_before_a_stabilization_adopts_succ_list; auto.
      - eapply has_first_succ_intro; eauto.
        find_rewrite; auto.
      - eauto using has_succs_intro.
      - unfold open_stabilize_request_to_first_succ, open_stabilize_request_to in *.
        simpl.
        cut (In GetPredAndSuccs (channel (occ_gst o) h (addr_of s)) /\
             open_request_to (occ_gst o) h (addr_of s) GetPredAndSuccs);
          tauto || eauto.
    }
    assert (wf_ptr s) by admit.
    eapply succs_eventually_adopted_error_eventually_bounded;
      eauto using has_succs_intro.
    + inv_prop phase_two.
      simpl in *.
      inv_prop (phase_two o).
      unfold first_succs_correct in *.
      replace (Some s) with (hd_error (succ_list st_h)) by (find_rewrite; reflexivity).
      eauto using make_pointer_wf.
    + remember (succs_error (addr_of s) (occ_gst o)) as e eqn:He; symmetry in He.
      assert (e <= S err) by admit.
      unfold succs_error in *.
      rewrite <- wf_ptr_eq in * by auto.
      repeat find_rewrite.
      simpl (occ_gst (hd (Cons o ex))).
      omega.
  - apply E_next, IHeventually; invar_eauto.
    find_apply_lem_hyp local_always_nonincreasing_causes_max_always_nonincreasing; invar_eauto.
    find_apply_lem_hyp always_now.
    unfold measure_nonincreasing in *.
    cbn in *.
    unfold phase_three_error in *.
    omega.
Admitted.

Lemma always_all_measures_drop_when_succs_error_nonzero :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_two) ex ->
    always (local_measures_nonincreasing succs_error) ex ->
    always (max_measure_nonzero_eventually_all_locals_below succs_error) ex.
Proof.
  cofix c; intros.
  constructor; destruct ex.
  - unfold max_measure_nonzero_eventually_all_locals_below in *.
    intros.
    eapply all_measures_drop_when_succs_error_nonzero; invar_eauto.
    admit.
    admit.
  - eapply c; invar_eauto.
Admitted.

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
  eapply local_measure_causes_max_measure_zero;
    auto using always_all_measures_drop_when_succs_error_nonzero,
               succs_error_nonincreasing.
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
