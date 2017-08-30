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
Require Import Chord.QueriesEventuallyStop.

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

Lemma all_measures_drop_when_succs_error_nonzero :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    phase_three_error (occ_gst (hd ex)) > 0 ->
    forall h,
      In h (active_nodes (occ_gst (hd ex))) ->
      eventually (consecutive (measure_decreasing (succs_error h))) ex.
Proof.
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
