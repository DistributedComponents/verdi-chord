Require Import List.
Import ListNotations.
Require Import Omega.

Require Verdi.Coqlib.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.

Require Import InfSeqExt.infseq.

Require Import Chord.InfSeqTactics.

Require Import Chord.Chord.
Require Import Chord.ChordPromises.

Require Import Chord.ChordLabeledLemmas.
Require Import Chord.ChordHandlerLemmas.
Require Import Chord.ChordSystemLemmas.
Require Import Chord.ChordSystemReachable.
Require Import Chord.ChordLabeledMeasures.

Require Import Chord.ValidPointersInvariant.

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
    live_node gst (addr_of h) ->
    wf_ptr h ->
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
  destruct H_preds as [H_preds _].
  specialize (H_preds h st).
  specialize (H_succs h st).
  tauto.
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

Lemma phase_two_without_phase_one :
  forall ex : infseq occurrence,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ now circular_wait) ex ->
    continuously (now phase_two) ex.
Proof.
  intros.
  find_copy_eapply_lem_hyp phase_one_continuously; eauto.
  apply eventually_idempotent.
  lift_eventually phase_two_continuously.
  - intros.
    unfold and_tl in *; break_and.
    repeat (split; invar_eauto).
  - firstorder.
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
  find_copy_eapply_lem_hyp phase_two_without_phase_one; eauto.
  find_copy_eapply_lem_hyp phase_three; eauto.
  eapply continuously_monotonic.
  eapply phases_sufficient.
  eapply continuously_monotonic.
  - intros.
    rewrite and_tl_gpred_and_comm.
    eauto.
  - apply continuously_and_tl; eauto.
Qed.
