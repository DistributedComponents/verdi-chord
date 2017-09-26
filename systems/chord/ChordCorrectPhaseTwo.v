Require Import List.
Import ListNotations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import InfSeqExt.infseq.

Require Import Chord.InfSeqTactics.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Set Bullet Behavior "Strict Subproofs".

Require Import Chord.Chord.

Require Import Chord.LabeledLemmas.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.
Require Import Chord.LabeledMeasures.

Require Import Chord.LiveNodesNotClients.
Require Import Chord.ValidPointersInvariant.
Require Import Chord.QueryInvariant.
Require Import Chord.NodesAlwaysHaveLiveSuccs.
Require Import Chord.PtrCorrectInvariant.
Require Import Chord.QueriesEventuallyStop.
Require Import Chord.FirstSuccNeverSelf.
Require Import Chord.PredNeverSelfInvariant.

Require Import Chord.ChordCorrectPhaseOne.

Open Scope nat_scope.

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
    if live_node_bool gst (addr_of p0)
    then length (filter (better_bool p0) (live_ptrs gst))
    else S (length (live_ptrs gst))
  | None => S (length (live_ptrs gst))
  end.

Lemma counting_opt_error_zero_implies_correct :
  forall gst p better_bool,
    (forall x y, id_of x <> id_of y -> better_bool x y = false -> better_bool y x = true) ->
    wf_ptr p ->
    counting_opt_error gst (Some p) better_bool = 0 ->
    forall p',
      p <> p' ->
      live_node gst (addr_of p') ->
      wf_ptr p' ->
      better_bool p' p = true.
Proof.
  unfold counting_opt_error.
  intros.
  repeat break_match; try omega.
  find_apply_lem_hyp length_zero_iff_nil.
  find_apply_lem_hyp live_In_live_ptrs; eauto.
  find_eapply_prop better_bool.
  {
    intro.
    unfold not in *; find_false.
    cut (addr_of p = addr_of p').
    {
      intros.
      destruct p as [a i], p' as [a' i']; simpl in *.
      congruence.
    }
    apply Chord.hash_inj.
    now rewrite !wf_ptr_hash_eq; auto.
  }
  eapply not_in_filter_false; eauto.
  find_rewrite.
  apply in_nil.
Qed.

Lemma length_filter_by_cmp_same_eq :
  forall A (l : list A) cmp x y,
    (forall a b c, In a l -> In b l -> In c l ->
              cmp a b = true ->
              cmp b c = true ->
              cmp a c = true) ->
    (forall a b, In a l -> In b l ->
            cmp a b = true ->
            cmp b a = true ->
            a = b) ->
    In x l ->
    In y l ->
    length (filter (cmp x) l) = length (filter (cmp y) l) ->
    x = y.
Proof.
(*
If we filter a list by comparing to two different elements, both of which are in
the list, and get two lists of the same length, then the elements are the same.

This is probably not that hard but it's not worth doing until
counting_opt_error_inj is done.

DIFFICULTY: 2
USED: In the proof of counting_opt_error_inj, which isn't currently used
      anywhere else.
*)
Admitted.

Lemma counting_opt_error_inj :
  forall gst cmp x y l,
    l = live_ptrs gst ->
    (forall a b c, In a l -> In b l -> In c l ->
              cmp a b = true ->
              cmp b c = true ->
              cmp a c = true) ->
    (forall a b, In a l -> In b l ->
            cmp a b = true ->
            cmp b a = true ->
            a = b) ->
    wf_ptr x ->
    wf_ptr y ->
    counting_opt_error gst (Some x) cmp = counting_opt_error gst (Some y) cmp ->
    x = y \/ ~ live_node gst (addr_of x) /\ ~ live_node gst (addr_of y).
Proof.
  unfold counting_opt_error.
  intros.
  subst.
  pose proof (filter_length_bound (cmp x) (live_ptrs gst)).
  pose proof (filter_length_bound (cmp y) (live_ptrs gst)).
  repeat break_match;
    try solve [eauto with zarith | tauto].
  - left.
    apply live_node_equiv_live_node_bool in Heqb.
    apply live_node_equiv_live_node_bool in Heqb0.
    eauto using length_filter_by_cmp_same_eq, live_In_live_ptrs.
  - right.
    move/negP/live_node_equiv_live_node_bool: Heqb => H_l.
    move/negP/live_node_equiv_live_node_bool: Heqb0 => H_l'.
    by split.
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
      p' <> p0 ->
      live_node gst (addr_of p') ->
      wf_ptr p' ->
      better_pred gst h p' p0.

Definition pred_error (h : addr) (gst : global_state) : nat :=
  match sigma gst h with
  | Some st =>
    counting_opt_error gst (pred st) (better_pred_bool (make_pointer h))
  | None =>
    S (S (length (active_nodes gst)))
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
    forall p',
      p' <> p0 ->
      live_node gst (addr_of p') ->
      wf_ptr p' ->
      better_succ gst h p' p0.

Definition first_succ_error (h : addr) (gst : global_state) : nat :=
  match sigma gst h with
  | Some st =>
    counting_opt_error gst (hd_error (succ_list st)) (better_succ_bool (make_pointer h))
  | None =>
    S (length (active_nodes gst))
  end.

Lemma succ_between_improves_error :
  forall h gst gst' st st' s s',
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    hd_error (succ_list st) = Some s ->
    hd_error (succ_list st') = Some s' ->
    live_node gst (addr_of s) ->
    live_node gst' (addr_of s') ->
    ptr_between (make_pointer h) s' s ->
    counting_opt_error gst' (Some s') (better_succ_bool (make_pointer h)) <
    counting_opt_error gst (Some s) (better_succ_bool (make_pointer h)).
Proof.
(*
if a node's first successor is s and then s',
and both s and s' are live,
and h < s' < s,
then the error measure of s' is less than that of s.

This requires reasoning about counting_opt_error, which is something I haven't
really figured out yet. I don't think it's going to be super involved since we
know so much about s and s'.

DIFFICULTY: Ryan.
USED: in a_before_pred_merge_point below
*)
Admitted.

(** First successor and predecessor combined phase two definitions *)
Definition pred_and_first_succ_correct (gst : global_state) (h : pointer) (st : data) : Prop :=
  pred_correct gst h (pred st) /\
  first_succ_correct gst h (hd_error (succ_list st)).

Definition pred_and_first_succ_error (h : addr) (gst : global_state) : nat :=
  pred_error h gst + first_succ_error h gst.

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

Lemma preds_and_first_succs_correct_from_phase_two_Cons :
  forall o ex,
    always (now phase_two) (Cons o ex) ->
    preds_and_first_succs_correct (occ_gst o).
Proof.
  unfold phase_two.
  intros.
  find_apply_lem_hyp always_Cons.
  tauto.
Qed.
Hint Resolve preds_and_first_succs_correct_from_phase_two_Cons.

Lemma phase_two_zero_error_has_pred :
  forall gst h st,
    live_node gst (addr_of h) ->
    wf_ptr h ->
    sigma gst (addr_of h) = Some st ->
    pred_and_first_succ_error (addr_of h) gst = 0 ->
    exists p, pred st = Some p /\
         pred_error (addr_of h) gst = 0.
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
      first_succ_error (addr_of h) gst = 0.
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

Lemma better_succ_intro :
  forall gst h s s',
    wf_ptr h ->
    wf_ptr s ->
    wf_ptr s' ->
    live_node gst (addr_of s') ->
    ptr_between h s' s ->
    better_succ gst h s s'.
Proof.
  unfold better_succ.
  auto.
Qed.

Lemma better_succ_bool_true_better_succ :
  forall gst h s s',
    wf_ptr h ->
    wf_ptr s ->
    wf_ptr s' ->
    live_node gst (addr_of s') ->
    better_succ_bool h s s' = true ->
    better_succ gst h s s'.
Proof.
  unfold better_succ_bool.
  intros.
  apply better_succ_intro; auto.
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

Lemma better_succ_bool_false_not_better_succ :
  forall gst h s s',
    better_succ_bool h s s' = false ->
    ~ better_succ gst h s s'.
Proof.
  unfold better_succ_bool, better_succ.
  intuition.
  find_eapply_lem_hyp between_bool_false_not_between; eauto.
Qed.

Lemma better_pred_bool_antisymmetric :
  forall h x y,
    id_of x <> id_of y ->
    better_pred_bool h x y = false ->
    better_pred_bool h y x = true.
Proof.
  unfold better_pred_bool.
  unfold ptr_between_bool.
  unfold between_bool.
  intros.
  repeat break_if; try congruence;
    repeat match goal with
           | H: _ = false |- _ =>
             apply ltb_false_lt in H
           | H: _ = true |- _ =>
             apply ltb_true_lt in H
           end;
    pose proof (Chord.ChordIDSpace.lt_total (id_of x) (id_of y));
    intuition.
Qed.

Lemma better_first_succ_bool_antisymmetric :
  forall h x y,
    id_of x <> id_of y ->
    better_succ_bool h x y = false ->
    better_succ_bool h y x = true.
Proof.
  unfold better_succ_bool.
  unfold ptr_between_bool.
  unfold between_bool.
  intros.
  repeat break_if; try congruence;
    repeat match goal with
           | H: _ = false |- _ =>
             apply ltb_false_lt in H
           | H: _ = true |- _ =>
             apply ltb_true_lt in H
           end;
    pose proof (Chord.ChordIDSpace.lt_total (id_of x) (id_of y));
    intuition.
Qed.

Lemma phase_two_zero_error_locally_correct :
  forall gst h st,
    reachable_st gst ->
    live_node gst (addr_of h) ->
    wf_ptr h ->
    sigma gst (addr_of h) = Some st ->
    pred_and_first_succ_error (addr_of h) gst = 0 ->
    pred_and_first_succ_correct gst h st.
Proof.
  intros.
  unfold pred_and_first_succ_correct; split; intros.
  - find_copy_apply_lem_hyp phase_two_zero_error_has_pred; auto.
    break_exists_exists; break_and; split; auto.
    intros.
    unfold pred_error in *; break_match; try congruence.
    find_injection.
    repeat find_rewrite.
    find_eapply_lem_hyp counting_opt_error_zero_implies_correct;
      eauto using better_pred_bool_antisymmetric.
    * assert (wf_ptr x /\ live_node gst (addr_of x)) by admit; try tauto.
      rewrite <- wf_ptr_eq in * by auto.
      by apply better_pred_bool_true_better_pred; tauto.
    * by admit.
  - find_copy_apply_lem_hyp phase_two_zero_error_has_first_succ; auto.
    break_exists_exists; expand_def; split; try find_rewrite; auto.
    unfold first_succ_error in *; break_match; try congruence.
    intros.
    find_injection.
    repeat find_rewrite.
    rewrite <- wf_ptr_eq in * by auto.
    find_eapply_lem_hyp counting_opt_error_zero_implies_correct;
      try eapply better_first_succ_bool_antisymmetric.
    all:assert (wf_ptr x /\ live_node gst (addr_of x)) by admit; break_and; eauto.
    eapply better_succ_bool_true_better_succ; simpl in *; tauto.

(*
This is an admit because it's missing an invariant saying predecessors and
successors are well-formed and live. This kind of bookkeeping is something Ryan
should take care of.

DIFFICULTY: Ryan
USED: Crucial to the phase 2 argument.
*)
Admitted.

Lemma phase_two_zero_error_correct :
  forall gst,
    reachable_st gst ->
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

Definition no_joins (gst gst' : global_state) :=
  forall h,
    live_node gst' h ->
    live_node gst h.

Theorem joins_stop :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    always (~_ (now circular_wait)) ex ->
    strong_local_fairness ex ->
    continuously (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex.
Proof.
(*
Since nodes only set joined=true some time after they are added to the network
and no new nodes are added to the network in an lb_execution, joins have to
eventually stop. That implies this lemma.

DIFFICULTY: Ryan
USED: In phase two.
*)
Admitted.

Lemma pred_error_nonincreasing :
  forall gst l gst' h,
    reachable_st gst ->
    no_joins gst gst' ->
    labeled_step_dynamic gst l gst' ->
    In h (active_nodes gst) ->
    pred_error h gst' <= pred_error h gst.
Proof.
(*
This needs to be connected to a safety property on predecessors.

DIFFICULTY: Ryan
USED: In phase two
*)
Admitted.

Lemma pred_error_always_nonincreasing :
  forall ex h,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    In h (active_nodes (occ_gst (hd ex))) ->
    always (consecutive (measure_nonincreasing (pred_error h))) ex.
Proof.
  intros ex h. revert ex.
  cofix c.
  intros.
  constructor;
    destruct ex as [o [o' ex]];
    inv_prop lb_execution.
  - simpl.
    inv_prop always.
    eapply pred_error_nonincreasing; eauto.
  - apply c; invar_eauto.
    eapply active_nodes_invar; eauto.
Qed.

Lemma first_succ_error_nonincreasing :
  forall gst l gst' h,
    reachable_st gst ->
    no_joins gst gst' ->
    labeled_step_dynamic gst l gst' ->
    In h (active_nodes gst) ->
    first_succ_error h gst' <= first_succ_error h gst.
Proof.
(*
This needs to be connected to a safety property on first successors.

DIFFICULTY: Ryan
USED: In phase two
*)
Admitted.

Lemma first_succ_error_always_nonincreasing :
  forall ex h,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    In h (active_nodes (occ_gst (hd ex))) ->
    always (consecutive (measure_nonincreasing (first_succ_error h))) ex.
Proof.
  intros ex h. revert ex.
  cofix c.
  intros.
  constructor;
    destruct ex as [o [o' ex]];
    inv_prop lb_execution.
  - simpl.
    inv_prop always.
    eapply first_succ_error_nonincreasing; eauto.
  - apply c; invar_eauto.
    eapply active_nodes_invar; eauto.
Qed.

Lemma nonincreasing_always_nonincreasing :
  forall meas,
    (forall gst l gst' h,
        reachable_st gst ->
        no_joins gst gst' ->
        labeled_step_dynamic gst l gst' ->
        In h (active_nodes gst) ->
        meas h gst' <= meas h gst) ->
    forall ex,
      reachable_st (occ_gst (hd ex)) ->
      lb_execution ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
      always (local_measures_nonincreasing meas) ex.
Proof.
  intros meas H_nonincreasing.
  cofix c.
  intros.
  constructor.
  - intros until 1.
    destruct ex as [o [o' ex]]; simpl in *.
    eapply H_nonincreasing; invar_eauto.
    now find_apply_lem_hyp always_now.
  - destruct ex.
    apply c; invar_eauto.
Qed.

Lemma pred_error_continuously_nonincreasing :
  forall ex,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    always (~_ now circular_wait) ex ->
    strong_local_fairness ex ->
    continuously (local_measures_nonincreasing pred_error) ex.
Proof.
  intros.
  find_apply_lem_hyp joins_stop; auto.
  induction 0.
  - apply E0.
    eapply nonincreasing_always_nonincreasing;
      eauto using pred_error_nonincreasing.
  - apply E_next.
    apply IHeventually; invar_eauto.
Qed.

Lemma first_succ_error_continuously_nonincreasing :
  forall ex,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    always (~_ now circular_wait) ex ->
    strong_local_fairness ex ->
    continuously (local_measures_nonincreasing first_succ_error) ex.
Proof.
  intros.
  find_apply_lem_hyp joins_stop; auto.
  induction 0.
  - apply E0.
    apply nonincreasing_always_nonincreasing;
      eauto using first_succ_error_nonincreasing.
  - apply E_next.
    apply IHeventually; invar_eauto.
Qed.

Theorem phase_two_error_always_nonincreasing :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    always (~_ now circular_wait) ex ->
    strong_local_fairness ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    always (local_measures_nonincreasing pred_and_first_succ_error) ex.
Proof.
  intros.
  eapply nonincreasing_always_nonincreasing; eauto.
  intros.
  apply plus_le_compat;
    eauto using pred_error_nonincreasing, first_succ_error_nonincreasing.
Qed.

Theorem phase_two_error_continuously_nonincreasing :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    always (~_ now circular_wait) ex ->
    strong_local_fairness ex ->
    continuously (local_measures_nonincreasing pred_and_first_succ_error) ex.
Proof.
  intros.
  find_copy_apply_lem_hyp joins_stop; auto.
  induction 0.
  - apply E0.
    apply phase_two_error_always_nonincreasing; auto.
  - apply E_next.
    apply IHeventually; invar_eauto.
Qed.

Definition pred_or_succ_improves (h : pointer) : infseq occurrence -> Prop :=
  consecutive (measure_decreasing (pred_and_first_succ_error (addr_of h))).

Definition pred_improves (h : pointer) : infseq occurrence -> Prop :=
  consecutive (measure_decreasing (pred_error (addr_of h))).

Definition first_succ_improves (h : pointer) : infseq occurrence -> Prop :=
  consecutive (measure_decreasing (first_succ_error (addr_of h))).

Lemma pred_improvement_suffices_local :
  forall o o' h,
    measure_nonincreasing (first_succ_error h) o o' ->
    measure_decreasing (pred_error h) o o' ->
    measure_decreasing (pred_and_first_succ_error h) o o'.
Proof.
  unfold measure_nonincreasing, measure_decreasing, pred_and_first_succ_error.
  intros.
  omega.
Qed.

Lemma first_succ_improvement_suffices_local :
  forall o o' h,
    measure_nonincreasing (pred_error h) o o' ->
    measure_decreasing (first_succ_error h) o o' ->
    measure_decreasing (pred_and_first_succ_error h) o o'.
Proof.
  unfold measure_nonincreasing, measure_decreasing, pred_and_first_succ_error.
  intros.
  omega.
Qed.

Lemma pred_improvement_suffices :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    always (~_ now circular_wait) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    strong_local_fairness ex ->
    forall h,
      live_node (occ_gst (hd ex)) (addr_of h) ->
      eventually (pred_improves h) ex ->
      eventually (pred_or_succ_improves h) ex.
Proof.
  intros.
  induction 0.
  - apply E0.
    destruct s as [o [o' s]].
    apply pred_improvement_suffices_local; eauto.
    find_apply_lem_hyp always_now'.
    eapply first_succ_error_nonincreasing;
      eauto using live_node_in_active, lb_execution_cons_cons.
  - apply E_next.
    apply IHeventually; invar_eauto.
Qed.

Lemma first_succ_improvement_suffices :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    always (~_ now circular_wait) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    strong_local_fairness ex ->
    forall h,
      live_node (occ_gst (hd ex)) (addr_of h) ->
      eventually (first_succ_improves h) ex ->
      eventually (pred_or_succ_improves h) ex.
Proof.
  intros.
  induction 0.
  - apply E0.
    destruct s as [o [o' s]].
    apply first_succ_improvement_suffices_local; eauto.
    find_apply_lem_hyp always_now'.
    eapply pred_error_nonincreasing;
      eauto using live_node_in_active, lb_execution_cons_cons.
  - apply E_next.
    apply IHeventually; invar_eauto.
Qed.

Lemma notify_when_pred_None_eventually_improves :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

    forall h p,
      In Notify (channel (occ_gst (hd ex)) (addr_of p) (addr_of h)) ->
      has_pred (occ_gst (hd ex)) (addr_of h) None ->
      wf_ptr h ->
      wf_ptr p ->
      eventually (pred_improves h) ex.
Proof.
(*
This assumes rectiying works, so that's several more proofs that need to be done.

DIFFICULTY: Ryan
USED: In phase two.
*)
Admitted.


Lemma notify_when_pred_dead_eventually_improves :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

    forall h p p',
      wf_ptr h ->
      wf_ptr p ->
      wf_ptr p' ->
      has_pred (occ_gst (hd ex)) (addr_of h) (Some p) ->
      In (addr_of p) (failed_nodes (occ_gst (hd ex))) ->
      In Notify (channel (occ_gst (hd ex)) (addr_of p') (addr_of h)) ->
      until
        (now (fun o => has_pred (occ_gst o) (addr_of h) (Some p)))
        (pred_improves h) ex.
Proof.
(*
This assumes rectiying works, so that's several more proofs that need to be done.

DIFFICULTY: Ryan
USED: In phase two.
*)
Admitted.

Lemma notify_when_pred_worse_eventually_improves :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

    forall h p p',
      In Notify (channel (occ_gst (hd ex)) p' h) ->
      has_pred (occ_gst (hd ex)) h (Some p) ->
      between (id_of p) (hash p') (hash h) ->
      eventually (pred_improves (make_pointer h)) ex.
Proof.
(*
This should be provable from the above two lemmas and a fact saying that if a
better pred exists, then the current pred is either dead or None.

DIFFICULTY: Ryan
USED: in phase two
*)
Admitted.

Definition merge_point (gst : global_state) (a b j : pointer) : Prop :=
  ptr_between a b j /\
  has_first_succ gst (addr_of a) j /\
  has_first_succ gst (addr_of b) j /\
  wf_ptr a /\
  wf_ptr b /\
  wf_ptr j /\
  a <> j /\
  b <> j /\
  a <> b /\
  live_node gst (addr_of a) /\
  live_node gst (addr_of b) /\
  live_node gst (addr_of j).

Lemma merge_point_wf :
  forall gst a b j,
    (merge_point gst a b j -> wf_ptr a) /\
    (merge_point gst a b j -> wf_ptr b) /\
    (merge_point gst a b j -> wf_ptr j).
Proof.
  unfold merge_point.
  tauto.
Qed.

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
(*
This is a problem and needs to be reduced to something less big.

DIFFICULTY: Ryan
USED: In phase two.
*)
Admitted.

Lemma open_stabilize_request_until_response :
  forall ex h j,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    wf_ptr j ->
    has_first_succ (occ_gst (hd ex)) h j ->
    open_stabilize_request_to_first_succ (occ_gst (hd ex)) h ->
    until
      (now (fun occ =>
              open_stabilize_request_to_first_succ (occ_gst occ) h /\
              has_first_succ (occ_gst occ) h j))
      (now (fun occ =>
              open_request_to (occ_gst occ) h (addr_of j) GetPredAndSuccs /\
              has_first_succ (occ_gst occ) h j /\
              (exists p succs,
                  In (GotPredAndSuccs p succs)
                     (channel (occ_gst occ) (addr_of j) h) /\
                  has_pred (occ_gst occ) (addr_of j) p /\
                  has_succs (occ_gst occ) (addr_of j) succs)))
      ex.
Proof.
(*
This is a problem and needs to be reduced to something less big.

DIFFICULTY: Ryan
USED: In phase two.
*)
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
              has_first_succ (occ_gst occ) h j /\
              (exists p succs,
                  In (GotPredAndSuccs p succs)
                     (channel (occ_gst occ) (addr_of j) h) /\
                  has_pred (occ_gst occ) (addr_of j) p /\
                  has_succs (occ_gst occ) (addr_of j) succs)))
      ex.
Proof.
  intros.
  eapply until_eventually.
  eapply open_stabilize_request_until_response; eauto.
Qed.

Lemma live_successor_changed_improves :
  forall gst l gst' h s s',
    reachable_st gst ->
    labeled_step_dynamic gst l gst' ->
    ~ In (addr_of s) (failed_nodes gst) ->
    has_first_succ gst h s ->
    has_first_succ gst' h s' ->
    s' <> s ->
    ptr_between (make_pointer h) s' s.
Proof using.
(*
This says that a new live successor at a host has to be between the host and its
old successor, provided the old one is live.

DIFFICULTY: 3
USED: In phase two (a_before_pred_merge_point).
*)
Admitted.

Lemma has_pred_eq :
  forall gst h p q,
    has_pred gst h p ->
    has_pred gst h q ->
    p = q.
Proof.
  intros.
  repeat invcs_prop has_pred; break_and.
  congruence.
Qed.

Ltac id_auto :=
  eauto using BetweenMono, BetweenWrapL, BetweenWrapR, Chord.ChordIDSpace.lt_asymm, Chord.ChordIDSpace.lt_irrefl, Chord.ChordIDSpace.lt_trans.

Ltac find_has_pred_eq :=
  match goal with
  | H : has_pred _ _ _ |- _ =>
    eapply has_pred_eq in H;
    [|clear H; now eauto]
  end.

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
    pose proof unrolling_total (hash (addr_of j)) (ptrId x) (ptrId y).
    break_or_hyp.
    - tauto.
    - find_copy_apply_lem_hyp unrolling_symmetry_cases.
      break_or_hyp.
      + right.
        now apply Bool.negb_true_iff.
      + tauto.
  Qed.

  Lemma pred_changing_suffices :
    forall ex h p p',
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

      p <> p' ->
      has_pred (occ_gst (hd ex)) h p ->
      eventually (now (fun o => has_pred (occ_gst o) h p')) ex ->
      eventually (pred_or_succ_improves (make_pointer h)) ex.
  Proof.
  (*
  If the predecessor changed, the pred or successor improved.
  Pretty obvious given earlier admits about predecessors changing, but I'm not
  sure how much work the proof actually is.

  DIFFICULTY: 3
  USED: In phase two.
  *)
  Admitted.

  Lemma pred_same_until_improvement :
    forall ex h p,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

      has_pred (occ_gst (hd ex)) h p ->
      weak_until (now (fun o => has_pred (occ_gst o) h p))
                 (pred_improves (make_pointer h)) ex.
  Proof.
  (*
  This should be a consequence of pred_changing_suffices or at least a similar argument.

  DIFFICULTY: 4
  USED: In phase two.
  *)
  Admitted.

  Lemma first_succ_same_until_improvement :
    forall ex h p,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

      has_first_succ (occ_gst (hd ex)) h p ->
      weak_until (now (fun o => has_first_succ (occ_gst o) h p))
                 (first_succ_improves (make_pointer h)) ex.
  Proof.
  (*
  This should be a consequence of first_succ_improvement_suffices or at least a similar argument.

  DIFFICULTY: 4
  USED: In phase two.
  *)
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
    - move/live_node_equiv_live_node_bool: Heqb0 => H_l.
      move/negP/live_node_equiv_live_node_bool: Heqb1 => H_l'.
      find_apply_lem_hyp live_In_live_ptrs; auto.
      find_rewrite.
      find_apply_lem_hyp In_live_ptrs_live.
      tauto.
    - move/negP/live_node_equiv_live_node_bool: Heqb0 => H_l.
      move/live_node_equiv_live_node_bool: Heqb1 => H_l'.
      find_apply_lem_hyp live_In_live_ptrs; auto.
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
  (* USELESS *)
  Admitted.

  Lemma handle_stabilize_sends_Notify_None :
    forall h src srcp st q new_succ succs st' ms nts cts,
      handle_stabilize h srcp st q new_succ succs = (st', ms, nts, cts) ->
      addr_of srcp = src ->
      new_succ = None ->
      In (src, Notify) ms.
  Proof.
    unfold handle_stabilize.
    intros.
    repeat find_rewrite.
    find_apply_lem_hyp end_query_definition; expand_def.
    auto with datatypes.
  Qed.

  Lemma handle_stabilize_sends_Notify_Some :
    forall h src srcp st q new_succ ns succs st' ms nts cts,
      handle_stabilize h srcp st q new_succ succs = (st', ms, nts, cts) ->
      addr_of srcp = src ->
      new_succ = Some ns ->
      ~ ptr_between (ptr st) ns srcp ->
      In (src, Notify) ms.
  Proof.
    unfold handle_stabilize.
    intros.
    find_apply_lem_hyp not_ptr_between.
    repeat find_rewrite.
    find_apply_lem_hyp end_query_definition; expand_def.
    auto with datatypes.
  Qed.

  Lemma notify_in_response_to_GotPredAndSuccs_None :
    forall st src srcp dst req succs st' ms nts cts,
      handle_msg src dst st (GotPredAndSuccs None succs) = (st', ms, nts, cts) ->
      addr_of srcp = src ->
      cur_request st = Some (srcp, Stabilize, req) ->
      In (src, Notify) ms.
  Proof.
    unfold handle_msg.
    intros.
    repeat find_rewrite.
    break_if; try congruence.
    simpl in *.
    congruence.
    unfold handle_query_res in *.
    repeat break_match; try (simpl in *; congruence).
    eapply handle_stabilize_sends_Notify_None; eauto.
  Qed.

  Lemma notify_in_response_to_GotPredAndSuccs_Some :
    forall st src srcp dst req p' succs st' ms nts cts,
      handle_msg src dst st (GotPredAndSuccs (Some p') succs) = (st', ms, nts, cts) ->
      addr_of srcp = src ->
      cur_request st = Some (srcp, Stabilize, req) ->
      ~ ptr_between (ptr st) p' (make_pointer src) ->
      In (src, Notify) ms.
  Proof.
    unfold handle_msg.
    intros.
    repeat find_rewrite.
    do 2 (break_match; try (simpl in *; congruence)).
    unfold handle_query_res in *.
    eauto using handle_stabilize_sends_Notify_Some.
  Qed.

  Lemma in_sends_in_msgs :
    forall gst gst' st' src dst st p ms nts cts target message,
      labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
      sigma gst dst = Some st ->
      recv_handler src dst st p = (st', ms, nts, cts) ->
      In (target, message) ms ->
      In (dst, (target, message)) (msgs gst').
  Proof.
    intros.
    invcs_prop labeled_step_dynamic; clean_up_labeled_step_cases.
    find_copy_apply_lem_hyp define_msg_from_recv_step_equality; break_and.
    find_apply_lem_hyp recv_handler_labeling.
    apply in_or_app; left.
    aggressive_rewrite_goal.
    fold (send dst (target, message)).
    apply in_map.
    congruence.
  Qed.

  Lemma sent_by_handle_msg_sent_by_recv_handler :
    forall send src dst st p hm_st hm_sends hm_nts hm_cts recv_st recv_sends recv_nts recv_cts,
      handle_msg src dst st p = (hm_st, hm_sends, hm_nts, hm_cts) ->
      recv_handler src dst st p = (recv_st, recv_sends, recv_nts, recv_cts) ->
      In send hm_sends ->
      In send recv_sends.
  Proof.
    intros.
    find_apply_lem_hyp recv_handler_definition_existential; expand_def.
    repeat find_rewrite; tuple_inversion.
    auto with datatypes.
  Qed.

  Lemma recv_GotPredAndSuccs_causes_Notify :
    forall gst gst' h s p succs st,
      reachable_st gst ->
      sigma gst (addr_of h) = Some st ->
      h = ptr st ->
      wf_ptr s ->
      labeled_step_dynamic gst (RecvMsg (addr_of s) (addr_of h) (GotPredAndSuccs p succs)) gst' ->
      open_request_to gst (addr_of h) (addr_of s) GetPredAndSuccs ->
      (exists p', p = Some p' /\ ~ ptr_between (ptr st) p' s) \/ p = None ->
      In Notify (channel gst' (addr_of h) (addr_of s)).
  Proof.
    intros.
    apply channel_contents.
    inv_prop open_request_to; break_exists; break_and.
    inv_labeled_step; clean_up_labeled_step_cases.
    find_copy_apply_lem_hyp define_msg_from_recv_step_equality; break_exists; break_and.
    find_apply_lem_hyp recv_handler_labeling; break_exists; break_and.
    subst_max.
    eapply in_sends_in_msgs; eauto.
    simpl in *.
    find_copy_apply_lem_hyp recv_handler_definition_existential; break_exists; break_and.
    eapply sent_by_handle_msg_sent_by_recv_handler; eauto.
    repeat find_rewrite; repeat find_injection.
    inv_prop request_msg_for_query.
    break_or_hyp.
    - break_exists; break_and.
      find_apply_lem_hyp (wf_ptr_eq s).
      repeat find_reverse_rewrite; subst_max.
      eapply notify_in_response_to_GotPredAndSuccs_Some; eauto.
    - find_apply_lem_hyp (wf_ptr_eq s).
      repeat find_reverse_rewrite.
      eapply notify_in_response_to_GotPredAndSuccs_None; eauto.
  Qed.

  Lemma recv_GotPredAndSuccs_causes_Notify_Some :
    forall gst gst' h s p succs st,
      reachable_st gst ->
      sigma gst (addr_of h) = Some st ->
      h = ptr st ->
      wf_ptr s ->
      labeled_step_dynamic gst (RecvMsg (addr_of s) (addr_of h) (GotPredAndSuccs (Some p) succs)) gst' ->
      open_request_to gst (addr_of h) (addr_of s) GetPredAndSuccs ->
      ~ ptr_between (ptr st) p s ->
      In Notify (channel gst' (addr_of h) (addr_of s)).
  Proof.
    eauto using recv_GotPredAndSuccs_causes_Notify.
  Qed.

  Lemma recv_GotPredAndSuccs_causes_Notify_None :
    forall gst gst' h s succs st,
      reachable_st gst ->
      sigma gst (addr_of h) = Some st ->
      h = ptr st ->
      wf_ptr s ->
      labeled_step_dynamic gst (RecvMsg (addr_of s) (addr_of h) (GotPredAndSuccs None succs)) gst' ->
      open_request_to gst (addr_of h) (addr_of s) GetPredAndSuccs ->
      In Notify (channel gst' (addr_of h) (addr_of s)).
  Proof.
    eauto using recv_GotPredAndSuccs_causes_Notify.
  Qed.

  Lemma handle_msg_busy_is_handle_query_req_busy :
    forall src dst st p,
      cur_request st <> None ->
      request_payload p ->
      p <> Ping ->
      handle_msg src dst st p = handle_query_req_busy src st p.
  Proof.
    intros.
    destruct (handle_msg _ _ _) as [[[?st ?ms] ?nts] ?cts] eqn:?H.
    symmetry.
    find_apply_lem_hyp handle_msg_definition; expand_def;
      solve [assumption | now invc_prop request_payload].
  Qed.

  Lemma recv_handler_GetPredAndSuccs_gives_GotPredAndSuccs :
    forall src dst st st' sends nts cts,
      cur_request st = None ->
      recv_handler src dst st GetPredAndSuccs = (st', sends, nts, cts) ->
      In (src, GotPredAndSuccs (pred st) (succ_list st)) sends.
  Proof.
    intros.
    find_copy_apply_lem_hyp recv_handler_definition_existential; expand_def.
    eapply sent_by_handle_msg_sent_by_recv_handler; eauto.
    simpl in *.
    repeat find_rewrite. tuple_inversion.
    auto with datatypes.
  Qed.

  Lemma recv_GetPredAndSuccs_busy_queues_request :
    forall gst gst' src dst st st',
      labeled_step_dynamic gst (RecvMsg src dst GetPredAndSuccs) gst' ->
      reachable_st gst ->
      sigma gst dst = Some st ->
      cur_request st <> None ->
      sigma gst' dst = Some st' ->
      In (src, GetPredAndSuccs) (delayed_queries st').
  Proof.
    intros.
    inv_labeled_step.
    find_copy_apply_lem_hyp define_msg_from_recv_step_equality; break_and.
    find_copy_apply_lem_hyp recv_handler_labeling.
    repeat find_rewrite. simpl in *. rewrite_update. repeat find_injection.
    find_apply_lem_hyp recv_handler_definition_existential; expand_def.
    rewrite handle_msg_busy_is_handle_query_req_busy in H3; auto;
      try constructor; try congruence.
    find_copy_apply_lem_hyp handle_query_req_busy_preserves_cur_request.
    find_copy_apply_lem_hyp do_delayed_queries_busy_nop; expand_def;
      try congruence.
    eapply handle_query_req_busy_delays_query; eauto.
  Qed.

  Lemma recv_GetPredAndSuccs_not_busy_causes_GotPredAndSuccs :
    forall gst gst' src dst st,
      labeled_step_dynamic gst (RecvMsg src dst GetPredAndSuccs) gst' ->
      reachable_st gst ->
      sigma gst dst = Some st ->
      cur_request st = None ->
      In (GotPredAndSuccs (pred st) (succ_list st)) (channel gst' dst src).
  Proof.
    intros.
    inv_labeled_step.
    find_copy_apply_lem_hyp define_msg_from_recv_step_equality; break_and.
    find_copy_apply_lem_hyp recv_handler_labeling.
    repeat find_rewrite. simpl in *. find_injection.
    apply channel_contents.
    eapply in_sends_in_msgs; eauto.
    eapply recv_handler_GetPredAndSuccs_gives_GotPredAndSuccs; eauto.
  Qed.

  Lemma recv_GetPredAndSuccs_causes_GotPredAndSuccs_eq :
    forall gst gst' src dst st,
      labeled_step_dynamic gst (RecvMsg src dst GetPredAndSuccs) gst' ->
      reachable_st gst ->
      sigma gst dst = Some st ->
      cur_request st = None ->
      forall p succs,
        p = pred st ->
        succs = succ_list st ->
        In (GotPredAndSuccs p succs) (channel gst' dst src).
  Proof.
    intros. subst.
    eapply recv_GetPredAndSuccs_not_busy_causes_GotPredAndSuccs; eauto.
  Qed.

  Definition pred_not_worse (h l : pointer) (ex : infseq occurrence) :=
    exists p,
      ptr_between l p h /\
      now (fun occ => has_pred (occ_gst occ) (addr_of h) (Some p)) ex /\
      always (now (fun occ =>
                     exists p',
                       has_pred (occ_gst occ) (addr_of h) (Some p') /\
                       (ptr_between p p' h \/ p = p')))
             ex.

  Lemma pred_bound_pred_not_worse :
    forall ex p,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      always (now phase_one) ex ->

      j <> a ->
      has_pred (occ_gst (hd ex)) (addr_of j) (Some p) ->
      a <=? p = true ->
      always (pred_not_worse j a) ex.
  Proof using a j.
  (*
  I don't understand how to prove this but I think it should be a consequence of
  other facts about how predecessor pointers are allowed to change.

  DIFFICULTY: Ryan
  USED: In phase two.
  *)
  Admitted.

  Ltac eapply_prop' P :=
    match goal with
    | H: P _ |- _ => eapply H
    | H: P _ _ |- _ => eapply H
    | H: P _ _ _ |- _ => eapply H
    | H: P _ _ _ _ |- _ => eapply H
    | H: context[P] |- _ => eapply H
    end.

  Lemma successors_are_live_nodes :
    forall gst h s,
      reachable_st gst ->
      all_first_succs_best gst ->
      has_first_succ gst h s ->
      live_node gst (addr_of s).
  Proof using.
  (*
  This won't be inductive as written. We'll have to generalize to all nodes in
  successor lists and possibly do some accounting for how joining works.

  DIFFICULTY: Ryan.
  USED: In phase two.
  *)
  Admitted.

  Lemma a_before_pred_merge_point :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

      forall st p,
        merge_point (occ_gst (hd ex)) a b j ->
        sigma (occ_gst (hd ex)) (addr_of j) = Some st ->
        pred st = Some p ->
        a <=? p = true ->
        eventually (pred_or_succ_improves a) ex.
  Proof.
    intros.
    invcs_prop merge_point; break_and.
    assert (has_pred (occ_gst (hd ex)) (addr_of j) (Some p))
      by (eexists; eauto).
    assert (always (pred_not_worse j a) ex)
      by eauto using pred_bound_pred_not_worse.
    find_copy_apply_lem_hyp (start_stabilize_with_first_successor_eventually ex (addr_of a)); auto.
    clear dependent p.
    clear dependent st.
    clear dependent b.
    induction 0 as [ex | o [o' ex]].
    - find_copy_apply_lem_hyp always_now'.
      inv_prop pred_not_worse; expand_def.
      find_apply_lem_hyp now_hd.
      eapply better_pred_eventually_improves_succ; eauto.
      {
        (* Why do I have to do this? *)
        fold (ptrAddr a) (addr_of a).
        now rewrite <- wf_ptr_eq.
      }
      find_apply_lem_hyp open_stabilize_request_eventually_gets_response;
        try now destruct ex.
      find_eapply_lem_hyp always_and_tl; [|eapply_prop' pred_not_worse].
      eapply eventually_monotonic;
        [ | | eapply_prop' always | eauto ];
        invar_eauto.
      intros.
      destruct s; simpl in *.
      intuition.
      break_exists_name p.
      repeat find_apply_lem_hyp always_now'.
      destruct p as [p|].
      + exists p. break_exists_exists.
        intuition.
        invcs_prop and_tl; break_exists.
        invc_prop pred_not_worse; break_and.
        invc_prop pred_not_worse; break_and.
        repeat find_has_pred_eq.
        find_injection.
        congruence.
      + invcs_prop and_tl; break_exists.
        invcs_prop and_tl; break_exists.
        invc_prop pred_not_worse; break_and.
        find_has_pred_eq.
        congruence.
    - assert (live_node (occ_gst o') (addr_of a))
        by (inv_prop lb_execution; invar_eauto).
      invcs_prop live_node; break_and.
      break_exists_name a_st; break_and.
      destruct (option_eq_dec _ pointer_eq_dec (Some j) (hd_error (succ_list a_st))).
      + apply E_next.
        apply IHeventually;
          invar_eauto.
        eexists; eauto.
      + apply E0.
        invcs_prop has_first_succ; break_and.
        find_apply_lem_hyp always_now; break_and.
        destruct (hd_error (succ_list a_st)) eqn:?H.
        * apply Nat.add_le_lt_mono.
          {
            eapply pred_error_nonincreasing; invar_eauto;
              eauto using live_node_in_active.
            now inv_prop no_joins.
          }
          unfold first_succ_error; repeat find_rewrite.
          eapply succ_between_improves_error; eauto.
          -- inv_prop phase_one.
             unfold phase_one in *.
             find_apply_lem_hyp always_Cons; break_and.
             eapply successors_are_live_nodes; invar_eauto.
             eapply has_first_succ_intro; eauto.
          -- inv_prop (live_node (occ_gst o) (addr_of j)); expand_def.
             eapply live_successor_changed_improves; invar_eauto.
             eapply has_first_succ_intro; eauto.
             eapply has_first_succ_intro; eauto.
             congruence.
        * exfalso.
          find_apply_lem_hyp hd_error_None.
          eapply (nodes_have_nonempty_succ_lists (occ_gst o')); invar_eauto.
  Qed.

  Lemma not_between_xxy :
    forall x y,
      ~ between x x y.
  Proof.
    intros; intro.
    inv_prop between;
      solve [tauto | eapply Chord.ChordIDSpace.lt_irrefl; eauto].
  Qed.

  Lemma not_between_xyy :
    forall x y,
      ~ between x y y.
  Proof.
    intros; intro.
    inv_prop between;
      solve [tauto | eapply Chord.ChordIDSpace.lt_irrefl; eauto].
  Qed.

  Lemma between_xyx :
    forall x y,
      x <> y ->
      between x y x.
  Proof.
    intros.
    pose proof (Chord.ChordIDSpace.lt_total x y); repeat break_or_hyp;
      congruence || id_auto.
  Qed.

  Lemma lt_asymm_neg :
    forall x y,
      ~ Chord.ChordIDSpace.lt x y ->
      Chord.ChordIDSpace.lt y x \/ x = y.
  Proof.
    intros.
    pose proof (Chord.ChordIDSpace.lt_total x y).
    repeat break_or_hyp; tauto.
  Qed.

  Lemma between_rot_l :
    forall x y z,
      x <> z ->
      between x y z ->
      between y z x.
  Proof.
    intros.
    invcs_prop between;
      id_auto;
      find_copy_apply_lem_hyp lt_asymm_neg;
      break_or_hyp;
      congruence || id_auto.
  Qed.

  Lemma between_rot_r :
    forall x y z,
      x <> z ->
      between x y z ->
      between z x y.
  Proof.
    intros.
    invcs_prop between;
      id_auto;
      find_copy_apply_lem_hyp lt_asymm_neg;
      break_or_hyp;
      congruence || id_auto.
  Qed.

  Lemma not_between_cases :
    forall x y z,
      ~ between x y z ->
      x = y \/ y = z \/ between z y x.
  Proof.
    intros.
    pose proof (Chord.ChordIDSpace.lt_total x y).
    pose proof (Chord.ChordIDSpace.lt_total y z).
    pose proof (Chord.ChordIDSpace.lt_total z x).
    repeat break_or_hyp;
      solve [tauto | id_auto |  congruence | find_false; id_auto].
  Qed.

  Lemma unrolled_not_between_rot :
    forall x y z,
      unroll_between z x y = false ->
      ~ between x y z.
  Proof.
    intros.
    unfold unroll_between in *.
    repeat break_if; try congruence.
    - subst.
      apply not_between_xyy.
    - intro.
      eapply between_bool_false_not_between;
        eauto using between_rot_r.
  Qed.

  Lemma not_between_swap :
    forall x y z,
      y <> z ->
      ~ between x y z ->
      between x z y.
  Proof.
    intros.
    find_copy_apply_lem_hyp not_between_cases.
    repeat break_or_hyp.
    - now apply between_xyx.
    - congruence.
    - pose proof (Chord.ChordIDSpace.lt_total x z).
      pose proof (Chord.ChordIDSpace.lt_total x y).
      pose proof (Chord.ChordIDSpace.lt_total y z).
      repeat break_or_hyp;
        solve [id_auto | congruence | find_false; id_auto].
  Qed.

  Lemma not_between_between :
    forall x y z,
      unroll_between x y z = false ->
      between z y x.
  Proof.
    unfold unroll_between.
    intros.
    repeat break_if; subst; try congruence.
    - now apply between_xyx.
    - apply between_rot_r; auto.
      apply between_rot_r; auto.
      apply not_between_swap; auto.
      now apply between_bool_false_not_between.
  Qed.

  Lemma recv_GotPredAndSuccs_with_a_after_p_causes_Notify :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->

      forall p js,
        wf_ptr a ->
        wf_ptr j ->
        live_node (occ_gst (hd ex)) (addr_of a) ->
        live_node (occ_gst (hd ex)) (addr_of j) ->
        has_first_succ (occ_gst (hd ex)) (addr_of a) j ->
        a <> j ->
        a >? p = true ->
        open_request_to (occ_gst (hd ex)) (addr_of a) (addr_of j) GetPredAndSuccs ->
        now (occurred (RecvMsg (addr_of j) (addr_of a) (GotPredAndSuccs (Some p) js))) ex ->
        next (now (fun o => In Notify (channel (occ_gst o) (addr_of a) (addr_of j)))) ex.
  Proof using a j.
    intros.
    destruct ex as [o [o' ex]].
    inv_prop lb_execution.
    simpl in *.
    find_eapply_lem_hyp (live_node_means_state_exists (occ_gst o) (addr_of a)).
    break_exists_name a_st.
    invc_prop occurred.
    repeat find_reverse_rewrite.
    assert (ptr a_st = a)
      by (erewrite ptr_correct, <- wf_ptr_eq; eauto).
    eapply recv_GotPredAndSuccs_causes_Notify_Some; eauto.
    repeat find_rewrite.
    eapply unrolled_not_between_rot.
    eapply Bool.negb_true_iff.
    erewrite (wf_ptr_eq j); auto.
  Qed.

  Lemma recv_GotPredAndSuccs_with_pred_None_causes_Notify :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->

      forall js,
        live_node (occ_gst (hd ex)) (addr_of a) ->
        wf_ptr a ->
        wf_ptr j ->
        open_request_to (occ_gst (hd ex)) (addr_of a) (addr_of j) GetPredAndSuccs ->
        now (occurred (RecvMsg (addr_of j) (addr_of a) (GotPredAndSuccs None js))) ex ->
        next (now (fun o => In Notify (channel (occ_gst o) (addr_of a) (addr_of j)))) ex.
  Proof.
    intros.
    destruct ex as [o [o' ex]].
    inv_prop lb_execution.
    simpl in *.
    find_eapply_lem_hyp (live_node_means_state_exists (occ_gst o) (addr_of a)).
    break_exists.
    invcs_prop occurred.
    repeat find_reverse_rewrite.
    eapply recv_GotPredAndSuccs_causes_Notify_None; eauto.
    erewrite ptr_correct, <- wf_ptr_eq; eauto.
  Qed.

  Lemma recv_GotPredAndSuccs_with_a_after_p_causes_improvement :
    forall o ex,
      lb_execution (Cons o ex) ->
      reachable_st (occ_gst o) ->
      strong_local_fairness (Cons o ex) ->
      always (~_ (now circular_wait)) (Cons o ex) ->
      always (now phase_one) (Cons o ex) ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
      has_first_succ (occ_gst o) (addr_of a) j ->
      a <> j ->
      wf_ptr a ->
      wf_ptr j ->
      live_node (occ_gst o) (addr_of a) ->
      live_node (occ_gst o) (addr_of j) ->

      forall p js,
        has_pred (occ_gst (hd ex)) (addr_of j) (Some p) ->
        a >? p = true ->
        open_request_to (occ_gst o) (addr_of a) (addr_of j) GetPredAndSuccs ->
        now (occurred (RecvMsg (addr_of j) (addr_of a) (GotPredAndSuccs (Some p) js))) (Cons o ex) ->
        eventually (pred_improves j) ex.
  Proof using a j.
    intros.
    repeat invc_prop merge_point. break_and.
    clear dependent b.
    find_apply_lem_hyp recv_GotPredAndSuccs_with_a_after_p_causes_Notify; simpl in *; invar_eauto.
    destruct ex as [o' ex]; simpl in *.
    rewrite (wf_ptr_eq j); eauto.
    eapply notify_when_pred_worse_eventually_improves; invar_eauto.
    apply not_between_between.
    unfold unroll_between_ptr in *.
    apply Bool.negb_true_iff.
    unfold Chord.ChordIDParams.hash in *.
    by rewrite (wf_ptr_hash_eq a).
  Qed.


  Lemma occurred_is_step :
    forall l o o' ex,
      occurred l o ->
      lb_execution (Cons o (Cons o' ex)) ->
      labeled_step_dynamic (occ_gst o) l (occ_gst o').
  Proof.
    unfold occurred.
    intros.
    now inv_prop lb_execution.
  Qed.

  Definition pred_or_succ_improves_abj : infseq occurrence -> Prop :=
    pred_or_succ_improves a \/_
    pred_or_succ_improves b \/_
    pred_or_succ_improves j.
  Hint Unfold pred_or_succ_improves_abj.

  Lemma merge_points_preserved_until_error_drops :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      always (now phase_one) ex ->

      merge_point (occ_gst (hd ex)) a b j ->
      weak_until (now (fun occ => merge_point (occ_gst occ) a b j))
                 pred_or_succ_improves_abj
                 ex.
  Proof.
  (*
  I'm really not sure how to prove this.
  DIFFICULTY: Ryan
  *)
  Admitted.

  Lemma merge_point_gone_improved_something :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      always (now phase_one) ex ->

      merge_point (occ_gst (hd ex)) a b j ->
      ~ merge_point (occ_gst (hd (tl ex))) a b j ->
      eventually (pred_or_succ_improves a) ex \/
      eventually (pred_or_succ_improves b) ex \/
      eventually (pred_or_succ_improves j) ex.
  Proof.
    intros.
    find_apply_lem_hyp merge_points_preserved_until_error_drops; auto.
    destruct ex as [o [o' ex]].
    autounfold in *.
    find_apply_lem_hyp weak_until_Cons; break_or_hyp.
    - unfold or_tl in *.
      intuition auto using E0.
    - break_and.
      find_apply_lem_hyp weak_until_Cons; break_or_hyp.
      + unfold or_tl in *.
        intuition auto using E_next, E0.
      + tauto.
  Qed.

  Lemma pred_improves_pred_and_succ_improves :
    forall h ex,
      consecutive (measure_nonincreasing (first_succ_error (addr_of h))) ex ->
      pred_improves h ex ->
      pred_or_succ_improves h ex.
  Proof.
    destruct ex as [o [o' ex]].
    unfold pred_or_succ_improves.
    apply pred_improvement_suffices_local.
  Qed.

  Lemma pred_improves_improves_abj :
    forall ex,
      consecutive (measure_nonincreasing (first_succ_error (addr_of j))) ex ->
      pred_improves j ex ->
      pred_or_succ_improves_abj ex.
  Proof.
    intros.
    unfold pred_or_succ_improves_abj, or_tl.
    intuition auto using pred_improves_pred_and_succ_improves.
  Qed.

  Lemma pred_improves_improves_abj_eventually :
    forall ex,
      always (consecutive (measure_nonincreasing (first_succ_error (addr_of j)))) ex ->
      eventually (pred_improves j) ex ->
      eventually pred_or_succ_improves_abj ex.
  Proof.
    apply eventually_monotonic; [invar_eauto|].
    intros until 1.
    apply pred_improves_improves_abj.
    now apply always_now'.
  Qed.

  Lemma first_succ_improves_pred_and_succ_improves :
    forall h ex,
      consecutive (measure_nonincreasing (pred_error (addr_of h))) ex ->
      first_succ_improves h ex ->
      pred_or_succ_improves h ex.
  Proof.
    destruct ex as [o [o' ex]].
    unfold pred_or_succ_improves.
    apply first_succ_improvement_suffices_local.
  Qed.

  Lemma first_succ_improves_improves_abj :
    forall ex,
      consecutive (measure_nonincreasing (pred_error (addr_of a))) ex ->
      first_succ_improves a ex ->
      pred_or_succ_improves_abj ex.
  Proof.
    intros.
    unfold pred_or_succ_improves_abj, or_tl.
    intuition auto using first_succ_improves_pred_and_succ_improves.
  Qed.

  Lemma incoming_GotPredAndSuccs_with_a_after_p_causes_improvement :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
      a <> j ->
      wf_ptr a ->
      wf_ptr j ->
      live_node (occ_gst (hd ex)) (addr_of a) ->
      live_node (occ_gst (hd ex)) (addr_of j) ->
      has_first_succ (occ_gst (hd ex)) (addr_of a) j ->

      forall p js,
        has_pred (occ_gst (hd ex)) (addr_of j) (Some p) ->
        a >? p = true ->
        open_request_to (occ_gst (hd ex)) (addr_of a) (addr_of j) GetPredAndSuccs ->
        In (GotPredAndSuccs (Some p) js) (channel (occ_gst (hd ex)) (addr_of j) (addr_of a)) ->
        eventually (pred_improves j) ex.
  Proof using a j.
    intros.
    find_apply_lem_hyp channel_contents.
    inv_prop (live_node (occ_gst (hd ex)) (addr_of a)).
    expand_def.
    find_eapply_lem_hyp RecvMsg_eventually_occurred; invar_eauto;
      eauto using strong_local_fairness_weak, live_node_in_nodes, live_node_means_state_exists.
    induction 0 as [[o [o' ex]] | o [o' ex]].
    - find_copy_apply_lem_hyp pred_same_until_improvement; auto.
      find_apply_lem_hyp weak_until_Cons.
      intuition auto using E0, E_next.
      find_apply_lem_hyp weak_until_Cons.
      intuition auto using E0, E_next.
      simpl in *.
      eapply E_next, recv_GotPredAndSuccs_with_a_after_p_causes_improvement;
        invar_eauto.
    - find_copy_apply_lem_hyp pred_same_until_improvement; auto.
      find_apply_lem_hyp weak_until_Cons.
      intuition auto using E0, E_next.
      find_apply_lem_hyp weak_until_Cons.
      intuition auto using E0, E_next.
      simpl in *.
      apply E_next, IHeventually; simpl; invar_eauto.
      (* branch on label *)
      all:admit.
  (* This might not be provable??? *)
  Admitted.

  Lemma recv_GotPredAndSuccs_with_pred_None_causes_improvement :
    forall o ex,
      lb_execution (Cons o ex) ->
      reachable_st (occ_gst o) ->
      strong_local_fairness (Cons o ex) ->
      always (~_ (now circular_wait)) (Cons o ex) ->
      always (now phase_one) (Cons o ex) ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
      wf_ptr a ->
      wf_ptr j ->
      live_node (occ_gst (hd (Cons o ex))) (addr_of a) ->

      forall js,
        has_pred (occ_gst (hd ex)) (addr_of j) None ->
        open_request_to (occ_gst o) (addr_of a) (addr_of j) GetPredAndSuccs ->
        now (occurred (RecvMsg (addr_of j) (addr_of a) (GotPredAndSuccs None js))) (Cons o ex) ->
        eventually (pred_improves j) ex.
  Proof.
    intros.
    find_apply_lem_hyp recv_GotPredAndSuccs_with_pred_None_causes_Notify;
      try now (repeat invcs_prop merge_point; intuition invar_eauto).
    destruct ex as [o' ex]; simpl in *.
    (* makes eauto instantiate evars correctly instead of making them both j *)
    change o' with (hd (Cons o' ex)) in *.
    find_eapply_lem_hyp notify_when_pred_None_eventually_improves; invar_eauto.
  Qed.

  Lemma incoming_GotPredAndSuccs_with_pred_None_causes_improvement :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

      live_node (occ_gst (hd ex)) (addr_of a) ->
      live_node (occ_gst (hd ex)) (addr_of j) ->
      wf_ptr a ->
      wf_ptr j ->

      forall js,
        has_pred (occ_gst (hd ex)) (addr_of j) None ->
        open_request_to (occ_gst (hd ex)) (addr_of a) (addr_of j) GetPredAndSuccs ->
        In (GotPredAndSuccs None js) (channel (occ_gst (hd ex)) (addr_of j) (addr_of a)) ->
        eventually pred_or_succ_improves_abj ex.
  Proof.
    intros.
    find_apply_lem_hyp channel_contents.
    inv_prop (live_node (occ_gst (hd ex)) (addr_of a)).
    break_and.
    break_exists_name st.
    break_and.
    find_copy_eapply_lem_hyp (first_succ_error_always_nonincreasing ex (addr_of j));
      eauto using live_node_in_active.
    find_eapply_lem_hyp RecvMsg_eventually_occurred; invar_eauto;
      eauto using strong_local_fairness_weak, live_node_in_nodes, live_node_means_state_exists.
    clear dependent st.
    repeat match goal with
           | H : context[In (addr_of a)] |- _ => clear H
           end.
    induction 0 as [[o [o' ex]] | o [o' ex]];
      find_copy_apply_lem_hyp pred_same_until_improvement; auto;
      do 2 (eapply_lem_prop_hyp weak_until_Cons has_pred;
            invc_prop measure_nonincreasing;
            intuition eauto using eventually_or_tl_intror, E0, E_next, pred_improves_improves_abj).
    - apply E_next.
      do 2 apply eventually_or_tl_intror.
      apply pred_improvement_suffices; invar_eauto.
      eapply recv_GotPredAndSuccs_with_pred_None_causes_improvement;
        invar_eauto.
    - inv_prop lb_execution.
      find_copy_apply_lem_hyp channel_contents.
      eapply_lem_prop_hyp open_request_with_response_on_wire_closed_or_preserved labeled_step_dynamic;
        eauto using pair_GetPredAndSuccs.
      break_or_hyp; break_and.
      + apply E_next.
        do 2 apply eventually_or_tl_intror.
        apply pred_improvement_suffices; invar_eauto.
        eapply recv_GotPredAndSuccs_with_pred_None_causes_improvement;
          invar_eauto.
      + find_apply_lem_hyp channel_contents.
        apply E_next.
        apply IHeventually;
          eauto using active_nodes_invar, nodes_never_removed; invar_eauto.
        apply first_succ_error_always_nonincreasing; invar_eauto.
        apply live_node_in_active; invar_eauto.
  Qed.

  Lemma open_stabilize_request_pred_None_eventually_improves_join_point :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
      live_node (occ_gst (hd ex)) (addr_of a) ->
      live_node (occ_gst (hd ex)) (addr_of j) ->
      wf_ptr a ->
      wf_ptr j ->
      has_first_succ (occ_gst (hd ex)) (addr_of a) j ->
      has_pred (occ_gst (hd ex)) (addr_of j) None ->
      open_stabilize_request_to_first_succ (occ_gst (hd ex)) (addr_of a) ->
      eventually pred_or_succ_improves_abj ex.
  Proof.
    intros.
    find_copy_eapply_lem_hyp (first_succ_error_always_nonincreasing ex (addr_of j));
      eauto using live_node_in_active.
    find_copy_eapply_lem_hyp open_stabilize_request_until_response; eauto.
    induction 0 as [[o [o' ex]] | o [o' ex]].
    - simpl in *. break_and.
      break_exists_name p; expand_def.
      destruct p as [p|].
      + find_has_pred_eq.
        congruence.
      + eapply incoming_GotPredAndSuccs_with_pred_None_causes_improvement; invar_eauto.
    - find_copy_apply_lem_hyp pred_same_until_improvement; auto.
      do 2 (eapply_lem_prop_hyp weak_until_Cons has_pred;
            inv_prop measure_nonincreasing;
            intuition eauto using eventually_or_tl_intror, E0, E_next, pred_improves_improves_abj).
      find_apply_lem_hyp until_Cons. simpl in H14; expand_def.
      + find_has_pred_eq; subst.
        apply E_next.
        eapply incoming_GotPredAndSuccs_with_pred_None_causes_improvement;
          invar_eauto;
          eauto using channel_contents.
      + apply E_next, IHuntil; invar_eauto.
  Qed.

  Lemma open_stabilize_request_a_after_p_eventually_improves_join_point :
    forall ex p,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
      a <> j ->
      live_node (occ_gst (hd ex)) (addr_of a) ->
      live_node (occ_gst (hd ex)) (addr_of j) ->
      wf_ptr a ->
      wf_ptr j ->
      has_first_succ (occ_gst (hd ex)) (addr_of a) j ->
      has_pred (occ_gst (hd ex)) (addr_of j) (Some p) ->
      (a >? p) = true ->
      open_stabilize_request_to_first_succ (occ_gst (hd ex)) (addr_of a) ->
      eventually (pred_improves j) ex.
  Proof.
    intros.
    find_copy_eapply_lem_hyp (first_succ_error_always_nonincreasing ex (addr_of j));
      eauto using live_node_in_active.
    find_copy_eapply_lem_hyp open_stabilize_request_until_response; eauto.
    induction 0 as [[o [o' ex]] | o [o' ex]].
    - simpl in *. expand_def.
      find_has_pred_eq; subst.
      eapply incoming_GotPredAndSuccs_with_a_after_p_causes_improvement; invar_eauto.
    - find_copy_apply_lem_hyp pred_same_until_improvement; auto.
      do 2 (eapply_lem_prop_hyp weak_until_Cons has_pred;
            inv_prop measure_nonincreasing;
            intuition eauto using eventually_or_tl_intror, E0, E_next, pred_improves_improves_abj).
      destruct ex.
      find_copy_apply_lem_hyp until_Cons. break_and. simpl in *; expand_def.
      + find_has_pred_eq; subst.
        apply E_next.
        eapply incoming_GotPredAndSuccs_with_a_after_p_causes_improvement;
          invar_eauto;
          eauto using channel_contents.
      + apply E_next, IHuntil; invar_eauto.
  Qed.

  Lemma a_after_pred_merge_point :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

      live_node (occ_gst (hd ex)) (addr_of a) ->
      live_node (occ_gst (hd ex)) (addr_of j) ->
      wf_ptr a ->
      wf_ptr j ->
      a <> j ->
      has_first_succ (occ_gst (hd ex)) (addr_of a) j ->

      forall st p,
        sigma (occ_gst (hd ex)) (addr_of j) = Some st ->
        pred st = Some p ->
        a >? p = true ->
        eventually pred_or_succ_improves_abj ex.
  Proof.
    intros.
    find_eapply_lem_hyp has_pred_intro; eauto.
    clear dependent st.
    find_copy_eapply_lem_hyp (first_succ_error_always_nonincreasing ex (addr_of j));
      eauto using live_node_in_active.
    find_copy_eapply_lem_hyp (pred_error_always_nonincreasing ex (addr_of a));
      eauto using live_node_in_active.
    find_copy_apply_lem_hyp (start_stabilize_with_first_successor_eventually ex (addr_of a));
      eauto.
    induction 0 as [[o [o' ex]] | o [o' ex]].
    - apply pred_improves_improves_abj_eventually; auto.
      eapply open_stabilize_request_a_after_p_eventually_improves_join_point;
        intuition eauto using has_pred_intro.
    - find_copy_apply_lem_hyp pred_same_until_improvement; auto.
      do 2 (eapply_lem_prop_hyp weak_until_Cons has_pred;
            inv_prop (measure_nonincreasing (first_succ_error (addr_of j)));
            intuition eauto using eventually_or_tl_intror, E0, E_next, pred_improves_improves_abj).
     find_copy_apply_lem_hyp first_succ_same_until_improvement; auto.
     do 2 (eapply_lem_prop_hyp weak_until_Cons has_first_succ;
           inv_prop (measure_nonincreasing (pred_error (addr_of a)));
           intuition eauto using eventually_or_tl_intror, E0, E_next, first_succ_improves_improves_abj).
      eapply E_next, IHeventually; invar_eauto.
  Qed.

  Lemma no_pred_merge_point :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

      merge_point (occ_gst (hd ex)) a b j ->
      has_pred (occ_gst (hd ex)) (addr_of j) None ->

      eventually pred_or_succ_improves_abj ex.
  Proof.
    intros.
    find_copy_eapply_lem_hyp (first_succ_error_always_nonincreasing ex (addr_of j));
      try now (inv_prop merge_point; intuition eauto using live_node_in_active).
    find_copy_eapply_lem_hyp (pred_error_always_nonincreasing ex (addr_of a));
      try now (inv_prop merge_point; intuition eauto using live_node_in_active).
    find_copy_apply_lem_hyp (start_stabilize_with_first_successor_eventually ex (addr_of a));
      try now (inv_prop merge_point; break_and); eauto.
    induction 0 as [[o [o' ex]] | o [o' ex]].
    - eapply open_stabilize_request_pred_None_eventually_improves_join_point;
        invcs_prop merge_point;
        intuition eauto using has_pred_intro.
    - find_copy_apply_lem_hyp merge_points_preserved_until_error_drops; auto.
      find_copy_apply_lem_hyp pred_same_until_improvement; auto.
      do 2 (eapply_lem_prop_hyp weak_until_Cons merge_point;
            intuition auto using E_next, E0).
      do 2 (eapply_lem_prop_hyp weak_until_Cons has_pred;
            inv_prop (measure_nonincreasing (first_succ_error (addr_of j)));
            intuition eauto using eventually_or_tl_intror, E0, E_next, pred_improves_improves_abj).
      eapply E_next, IHeventually; invar_eauto.
  Qed.

  Lemma error_decreases_at_merge_point :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->

      merge_point (occ_gst (hd ex)) a b j ->
      eventually pred_or_succ_improves_abj ex.
  Proof.
    intros.
    find_copy_apply_lem_hyp merge_points_preserved_until_error_drops; auto.
    find_copy_apply_lem_hyp joins_stop; auto using strong_local_fairness_weak.
    induction 0 as [ex | o [o' ex]].
    - inv_prop (merge_point (occ_gst (hd ex))); break_and.
      inv_prop (live_node (occ_gst (hd ex)) (addr_of j)); expand_def.
      destruct (pred ltac:(auto)) as [p |] eqn:?H.
      + pose proof (order_cases_le_gt a p); break_or_hyp.
        * eauto using a_before_pred_merge_point, eventually_or_tl_introl.
        * eauto using a_after_pred_merge_point.
      + eauto using no_pred_merge_point, has_pred_intro, eventually_or_tl_introl, eventually_or_tl_intror.
    - find_apply_lem_hyp weak_until_Cons; break_or_hyp;
        [now auto using E_next, E0|break_and].
      find_copy_apply_lem_hyp weak_until_Cons; break_or_hyp;
        [now auto using E_next, E0|break_and].
      eapply E_next, IHeventually;
        invar_eauto.
  Qed.

End MergePoint.

Lemma between_swap_not :
  forall x y z,
    y <> z ->
    between x z y ->
    ~ between x y z.
Proof.
  unfold not.
  intros.
  repeat invcs_prop between;
    solve [id_auto | eapply Chord.ChordIDSpace.lt_asymm; eauto].
Qed.

Lemma between_swap_not_xy :
  forall x y z,
    between x y z ->
    between y x z ->
    False.
Proof.
  unfold not.
  intros.
  repeat invcs_prop between;
    try solve [id_auto | eapply Chord.ChordIDSpace.lt_asymm; eauto].
  apply (Chord.ChordIDSpace.lt_irrefl y).
  eauto using Chord.ChordIDSpace.lt_trans.
Qed.

Lemma not_between_between_bool_equiv :
  forall x y z,
    between_bool x y z = false <->
    ~ between x y z.
Proof.
(*
This is easy.

DIFFICULTY: 1
USED: In unroll_between_neq_swap_false and phase two.
*)
Admitted.

Lemma unroll_between_neq_swap_false :
  forall x y z,
    y <> z ->
    unroll_between x z y = true ->
    unroll_between x y z = false.
Proof.
  unfold unroll_between.
  intros.
  repeat break_if; try congruence.
  apply not_between_between_bool_equiv, between_swap_not, between_between_bool_equiv; auto.
Qed.

Lemma id_eq_wf_ptr_eq :
  forall p q,
    id_of p = id_of q ->
    wf_ptr p ->
    wf_ptr q ->
    p = q.
Proof.
  intros.
  cut (addr_of p = addr_of q).
  {
    intros.
    destruct p, q; simpl in *; congruence.
  }
  apply Chord.hash_inj.
  by rewrite wf_ptr_hash_eq // wf_ptr_hash_eq.
Qed.

Lemma wf_ptr_neq_id_neq :
  forall p q,
    p <> q ->
    wf_ptr p ->
    wf_ptr q ->
    id_of p <> id_of q.
Proof.
  unfold not.
  intros.
  find_false.
  auto using id_eq_wf_ptr_eq.
Qed.

Lemma between_ends_neq_unroll_between :
  forall x y z,
    between_bool x y z = true ->
    x <> z ->
    unroll_between x y z = true.
Proof.
  intros.
  unfold unroll_between.
  repeat break_if; congruence.
Qed.

Lemma open_request_from_better_pred_eventually_improves_error :
  forall ex h p p',
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

    wf_ptr h ->
    wf_ptr p ->
    wf_ptr p' ->
    live_node (occ_gst (hd ex)) (addr_of p) ->
    live_node (occ_gst (hd ex)) (addr_of h) ->
    p <> h ->
    p <> p' ->
    h <> p' ->
    has_pred (occ_gst (hd ex)) (addr_of h) (Some p') ->
    has_first_succ (occ_gst (hd ex)) (addr_of p) h ->
    ptr_between p' p h ->
    open_stabilize_request_to (occ_gst (hd ex)) (addr_of p) (addr_of h) ->
    eventually (pred_improves h) ex.
Proof using.
  intros.
  eapply open_stabilize_request_a_after_p_eventually_improves_join_point; eauto.
  - unfold unroll_between_ptr, ChordIDParams.hash in *.
    apply Bool.negb_true_iff.
    apply unroll_between_neq_swap_false; auto using wf_ptr_neq_id_neq.
    unfold ptr_between in *.
    apply between_ends_neq_unroll_between;
      rewrite wf_ptr_hash_eq;
      auto using wf_ptr_neq_id_neq.
    apply between_between_bool_equiv.
    by apply between_rot_r; auto using wf_ptr_neq_id_neq.
  - unfold open_stabilize_request_to_first_succ. intros.
    cut (h = dst).
    { intros; subst; auto. }
    inv_prop has_first_succ.
    break_and.
    find_apply_lem_hyp hd_error_tl_exists. break_exists.
    congruence.
Qed.

Lemma succ_error_means_merge_point :
  forall gst,
    reachable_st gst ->
    ~ first_succs_correct gst ->
    exists a b j,
      merge_point gst a b j.
Proof.
(*
This leans on the entire ring invariant. Try reducing it to that first.

DIFFICULTY: Ryan
USED: Crucially in phase two.
*)
Admitted.

Definition wrong_pred (gst : global_state) (h : pointer) : Prop :=
  exists p p',
    has_pred gst (addr_of h) (Some p) /\
    better_pred gst h p p'.

Lemma better_succ_better_pred :
  forall gst h p p',
    live_node gst (addr_of h) ->
    id_of h <> id_of p ->
    better_succ gst h p p' ->
    better_pred gst p' p h.
Proof.
  unfold better_pred, better_succ.
  intuition.
  apply between_rot_r; auto.
Qed.

Lemma better_pred_better_succ :
  forall gst h p p',
    live_node gst (addr_of h) ->
    id_of h <> id_of p ->
    better_pred gst h p p' ->
    better_succ gst p' p h.
Proof.
  unfold better_pred, better_succ.
  intuition.
  apply between_rot_l; auto.
Qed.

Lemma best_pred_is_best_first_succ :
  forall gst p s,
    wf_ptr s ->
    live_node gst (addr_of s) ->
    pred_correct gst s (Some p) ->
    first_succ_correct gst p (Some s).
Proof.
  unfold first_succ_correct, pred_correct.
  intros.
  break_exists. break_and.
  find_injection.
  eexists; split; eauto; intros.
  assert (ptrId p' <> ptrId s).
  {
    intro.
    unfold not in *; find_false.
    apply id_eq_wf_ptr_eq; auto.
  }
  destruct (pointer_eq_dec x p').
  - subst.
    unfold better_succ, better_pred in *.
    intuition.
    apply between_xyx; auto.
  - auto using better_pred_better_succ; eauto.
Qed.

Lemma best_first_succ_is_best_pred :
  forall gst p s,
    wf_ptr p ->
    live_node gst (addr_of p) ->
    first_succ_correct gst p (Some s) ->
    pred_correct gst s (Some p).
Proof.
  unfold first_succ_correct, pred_correct.
  intros.
  break_exists. break_and.
  find_injection.
  eexists; split; eauto; intros.
  assert (ptrId p' <> ptrId p).
  {
    intro.
    unfold not in *; find_false.
    apply id_eq_wf_ptr_eq; auto.
  }
  destruct (pointer_eq_dec x p').
  - subst.
    unfold better_succ, better_pred in *.
    intuition.
    apply between_xyx; auto.
  - auto using better_succ_better_pred; eauto.
Qed.

Lemma correct_pred_exists :
  forall gst h,
    reachable_st gst ->
    exists p,
      wf_ptr p /\
      live_node gst (addr_of p) /\
      pred_correct gst h (Some p).
Proof.
(*
This is mostly a fact about the definition of pred_correct and shouldn't require
any invariants besides "there are at least 2 live joined nodes in the network".

DIFFICULTY: 3
USED: In phase two.
*)
Admitted.

Lemma correct_pred_unique :
  forall gst h p p',
    reachable_st gst ->
    live_node gst (addr_of p) ->
    live_node gst (addr_of p') ->
    pred_correct gst h (Some p) ->
    pred_correct gst h (Some p') ->
    p = p'.
Proof.
(*
This is mostly a fact about the definition of pred_correct and shouldn't require
any tricky invariants.

DIFFICULTY: 3
USED: In phase two.
*)
Admitted.

Lemma correct_first_succ_unique :
  forall gst h s s',
    reachable_st gst ->
    live_node gst (addr_of s) ->
    live_node gst (addr_of s') ->
    first_succ_correct gst h (Some s) ->
    first_succ_correct gst h (Some s') ->
    s = s'.
Proof.
(*
This is mostly a fact about the definition of first_succ_correct and shouldn't
require any tricky invariants.

DIFFICULTY: 3
USED: In phase two.
*)
Admitted.

Lemma first_succs_correct_succ_right :
  forall gst h s,
    reachable_st gst ->
    first_succs_correct gst ->
    wf_ptr h ->
    live_node gst (addr_of h) ->
    live_node gst (addr_of s) ->
    first_succ_correct gst h (Some s) ->
    has_first_succ gst (addr_of h) s.
Proof.
(*
This is really a proof about first_succ_correct and has_first_succ and shouldn't
require any invariants.

DIFFICULTY: 2
USED: In phase two.
*)
Admitted.

Lemma all_first_succs_correct_finds_pred :
  forall gst h,
    reachable_st gst ->
    first_succs_correct gst ->
    wf_ptr h ->
    live_node gst (addr_of h) ->
    exists p,
      wf_ptr p /\
      live_node gst (addr_of p) /\
      pred_correct gst h (Some p) /\
      has_first_succ gst (addr_of p) h.
Proof.
  intros.
  find_copy_eapply_lem_hyp correct_pred_exists.
  break_exists_exists.
  intuition eauto.
  eapply first_succs_correct_succ_right; auto.
  now apply best_pred_is_best_first_succ.
Qed.

Lemma open_stabilize_request_to_open_request_to :
  forall gst src dst,
    open_stabilize_request_to gst src dst ->
    open_request_to gst src dst GetPredAndSuccs.
Proof.
  unfold open_stabilize_request_to.
  intros.
  tauto.
Qed.

Lemma wrong_pred_not_correct_pred :
  forall gst h p_wrong p_correct,
    wrong_pred gst h ->
    has_pred gst (addr_of h) p_wrong ->
    pred_correct gst h (Some p_correct) ->
    p_wrong <> (Some p_correct).
Proof.
  intros.
  intro.
  subst.
  invcs_prop pred_correct.
  invcs_prop wrong_pred.
  expand_def.
  find_has_pred_eq.
  repeat find_injection.
  invcs_prop better_pred.
  break_and.
  assert (better_pred gst h x1 x).
  {
    find_eapply_prop better_pred; auto.
    intro; subst.
    eapply not_between_xxy; eauto.
  }
  inv_prop better_pred. expand_def.
  eapply between_swap_not_xy; eauto.
Qed.

Lemma error_decreases_when_succs_right :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

    wf_ptr h ->
    live_node (occ_gst (hd ex)) (addr_of h) ->
    first_succs_correct (occ_gst (hd ex)) ->
    wrong_pred (occ_gst (hd ex)) h ->
    eventually (pred_improves h) ex.
Proof.
  intros.
  find_copy_apply_lem_hyp all_first_succs_correct_finds_pred; auto.
  break_exists_name p. break_and.
  find_copy_apply_lem_hyp (start_stabilize_with_first_successor_eventually ex (addr_of p));
    eauto; try now (inv_prop merge_point; break_and).
  induction 0 as [[o [o' ex]] | o [o' ex]].
  - inv_prop wrong_pred. expand_def.
    simpl in *.
    assert (open_stabilize_request_to (occ_gst o) (addr_of p) (addr_of h)).
    {
      inv_prop has_first_succ. expand_def.
      find_apply_lem_hyp hd_error_tl_exists. break_exists.
      eauto.
    }
    destruct (In_dec addr_eq_dec (addr_of x) (failed_nodes (occ_gst o))).
    + inv_prop wrong_pred. expand_def.
      inv_prop better_pred. expand_def.
      find_has_pred_eq. repeat find_injection.
      admit.
    + eapply open_request_from_better_pred_eventually_improves_error.
      15:eauto.
      15:eauto.
      all:eauto.
      * unfold better_pred in *. intuition auto.
      * find_apply_lem_hyp (first_succ_never_self (occ_gst o) (addr_of p) h); auto.
        congruence.
      * inv_prop better_pred. expand_def.
        cut (Some x <> Some p); [congruence|].
        eapply wrong_pred_not_correct_pred; eauto.
      * find_apply_lem_hyp pred_never_self; auto.
        congruence.
      * unfold pred_correct in *.
        break_exists; intuition find_injection.
        unfold better_pred in *.
        apply H18; try by intuition eauto; subst.
        -- break_and.
           unfold ptr_between in *.
           intro; subst.
           find_eapply_lem_hyp wrong_pred_not_correct_pred; eauto.
           assert (addr_of h <> addr_of x1)
             by (eapply pred_never_self; eauto).
           assert (id_of h <> id_of x1)
             by (apply wf_ptr_neq_id_neq; auto; congruence).
           admit.
        -- admit.
  - inv_prop wrong_pred. expand_def.
    find_copy_eapply_lem_hyp pred_same_until_improvement; eauto.
    find_apply_lem_hyp weak_until_Cons. break_or_hyp.
    + apply E0; eauto.
    + apply E_next, IHeventually; invar_eauto; eauto;
        (* these are all manageable *)
        admit.
Admitted.

Lemma error_means_merge_point_or_wrong_pred :
  forall gst,
    phase_two_error gst > 0 ->
    reachable_st gst ->
    all_first_succs_best gst ->

    first_succs_correct gst /\
    (exists h, live_node gst (addr_of h) /\
          wf_ptr h /\
          wrong_pred gst h) \/
    exists a b j,
      merge_point gst a b j.
Proof.
(*
This should follow from first_succ_error_means_merge_point.

DIFFICULTY: 2
USED: In phase two.
*)
Admitted.

Lemma always_zero_phase_two_error_phase_two :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    always (now (measure_zero phase_two_error)) ex ->
    always (now phase_two) ex.
Proof.
  cofix c.
  intros.
  constructor.
  - destruct ex.
    inv_prop always.
    apply phase_two_zero_error_correct; auto.
  - destruct ex as [o [o' ex]].
    apply c; invar_eauto.
Qed.

Lemma continuously_zero_phase_two_error_phase_two :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    continuously (now (measure_zero phase_two_error)) ex ->
    continuously (now phase_two) ex.
Proof.
  intros until 2.
  intros.
  induction 0.
  - destruct s; simpl in *.
    apply E0, always_zero_phase_two_error_phase_two; eauto.
  - apply E_next.
    apply IHeventually; invar_eauto.
Qed.

Lemma phase_two_nonzero_error_causes_measure_drop :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ now circular_wait) ex ->
    always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
    always (now phase_one) ex ->

    nonzero_error_causes_measure_drop pred_and_first_succ_error ex.
Proof.
  intros; intro.
  assert (all_first_succs_best (occ_gst (hd ex)))
    by (inv_prop always; destruct ex; auto).
  find_apply_lem_hyp error_means_merge_point_or_wrong_pred; auto.
  expand_def.
  - find_eapply_lem_hyp error_decreases_when_succs_right; eauto.
    eexists; eauto using live_node_is_active, pred_improvement_suffices.
  - inv_prop merge_point; break_and.
    find_apply_lem_hyp error_decreases_at_merge_point; eauto.
    unfold pred_or_succ_improves_abj in *.
    repeat (find_apply_lem_hyp eventually_or_tl_or; auto; try break_or_hyp);
      eexists; eauto using live_node_is_active.
Qed.

Lemma phase_two_nonzero_error_continuous_drop :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ now circular_wait) ex ->
    always (now phase_one) ex ->
    continuously (nonzero_error_causes_measure_drop pred_and_first_succ_error) ex.
Proof.
  intros.
  find_copy_apply_lem_hyp joins_stop; auto.
  induction 0.
  - apply E0.
    generalize dependent s.
    cofix c.
    intros.
    destruct s.
    constructor.
    + apply phase_two_nonzero_error_causes_measure_drop; auto.
    + simpl.
      apply c; invar_eauto.
  - apply E_next, IHeventually; invar_eauto.
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
  apply continuously_zero_phase_two_error_phase_two; auto.
  apply local_measure_causes_measure_zero_continuosly;
    auto using phase_two_error_continuously_nonincreasing, phase_two_nonzero_error_continuous_drop.
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
