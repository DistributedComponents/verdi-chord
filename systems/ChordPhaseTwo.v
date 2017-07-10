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

Lemma now_hd :
  forall T (P : T -> Prop) ex,
    now P ex ->
    P (hd ex).
Proof.
  now destruct ex.
Qed.

Lemma always_now' :
  forall T (P : infseq T -> Prop) ex,
    always P ex ->
    P ex.
Proof.
  destruct ex.
  apply always_now.
Qed.

Lemma always_now_hd :
  forall T (P : T -> Prop) ex,
    always (now P) ex ->
    P (hd ex).
Proof.
  intros.
  destruct ex.
  now find_apply_lem_hyp always_Cons.
Qed.

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
    else S (length (live_ptrs gst))
  | None => S (length (live_ptrs gst))
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

Lemma filter_length_bound :
  forall A f (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l.
  - easy.
  - simpl.
    break_if; simpl; omega.
Qed.

Lemma len_eq_Slen_absurd :
  forall A f (l : list A),
    length (filter f l) <> S (length l).
Proof.
  intros.
  apply Nat.lt_neq.
  apply le_lt_n_Sm.
  apply filter_length_bound.
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
  repeat break_match;
    try solve [exfalso; eapply len_eq_Slen_absurd; eauto | tauto].
  left.
  eapply length_filter_by_cmp_same_eq; eauto;
    eapply live_In_live_ptrs; auto.
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
    forall p', ~ better_succ gst h p0 p'.

Definition first_succ_error (h : addr) (gst : global_state) : nat :=
  match sigma gst h with
  | Some st =>
    counting_opt_error gst (hd_error (succ_list st)) (better_succ_bool (make_pointer h))
  | None =>
    S (length (active_nodes gst))
  end.

Lemma pred_between_improves_error :
  forall h gst p p',
    ptr_between p p' (make_pointer h) ->
    live_node gst (addr_of p) ->
    live_node gst (addr_of p') ->
    counting_opt_error gst (Some p') (better_pred_bool (make_pointer h)) <
    counting_opt_error gst (Some p) (better_pred_bool (make_pointer h)).
Proof.
  intros.
  simpl.
  repeat break_if; try congruence.
  unfold better_pred_bool.
Admitted.

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

Lemma has_pred_intro :
  forall gst h p st,
    sigma gst h = Some st ->
    pred st = p ->
    has_pred gst h p.
Proof.
  unfold has_pred.
  eauto.
Qed.

Definition has_first_succ (gst : global_state) (h : addr) (s : pointer) : Prop :=
  exists st,
    sigma gst h = Some st /\
    hd_error (succ_list st) = Some s.

Lemma has_first_succ_intro :
  forall gst h s st,
    sigma gst h = Some st ->
    hd_error (succ_list st) = Some s ->
    has_first_succ gst h s.
Proof.
  intros.
  eexists; eauto.
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
Admitted.

Lemma pred_error_nonincreasing :
  forall gst l gst' h,
    reachable_st gst ->
    no_joins gst gst' ->
    labeled_step_dynamic gst l gst' ->
    In h (active_nodes gst) ->
    pred_error h gst' <= pred_error h gst.
Proof.
Admitted.

Lemma first_succ_error_nonincreasing :
  forall gst l gst' h,
    reachable_st gst ->
    no_joins gst gst' ->
    labeled_step_dynamic gst l gst' ->
    In h (active_nodes gst) ->
    first_succ_error h gst' <= first_succ_error h gst.
Proof.
Admitted.

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

Lemma pred_error_bound :
  forall ex h st n,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    sigma (occ_gst (hd ex)) h = Some st ->
    pred_error h (occ_gst (hd ex)) = n ->
    always (now (fun occ => pred_error h (occ_gst occ) <= n)) ex.
Proof.
Admitted.

Lemma first_succ_error_bound :
  forall ex h st n,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    sigma (occ_gst (hd ex)) h = Some st ->
    first_succ_error h (occ_gst (hd ex)) = n ->
    always (now (fun occ => first_succ_error h (occ_gst occ) <= n)) ex.
Proof.
Admitted.

Ltac find_always_and_tl :=
  match goal with
  | H : always ?P ?ex, H' : always ?Q ?ex |- _ =>
    pose proof (always_and_tl H H');
    clear H H'
  end.

Ltac find_continuously_and_tl :=
  match goal with
  | H : continuously ?P ?ex, H' : continuously ?Q ?ex |- _ =>
    pose proof (continuously_and_tl H H');
    clear H H'
  end.

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
  consecutive (measure_decreasing (pred_error (addr_of h))).

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
    measure_nonincreasing (first_succ_error h) o o' ->
    measure_decreasing (pred_error h) o o' ->
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
    eapply first_succ_error_nonincreasing;
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
      wf_ptr h ->
      wf_ptr p ->
      has_pred (occ_gst (hd ex)) (addr_of h) None ->
      In Notify (channel (occ_gst (hd ex)) (addr_of p) (addr_of h)) ->
      eventually (pred_improves h) ex.
Proof.
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
  a <> j /\
  b <> j /\
  a <> b /\
  live_node gst (addr_of a) /\
  live_node gst (addr_of b) /\
  live_node gst (addr_of j).

Definition merge_point_dec :
  forall gst a b j,
    {merge_point gst a b j} + {~ merge_point gst a b j}.
Proof.
Admitted.

Lemma merge_point_wf :
  forall gst a b j,
    (merge_point gst a b j -> wf_ptr a) /\
    (merge_point gst a b j -> wf_ptr b) /\
    (merge_point gst a b j -> wf_ptr j).
Proof.
  unfold merge_point.
  tauto.
Qed.

Lemma weak_until_eventually_until :
  forall T (P Q : infseq T -> Prop) s,
    weak_until P Q s ->
    eventually Q s ->
    until P Q s.
Proof.
  intros.
  induction 0.
  - now apply U0.
  - find_apply_lem_hyp weak_until_Cons.
    intuition auto using U0, U_next.
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
                 (pred_or_succ_improves (make_pointer h)) ex.
  Proof.
  Admitted.

  Lemma no_pred_merge_point' :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->

      merge_point (occ_gst (hd ex)) a b j ->
      has_pred (occ_gst (hd ex)) (addr_of j) None ->

      until
        (now (fun o => has_pred (occ_gst o) (addr_of j) None))
        (pred_or_succ_improves j)
        ex.
  Proof.
    intros.
    find_copy_apply_lem_hyp (start_stabilize_with_first_successor_eventually ex (addr_of a));
      eauto.
    2:now inv_prop merge_point.
    induction 0.
    - inv_prop merge_point; break_and.
      clear dependent b.
      find_apply_lem_hyp now_hd.
      find_eapply_lem_hyp (open_stabilize_request_eventually_gets_response s); eauto.

  Admitted.

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

      eventually (pred_or_succ_improves j) ex.
  Proof.
    intros.
    eapply until_eventually.
    eapply no_pred_merge_point'; eauto.
  Qed.

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

  Lemma ptr_between_ptr_between_bool :
    forall a b c,
      ptr_between a b c ->
      ptr_between_bool a b c = true.
  Proof.
    unfold ptr_between, ptr_between_bool.
    intros.
    now apply between_between_bool_equiv.
  Qed.

  Ltac find_false :=
    match goal with
    | H : _ |- _ => exfalso; apply H
    end.

  Lemma not_ptr_between :
    forall a b c,
      ~ ptr_between a b c ->
      ptr_between_bool a b c = false.
  Proof.
    intros.
    destruct (ptr_between_bool _ _ _) eqn:?H; [|reflexivity].
    find_false.
    now apply between_between_bool_equiv.
  Qed.

  Lemma ptr_between_bool_false :
    forall a b c,
      ptr_between_bool a b c = false ->
      ~ ptr_between a b c.
  Proof.
    unfold ptr_between, ptr_between_bool.
    intros.
    now apply between_bool_false_not_between.
  Qed.

  Lemma ptr_between_bool_true :
    forall a b c,
      ptr_between_bool a b c = true ->
      ptr_between a b c.
  Proof.
    unfold ptr_between, ptr_between_bool.
    intros.
    now apply between_bool_between.
  Qed.

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
    rewrite handle_msg_busy_is_handle_query_req_busy in *; auto;
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

  Ltac find_has_pred_eq :=
    match goal with
    | H : has_pred _ _ _ |- _ =>
      eapply has_pred_eq in H;
      [|clear H; now eauto]
    end.

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
  Admitted.

  Ltac eapply_prop' P :=
    match goal with
    | H: P _ |- _ => eapply H
    | H: P _ _ |- _ => eapply H
    | H: P _ _ _ |- _ => eapply H
    | H: P _ _ _ _ |- _ => eapply H
    | H: context[P] |- _ => eapply H
    end.

  Lemma hd_error_None :
    forall A (l : list A),
      hd_error l = None ->
      l = [].
  Proof.
    now destruct l.
  Qed.

  Lemma successors_are_live_nodes :
    forall gst h s,
      reachable_st gst ->
      all_first_succs_best gst ->
      has_first_succ gst h s ->
      live_node gst (addr_of s).
  Proof using.
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
      intuition break_exists_exists.
      intuition.
      repeat find_apply_lem_hyp always_now'.
      invcs_prop and_tl; break_exists.
      invc_prop pred_not_worse; break_and.
      invc_prop pred_not_worse; break_and.
      repeat find_has_pred_eq.
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

  Theorem ptr_correct :
    forall gst h st,
      reachable_st gst ->
      sigma gst h = Some st ->
      ptr st = make_pointer h.
  Proof.
  Admitted.

  Ltac id_auto :=
    auto using BetweenMono, BetweenWrapL, BetweenWrapR, Chord.ChordIDSpace.lt_asymm, Chord.ChordIDSpace.lt_irrefl.

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
    pose proof (Chord.ChordIDSpace.lt_total x z).
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
        merge_point (occ_gst (hd ex)) a b j ->
        a >? p = true ->
        open_request_to (occ_gst (hd ex)) (addr_of a) (addr_of j) GetPredAndSuccs ->
        now (occurred (RecvMsg (addr_of j) (addr_of a) (GotPredAndSuccs (Some p) js))) ex ->
        next (now (fun o => In Notify (channel (occ_gst o) (addr_of a) (addr_of j)))) ex.
  Proof.
    intros.
    destruct ex as [o [o' ex]].
    inv_prop merge_point; break_and.
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

  Lemma wf_ptr_hash_eq :
    forall p,
      wf_ptr p ->
      hash (addr_of p) = id_of p.
  Proof.
    auto.
  Qed.

  Lemma recv_GotPredAndSuccs_with_a_after_p_causes_improvement :
    forall o ex,
      lb_execution (Cons o ex) ->
      reachable_st (occ_gst o) ->
      strong_local_fairness (Cons o ex) ->
      always (~_ (now circular_wait)) (Cons o ex) ->
      always (now phase_one) (Cons o ex) ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
      merge_point (occ_gst o) a b j ->
      merge_point (occ_gst (hd ex)) a b j ->

      forall p js,
        has_pred (occ_gst (hd ex)) (addr_of j) (Some p) ->
        a >? p = true ->
        open_request_to (occ_gst o) (addr_of a) (addr_of j) GetPredAndSuccs ->
        now (occurred (RecvMsg (addr_of j) (addr_of a) (GotPredAndSuccs (Some p) js))) (Cons o ex) ->
        eventually (pred_improves j) ex.
  Proof.
    intros.
    find_apply_lem_hyp recv_GotPredAndSuccs_with_a_after_p_causes_Notify; simpl in *; invar_eauto.
    destruct ex as [o' ex]; simpl in *.
    rewrite (wf_ptr_eq j) by (eapply merge_point_wf; eauto).
    eapply notify_when_pred_worse_eventually_improves; invar_eauto.
    inv_prop merge_point; break_and.
    apply not_between_between.
    unfold unroll_between_ptr in *.
    apply Bool.negb_true_iff.
    unfold ChordIDParams.hash in *.
    rewrite !(wf_ptr_hash_eq a), !(wf_ptr_hash_eq j) in *; auto.
  Qed.

  Lemma live_nodes_not_clients :
    forall gst h,
      reachable_st gst ->
      live_node gst h ->
      ~ client_addr h.
  Proof.
  Admitted.

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

  Lemma eventually_or_tl_intror :
    forall T (P Q : infseq T -> Prop) s,
      eventually Q s ->
      eventually (P \/_ Q) s.
  Proof.
    intros until 0.
    apply eventually_monotonic_simple.
    firstorder.
  Qed.

  Lemma eventually_or_tl_introl :
    forall T (P Q : infseq T -> Prop) s,
      eventually P s ->
      eventually (P \/_ Q) s.
  Proof.
    intros until 0.
    apply eventually_monotonic_simple.
    firstorder.
  Qed.

  Lemma open_request_with_response_on_wire_closed_or_preserved :
    forall gst l gst' src dst req res,
      labeled_step_dynamic gst l gst' ->
      open_request_to gst src dst req ->
      request_response_pair req res ->
      In res (channel gst dst src) ->
      RecvMsg dst src res = l \/
      open_request_to gst' src dst req /\
      In res (channel gst' dst src).
  Proof.
  Admitted.

  Lemma incoming_GotPredAndSuccs_with_a_after_p_causes_improvement :
    forall ex,
      lb_execution ex ->
      reachable_st (occ_gst (hd ex)) ->
      strong_local_fairness ex ->
      always (~_ (now circular_wait)) ex ->
      always (now phase_one) ex ->
      always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex ->
      merge_point (occ_gst (hd ex)) a b j ->

      forall p js,
        has_pred (occ_gst (hd ex)) (addr_of j) (Some p) ->
        a >? p = true ->
        open_request_to (occ_gst (hd ex)) (addr_of a) (addr_of j) GetPredAndSuccs ->
        In (GotPredAndSuccs (Some p) js) (channel (occ_gst (hd ex)) (addr_of j) (addr_of a)) ->
        eventually pred_or_succ_improves_abj ex.
  Proof.
    intros.
    inv_prop merge_point; break_and.
    find_apply_lem_hyp channel_contents.
    inv_prop (live_node (occ_gst (hd ex)) (addr_of a)).
    expand_def.

    find_eapply_lem_hyp RecvMsg_eventually_occurred; invar_eauto;
      eauto using strong_local_fairness_weak, live_node_in_nodes, live_node_means_state_exists, live_nodes_not_clients.
    induction 0 as [[o [o' ex]] | o [o' ex]].
    - find_copy_apply_lem_hyp merge_points_preserved_until_error_drops; auto.
      find_copy_apply_lem_hyp pred_same_until_improvement; auto.
      eapply_lem_prop_hyp weak_until_Cons merge_point.
      break_or_hyp; [now auto using E_next, E0|].
      break_and.
      eapply_lem_prop_hyp weak_until_Cons merge_point.
      break_or_hyp; [now auto using E_next, E0|].
      break_and.

      eapply_lem_prop_hyp weak_until_Cons has_pred.
      break_or_hyp; [now eauto using eventually_or_tl_intror, E0, E_next|].
      break_and.
      eapply_lem_prop_hyp weak_until_Cons has_pred.
      break_or_hyp; [now eauto using eventually_or_tl_intror, E0, E_next|].
      break_and.

      apply E_next.
      do 2 apply eventually_or_tl_intror.
      apply pred_improvement_suffices; invar_eauto.
      eapply recv_GotPredAndSuccs_with_a_after_p_causes_improvement;
        invar_eauto.
    - find_copy_apply_lem_hyp merge_points_preserved_until_error_drops; auto.
      find_copy_apply_lem_hyp pred_same_until_improvement; auto.

      eapply_lem_prop_hyp weak_until_Cons merge_point.
      break_or_hyp; [now auto using E_next, E0|].
      break_and.
      eapply_lem_prop_hyp weak_until_Cons merge_point.
      break_or_hyp; [now auto using E_next, E0|].
      break_and.
      eapply_lem_prop_hyp weak_until_Cons has_pred.
      break_or_hyp; [now eauto using eventually_or_tl_intror, E0, E_next|].
      break_and.
      eapply_lem_prop_hyp weak_until_Cons has_pred.
      break_or_hyp; [now eauto using eventually_or_tl_intror, E0, E_next|].
      break_and.
      simpl in *.
      inv_prop lb_execution.
      find_copy_apply_lem_hyp channel_contents.
      eapply_lem_prop_hyp open_request_with_response_on_wire_closed_or_preserved labeled_step_dynamic;
        eauto using pair_GetPredAndSuccs.
      break_or_hyp; break_and.
      + apply E_next.
        do 2 apply eventually_or_tl_intror.
        apply pred_improvement_suffices; invar_eauto.
        eapply recv_GotPredAndSuccs_with_a_after_p_causes_improvement;
          invar_eauto.
      + find_apply_lem_hyp channel_contents.
        inv_prop (merge_point (occ_gst o')); break_and.
        inv_prop (live_node (occ_gst o') (addr_of a)); expand_def.
        apply E_next.
        apply IHeventually; invar_eauto.
  Qed.

  (* Lemma a_after_pred_merge_point_response_incoming : *)
  (*   forall ex, *)
  (*     lb_execution ex -> *)
  (*     reachable_st (occ_gst (hd ex)) -> *)
  (*     strong_local_fairness ex -> *)
  (*     always (~_ (now circular_wait)) ex -> *)
  (*     always (now phase_one) ex -> *)
  (*     always (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex -> *)

  (*     forall st p jp js, *)
  (*       merge_point (occ_gst (hd ex)) a b j -> *)
  (*       sigma (occ_gst (hd ex)) (addr_of j) = Some st -> *)
  (*       pred st = Some p -> *)
  (*       a >? p = true -> *)
  (*       In (GotPredAndSuccs (Some p) js) (channel (occ_gst (hd ex)) (addr_of j) (addr_of a)) -> *)
  (*       until *)
  (*         (now (fun o => has_pred (occ_gst o) (addr_of j) (Some p))) *)
  (*         (pred_improves j) ex. *)
  (* Proof. *)
  (* Admitted. *)

  Lemma a_after_pred_merge_point_stabilize_open :
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
        a >? p = true ->
        open_stabilize_request_to_first_succ (occ_gst (hd ex)) (addr_of a) ->
        until
          (now (fun o => has_pred (occ_gst o) (addr_of j) (Some p)))
          (pred_improves j) ex.
  Proof using a b j.
    (* intros. *)
    (* inv_prop merge_point; break_and. *)
    (* find_copy_apply_lem_hyp (open_stabilize_request_eventually_gets_response ex (addr_of a)); auto. *)
    (* induction 0. *)
    (* - find_apply_lem_hyp now_hd; expand_def. *)
    (*   eapply a_after_pred_merge_point_response_incoming; eauto. *)
    (* -  *)
  Admitted.


  Lemma a_after_pred_merge_point_precise :
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
        a >? p = true ->
        until
          (now (fun o => has_pred (occ_gst o) (addr_of j) (Some p)))
          (pred_improves j) ex.
  Proof.
    intros.
    inv_prop merge_point; break_and.
    find_eapply_lem_hyp notify_when_pred_worse_eventually_improves;
      eauto using has_pred_intro.
  Admitted.

  Lemma a_after_pred_merge_point :
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
        a >? p = true ->
        eventually (pred_or_succ_improves j) ex.
  Proof.
    intros.
    invc_prop merge_point; break_and.
    find_copy_apply_lem_hyp (start_stabilize_with_first_successor_eventually ex (addr_of a)); auto.
    induction 0.
    2:admit.

    destruct s as [o s]; simpl in *.
    invc_prop has_first_succ; break_and.
    inv_prop has_first_succ; break_and.
    find_apply_lem_hyp hd_error_tl_exists; break_exists.
    find_eapply_lem_hyp open_stabilize_request_to_first_succ_elim; eauto.

    find_eapply_lem_hyp open_stabilize_request_eventually_gets_response; eauto.
    induction 0.
    2:admit.
    destruct s0.
    (* find_copy_eapply_lem_hyp *)
    (*   (stabilize_with_worse_pred_completes (Cons o s) (addr_of a) (addr_of j)); *)
    (*   eauto. *)
    (* destruct s in *. *)
    (* simpl in *. *)

    (*   open_stabilize_request_eventually_gets_response *)
    (* find_copy_eapply_lem_hyp a_after_pred_merge_point_precise; eauto. *)
    (* inv_prop merge_point; break_and. *)
    (* apply pred_improvement_suffices; *)
    (*   eauto using until_eventually. *)
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
    find_copy_apply_lem_hyp joins_stop; auto using strong_local_fairness_weak.
    induction 0 as [ex | o [o' ex]].
    - inv_prop merge_point; break_and.
      inv_prop (live_node (occ_gst (hd ex)) (addr_of j)); expand_def.
      destruct (pred ltac:(auto)) as [p |] eqn:?H.
      + pose proof (order_cases_le_gt a p); break_or_hyp;
          eauto using a_before_pred_merge_point, a_after_pred_merge_point.
      + eauto using no_pred_merge_point, has_pred_intro.
    - destruct (merge_point_dec (occ_gst o') a b j).
      + elim IHeventually; invar_eauto; intuition eauto using E_next.
      + apply merge_point_gone_improved_something; auto.
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
  - eapply phase_two_error_continuously_nonincreasing;
      eauto using strong_local_fairness_weak.
  - apply E0; eapply phase_two_nonzero_error_continuous_drop; eauto.
Qed.
