Require Import List.
Import ListNotations.
Require Import Omega.

Require Verdi.Coqlib.
Require Import StructTact.StructTactics.
Require Import InfSeqExt.infseq.

Require Import Chord.Chord.
Import Chord.Chord.Chord.
Import ChordIDSpace.
Require Import Chord.ChordProof.
Require Import Chord.ChordSemantics.
Import ChordSemantics.
Import ConstrainedChord.
Require Import Chord.ChordValidPointersInvariant.

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

Definition correct_succs
           (gst : global_state)
           (h : pointer)
           (succs : list pointer) : Prop :=
  forall s xs ys s',
    succs = xs ++ s :: ys ->
    ptr_between h s' s ->
    live gst s' ->
    In s' xs.

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

Definition phase_one (ex : infseq.infseq occurrence) :=
  lb_execution ex ->
  reachable_st (occ_gst (infseq.hd ex)) ->
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

Definition sum (l : list nat) :=
  fold_left Nat.add l 0.

Definition maybe_count_failed_nodes (gst : global_state) (h : addr) :=
  match sigma gst h with
  | Some st =>
    Some (succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st))
  | None =>
    None
  end.

Lemma maybe_count_failed_nodes_Some :
  forall gst h st n,
    maybe_count_failed_nodes gst h = Some n ->
    sigma gst h = Some st ->
    succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st) = n.
Proof.
  unfold maybe_count_failed_nodes.
  intros.
  break_match; congruence.
Qed.

Definition total_leading_failed_nodes (gst : global_state) : nat :=
  sum (FilterMap.filterMap (maybe_count_failed_nodes gst) (live_addrs gst)).

Definition nonempty_succ_lists (gst : global_state) : Prop :=
  forall h st,
    sigma gst h = Some st ->
    succ_list st <> [].

Lemma equal_folds_means_equal_acc :
  forall l a b,
    fold_left Nat.add l a = fold_left Nat.add l b ->
    a = b.
Proof.
  unfold sum.
  induction l.
  - easy.
  - simpl.
    intros.
    find_apply_hyp_hyp.
    omega.
Qed.

Lemma fold_left_acc_comm :
  forall a l,
    fold_left Nat.add l a = a + fold_left Nat.add l 0.
Proof.
  intros.
  generalize a.
  induction l.
  - easy.
  - simpl.
    intros.
    rewrite (IHl (_ + _)).
    rewrite (IHl a0).
    omega.
Qed.

(* TODO(ryan) move to structtact *)
Theorem list_strong_ind :
  forall A (P : list A -> Prop),
    (forall l, (forall l', length l' < length l -> P l') ->
        P l) ->
    forall l0 : list A, P l0.
Proof.
  intros.
  apply H.
  induction l0; simpl.
  - intros.
    now find_apply_lem_hyp Nat.nlt_0_r.
  - intros.
    apply H; intros.
    intuition eauto using lt_n_Sm_le, lt_le_trans.
Qed.

Lemma sum_of_nats_bounds_addends :
  forall l n,
    sum l = n ->
    forall x,
      In x l ->
      x <= n.
Proof.
  unfold sum.
  intro l.
  induction l using list_strong_ind.
  destruct l.
  - easy.
  - intros.
    find_apply_lem_hyp in_inv. break_or_hyp.
    + simpl.
      rewrite fold_left_acc_comm.
      omega.
    + simpl. rewrite fold_left_acc_comm.
      assert (x <= fold_left Nat.add l 0).
      { assert (H_len: length l < length (n :: l)) by auto.
        apply (H l H_len); auto.
      }
      omega.
Qed.

Lemma sum_of_nats_zero_means_all_zero :
  forall l,
    sum l = 0 ->
    forall x,
      In x l ->
      x = 0.
Proof.
  intros.
  symmetry.
  apply le_n_0_eq.
  eapply sum_of_nats_bounds_addends; eauto.
Qed.

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
    total_leading_failed_nodes gst = 0 ->
    live_addr gst h ->
    sigma gst h = Some st ->
    succ_list_leading_failed_nodes (failed_nodes gst) (succ_list st) = 0.
Proof.
  unfold total_leading_failed_nodes in *.
  intros.

  assert (In h (live_addrs gst)).
  {
    unfold live_addrs.
    apply filter_In.
    split.
    - live_addr_inv; easy.
    - now apply Coqlib.proj_sumbool_is_true.
  }

  assert (exists n, maybe_count_failed_nodes gst h = Some n).
  {
    unfold maybe_count_failed_nodes.
    find_rewrite.
    eexists; eauto.
  }
  break_exists_name failed_succs.

  replace failed_succs with 0 in *.
  - eapply maybe_count_failed_nodes_Some; eauto.
  - symmetry.
    eapply sum_of_nats_zero_means_all_zero; eauto.
    eapply FilterMap.filterMap_In; eauto.
Qed.

Definition zero_total_leading_failed_nodes (gst : global_state) : Prop :=
  total_leading_failed_nodes gst = 0.

Theorem zero_leading_failed_nodes_implies_all_first_succs_best :
  forall gst,
    reachable_after_churn gst ->
    (* total leading failed nodes says nothing about the length of successor lists *)
    nonempty_succ_lists gst ->
    zero_total_leading_failed_nodes gst ->
    all_first_succs_best gst.
Proof.
  unfold all_first_succs_best, first_succ_is_best_succ, zero_total_leading_failed_nodes.
  intros.
  find_eapply_lem_hyp live_inv;
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

Lemma zero_leading_failed_all_best :
    forall gst,
      reachable_after_churn gst ->
      (gpred_and
         nonempty_succ_lists
         zero_total_leading_failed_nodes) gst ->
      all_first_succs_best gst.
Proof.
  unfold gpred_and.
  intros.
  break_and.
  auto using zero_leading_failed_nodes_implies_all_first_succs_best.
Qed.

Theorem continuously_zero_total_leading_failed_nodes_implies_phase_one :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (infseq.hd ex)) ->
    infseq.continuously
      ((lift_gpred_to_ex zero_total_leading_failed_nodes) /\_
       (lift_gpred_to_ex nonempty_succ_lists))
      ex ->
    phase_one ex.
Proof.
Admitted.

(** In phase two we want to talk about the existence and number of better
    predecessors and better first successors to a node. We do this with the
    following functions.
    - better_* : Prop, which holds if a node is closer to h
    - better_*_bool : bool, which is true if some live node is a better pointer for h
    - *_correct : Prop, which holds if the pointer is globally correct
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
Definition better_first_succ (gst : global_state) (h s s' : pointer) : Prop :=
  live gst s' /\ ptr_between h s' s.

Definition better_first_succ_bool (h s s' : pointer) : bool :=
  ptr_between_bool h s' s.

Definition first_succ_correct (gst : global_state) (h : pointer) (p : option pointer) : Prop :=
  exists p0,
    p = Some p0 /\
    forall p', ~ better_first_succ gst h p0 p'.

Definition first_succ_error (gst : global_state) (h : pointer) (s : option pointer) : nat :=
  counting_opt_error gst s (better_first_succ_bool h).

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

Definition total_pred_and_first_succ_error (gst : global_state) : nat :=
  sum (map (fun pair =>
              let '(h, st) := pair in
              pred_and_first_succ_error gst h st)
           (live_ptrs_with_states gst)).

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

(** Generic reasoning about measures. *)
Definition measure_doesnt_increase (measure : global_state -> nat) (o o' : occurrence) : Prop :=
  measure (occ_gst o') <= measure (occ_gst o).

Definition measure_drops (measure : global_state -> nat) (o o' : occurrence) : Prop :=
  measure (occ_gst o') < measure (occ_gst o).

Definition measure_zero (measure : global_state -> nat) (o : occurrence) : Prop :=
  measure (occ_gst o) = 0.

Lemma measure_zero_elim :
  forall measure o,
    measure_zero measure o ->
    measure (occ_gst o) = 0.
Proof.
  easy.
Qed.

Lemma measure_decreasing_to_zero :
  forall measure ex,
    continuously (consecutive (measure_doesnt_increase measure)) ex ->
    weak_until (consecutive (measure_drops measure))
               (now (measure_zero measure))
               ex ->
    continuously (now (measure_zero measure)) ex.
Proof.
Admitted.

(* This is really an invariant. *)
Lemma phase_two_error_stable :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    continuously
      (consecutive
         (measure_doesnt_increase total_pred_and_first_succ_error))
      ex.
Proof.
Admitted.

(* This is the hard part. *)
Lemma phase_two_error_decreasing :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_until
      (consecutive
         (measure_drops total_pred_and_first_succ_error))
      (now
         (measure_zero total_pred_and_first_succ_error))
      ex.
Proof.
Admitted.

Lemma continuously_frame_monotonic :
  forall T (P Q J : infseq T -> Prop),
    (forall x s, J (Cons x s) -> J s) ->
    (forall s, J s -> always P s -> always Q s) ->
    forall s,
      J s ->
      continuously P s ->
      continuously Q s.
Proof.
  intros.
  apply eventually_monotonic with (P := always P) (J := J); auto.
Qed.

Lemma phase_two :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    continuously (lift_gpred_to_ex preds_and_first_succs_correct) ex.
Proof.
  intros.
  find_copy_apply_lem_hyp phase_two_error_stable; auto.
  find_copy_apply_lem_hyp phase_two_error_decreasing; auto.
  find_copy_apply_lem_hyp measure_decreasing_to_zero; auto.
  unfold lift_gpred_to_ex.
  eapply continuously_monotonic.
  - eapply now_monotonic; intros.
    apply phase_two_zero_error_correct.
    eauto using measure_zero_elim.
  - assumption.
Qed.

Definition ideal (gst : global_state) : Prop :=
  forall h st,
    live gst h ->
    sigma gst (addr_of h) = Some st ->
    correct_succs gst h (succ_list st) /\
    full_succs gst h (succ_list st) /\
    pred_correct gst h (pred st).

Definition deadlock_free : infseq.infseq occurrence -> Prop.
Admitted.

Theorem chord_stabilization :
  forall ex : infseq.infseq occurrence,
    reachable_st (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    weak_local_fairness ex ->
    deadlock_free ex ->
    infseq.eventually
      (infseq.always
         (fun ex' => (ideal (occ_gst (infseq.hd ex')))))
      ex.
Admitted.
