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
Require Import Chord.ChannelLemmas.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.
Require Import Chord.LabeledMeasures.

Require Import Chord.LiveNodesNotClients.
Require Import Chord.ValidPointersInvariant.
Require Import Chord.QueryInvariant.
Require Import Chord.NodesAlwaysHaveLiveSuccs.
Require Import Chord.NodesNotJoinedHaveNoSuccessors.
Require Import Chord.NodesHaveState.
Require Import Chord.PtrCorrectInvariant.
Require Import Chord.QueriesEventuallyStop.
Require Import Chord.QueryTargetsJoined.
Require Import Chord.FirstSuccNeverSelf.
Require Import Chord.SuccessorNodesAlwaysValid.
Require Import Chord.PredNeverSelfInvariant.
Require Import Chord.PtrsJoined.
Require Import Chord.RingCorrect.
Require Import Chord.ChordCorrectPhaseOne.
Require Import Chord.HashInjective.

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
    reachable_st gst ->
    (forall x y, id_of x <> id_of y -> better_bool x y = false -> better_bool y x = true) ->
    wf_ptr p ->
    counting_opt_error gst (Some p) better_bool = 0 ->
    forall p',
      p <> p' ->
      In (addr_of p) (nodes gst) ->
      live_node gst (addr_of p') ->
      wf_ptr p' ->
      better_bool p' p = true.
Proof.
  unfold counting_opt_error.
  intros.
  repeat break_match; try omega.
  find_apply_lem_hyp length_zero_iff_nil.
  find_apply_lem_hyp live_In_live_ptrs; eauto.
  find_apply_lem_hyp hash_injective_invariant.
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
    replace (id_of p) with (hash (addr_of p)) in *.
    replace (id_of p') with (hash (addr_of p')) in *.
    find_apply_lem_hyp In_live_ptrs_live.
    eapply_prop hash_injective_on; eauto.
  }
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

(*
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
*)

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
  auto using better_pred_intro.
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
  auto using better_succ_intro.
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

(*
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
    eapply_lem_prop_hyp counting_opt_error_zero_implies_correct counting_opt_error;
      eauto using better_pred_bool_antisymmetric.
    * assert (wf_ptr x /\ live_node gst (addr_of x)) by admit; try tauto.
      rewrite <- wf_ptr_eq in * by auto.
      by apply better_pred_bool_true_better_pred; tauto.
    * by admit.
    * by admit.
  - find_copy_apply_lem_hyp phase_two_zero_error_has_first_succ; auto.
    break_exists_exists; expand_def; split; try find_rewrite; auto.
    unfold first_succ_error in *; break_match; try congruence.
    intros.
    find_injection.
    repeat find_rewrite.
    rewrite <- wf_ptr_eq in * by auto.
    eapply_lem_prop_hyp counting_opt_error_zero_implies_correct counting_opt_error;
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
*)

(*
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
Admitted.
*)


Definition no_joins (gst gst' : global_state) :=
  forall h,
    live_node gst' h ->
    live_node gst h.

Definition n_unjoined_nodes gst := length (dedup addr_eq_dec (nodes gst)) -
                                   length (dedup addr_eq_dec (live_addrs gst)).

Lemma length_dedup_le :
  forall A (eq_dec : forall x y : A, {x = y} + {x <> y}) l1 l2,
    (forall x, In x l1 -> In x l2) ->
    length (dedup eq_dec l1) <= length (dedup eq_dec l2).
Proof.
  intros.
  apply NoDup_incl_length; eauto using NoDup_dedup.
  unfold incl.
  intros.
  eauto using dedup_In, in_dedup_was_in.
Qed.

Lemma n_unjoined_nodes_nonincreasing :
  forall ex,
    lb_execution ex ->
    always (consecutive (measure_nonincreasing n_unjoined_nodes)) ex.
Proof.
  cofix c. intros. inv_prop lb_execution.
  apply Always; eauto.
  simpl. unfold measure_nonincreasing.
  unfold n_unjoined_nodes.
  find_copy_apply_lem_hyp labeled_step_dynamic_preserves_nodes.
  repeat find_rewrite.
  cut (length (dedup addr_eq_dec (live_addrs (occ_gst o))) <=
       length (dedup addr_eq_dec (live_addrs (occ_gst o'))));
    [omega|].
  apply length_dedup_le.
  intros.
  eauto using In_live_addrs_live, live_addr_In_live_addrs, LiveNodesStayLive.live_node_invariant.
Qed.

Lemma NoDup_cons_elim :
  forall A (x : A) l,
    NoDup (x :: l) ->
    NoDup l /\
    ~ In x l.
Proof.
  intros. inv_prop NoDup; auto.
Qed.

Lemma incl_cons :
  forall A (x : A) l1 l2,
    incl (x :: l1) l2 ->
    incl l1 l2.
Proof.
  unfold incl.
  intros. simpl in *. intuition.
Qed.
  

Lemma NoDup_list_diff :
  forall A (eq_dec : forall x y : A, {x = y} + {x <> y}) (l2 l1 : list A),
    NoDup l1 ->
    NoDup l2 ->
    incl l1 l2 ->
    length l2 = length l1 ->
    incl l2 l1.
Proof.
  unfold incl. intros.
  destruct (in_dec eq_dec a l1); intuition.
  assert (incl (a :: l1) l2).
  + unfold incl. simpl. intuition. subst. auto.
  + find_apply_lem_hyp NoDup_incl_length; simpl in *; try omega.
    constructor; auto.
Qed.

Lemma length_live_addrs_le_length_nodes :
  forall gst,
    length (dedup addr_eq_dec (live_addrs gst)) <=
    length (dedup addr_eq_dec (nodes gst)).
Proof.
  intros. apply NoDup_incl_length; eauto using NoDup_dedup.
  unfold incl. intros. apply dedup_In.
  find_apply_lem_hyp in_dedup_was_in.
  unfold live_addrs in *. find_apply_lem_hyp filter_In. intuition.
Qed.

Lemma unjoined_nodes_no_joins :
  forall gst l gst',
    labeled_step_dynamic gst l gst' ->
    n_unjoined_nodes gst = n_unjoined_nodes gst' ->
    no_joins gst gst'.
Proof.
  unfold no_joins, n_unjoined_nodes. simpl. intros.
  pose proof length_live_addrs_le_length_nodes gst.
  pose proof length_live_addrs_le_length_nodes gst'.
  find_copy_apply_lem_hyp labeled_step_dynamic_preserves_nodes.
  repeat find_rewrite.
  match goal with
  | H : ?a - ?b = ?a - ?c |- _ =>
    assert ((b <= a) /\ (c <= a)) by intuition
  end. intuition.
  assert (length (dedup addr_eq_dec (live_addrs gst')) =
          length (dedup addr_eq_dec (live_addrs gst))) by omega.
  find_apply_lem_hyp NoDup_list_diff; eauto using NoDup_dedup, addr_eq_dec.
  + unfold incl in *.
    apply In_live_addrs_live. apply (in_dedup_was_in addr_eq_dec).
    eauto using In_live_addrs_live, live_addr_In_live_addrs, dedup_In.
  + unfold incl. intros.
    eapply dedup_In. find_apply_lem_hyp in_dedup_was_in.
    eauto using In_live_addrs_live, live_addr_In_live_addrs, LiveNodesStayLive.live_node_invariant.
Qed.


Lemma eventually_n_unjoined_nodes_stable :
  forall ex,
    lb_execution ex ->
    exists x,
      continuously (now (fun o => n_unjoined_nodes (occ_gst o) = x)) ex.
Proof.
  intros. eauto using n_unjoined_nodes_nonincreasing, measure_nonincreasing_eventually_stable.
Qed.

Lemma always_now_consecutive :
  forall T P (s : infseq T),
    always (now P) s ->
    always (consecutive (fun o o' => P o /\ P o')) s.
Proof.
  cofix. intros.
  destruct s.
  constructor.
  - destruct s. simpl. do 2 inv_prop always. simpl in *. auto.
  - simpl. inversion H. simpl in *. eauto.
Qed.

Lemma always_monotonic_complex :
  forall T (J P Q : infseq T -> Prop),
    (forall s, J s -> P s -> Q s) ->
    (forall x s, J (Cons x s) -> J s) ->
    forall s,
      J s ->
      always P s ->
      always Q s.
Proof.
  intros T J P Q PQ Jinvar.  cofix cf. intros (x, s) HJ HP.
  generalize (@always_Cons _ x s P HP); simpl; intros (a1, a2).
  constructor; simpl; eauto.
Qed.

Lemma consecutive_monotonic_extra :
  forall T (J P Q : T -> T -> Prop),
    (forall x y, J x y -> P x y -> Q x y) ->
    forall s,
      consecutive J s ->
      consecutive P s ->
      consecutive Q s.
Proof.
  intros T J P Q JPQ (x, (y, s)) nJ nP; simpl. eauto.
Qed.

Definition is_step x y :=
  exists l, labeled_step_dynamic (occ_gst x) l (occ_gst y).

Theorem joins_stop :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    always (~_ (now circular_wait)) ex ->
    strong_local_fairness ex ->
    continuously (consecutive (fun o o' => no_joins (occ_gst o) (occ_gst o'))) ex.
Proof.
  intros.
  find_copy_eapply_lem_hyp eventually_n_unjoined_nodes_stable.
  break_exists.
  unfold continuously in *.
  eapply eventually_monotonic with (J := lb_execution).
  4:eauto.
  all:eauto using lb_execution_invar.
  intros.
  find_eapply_lem_hyp always_now_consecutive.
  eapply always_monotonic_complex with (J := lb_execution).
  4:eauto.
  all:eauto using lb_execution_invar.
  intros. destruct s0. destruct s0. simpl in *.
  inv_prop lb_execution. intuition. subst.
  eauto using unjoined_nodes_no_joins.
(*
Since nodes only set joined=true some time after they are added to the network
and no new nodes are added to the network in an lb_execution, joins have to
eventually stop. That implies this lemma.

DIFFICULTY: Ryan
USED: In phase two.
*)
Qed.


(*
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
*)

(*
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
*)

(*
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
*)

(*
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
*)

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

(*
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
*)

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

(*
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
*)

(*
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
*)

(*
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
*)

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

(*
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
*)

Lemma has_first_succ_stable :
  forall gst l gst' h s,
    preds_and_first_succs_correct gst ->
    labeled_step_dynamic gst l gst' ->
    has_first_succ gst h s ->
    has_first_succ gst' h s.
Proof.
Admitted.

Lemma open_request_to_preserved :
  forall gst gst' h s m st st',
    open_request_to gst h s m ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    cur_request st = cur_request st' ->
    (forall dst m, In (Request dst m) (timeouts gst h) -> In (Request dst m) (timeouts gst' h)) \/
    In (Request s m) (timeouts gst' h) ->
    open_request_to gst' h s m.
Proof.
  unfold open_request_to.
  intros; expand_def;
    intuition (repeat eexists; eauto);
    congruence.
Qed.

Lemma has_first_succ_preserved :
  forall gst gst' h s st st',
    has_first_succ gst h s ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    succ_list st = succ_list st' ->
    has_first_succ gst' h s.
Proof.
  intros.
  inv_prop has_first_succ; expand_def.
  eapply has_first_succ_intro;
    eauto; congruence.
Qed.

Lemma no_response_when_busy :
  forall src dst msg st st' sends nts cts,
    cur_request st' <> None ->
    recv_handler src dst st msg = (st', sends, nts, cts) ->
    forall h res,
      response_payload res ->
      res <> Busy ->
      res <> Pong ->
      ~ In (h, res) sends.
Proof.
  intros.
  repeat handler_def; simpl; eauto;
    try intuition (inv_prop response_payload); simpl in *; congruence.
Qed.
Hint Resolve no_response_when_busy.

Lemma all_first_succs_best_first_succ_not_failed :
  forall gst h s,
    all_first_succs_best gst ->
    has_first_succ gst h s ->
    live_node gst h ->
    ~ In (addr_of s) (failed_nodes gst).
Proof.
Admitted.

Lemma not_request_is_response :
  forall p,
    is_request p = false ->
    response_payload p \/ p = Notify.
Proof.
  destruct p;
    solve [eauto
          |simpl; congruence].
Qed.

Lemma open_stabilize_request_until_step_recv_half :
  forall gst h j,
    reachable_st gst ->
    all_first_succs_best gst ->
    wf_ptr j ->
    has_first_succ gst h j ->
    open_request_to gst h (addr_of j) GetPredAndSuccs ->
    live_node gst h ->
    (forall p succs, ~ In (GotPredAndSuccs p succs) (channel gst (addr_of j) h)) ->
    forall gst' src dst msg,
      labeled_step_dynamic gst (RecvMsg src dst msg) gst' ->
      all_first_succs_best gst' ->
      open_request_to gst' h (addr_of j) GetPredAndSuccs /\
      has_first_succ gst' h j.
Proof.
  intros.
  inv_prop labeled_step_dynamic;
    unfold label_input, label_output in *;
    try handler_def; try congruence.
  destruct (addr_eq_dec (fst (snd m)) h).
  - assert (forall m,
               m = msg0 ->
               ~response_payload m).
    {
      intros; subst.
      assert (In m (msgs gst)) by (repeat find_rewrite; eauto with datatypes).
      destruct m as [src' [dst' p']].
      find_apply_lem_hyp sent_message_means_in_nodes_or_client; auto.
      break_or_hyp.
      + cut (no_responses (channel gst src' dst')).
        {
          find_injection.
          assert (In p' (channel gst src' dst')).
          apply in_msgs_in_channel.
          repeat find_rewrite; eauto with datatypes.
          eauto.
        }
        find_apply_lem_hyp nodes_have_state; eauto.
        break_exists_name st__src.
        inv_prop open_request_to; expand_def.
        simpl in *.
        find_copy_eapply_lem_hyp (query_message_ok'_invariant gst ltac:(eauto) dst' src'); eauto.
        inv_prop query_message_ok';
          try inv_prop query_message_ok;
          try congruence; eauto.
        * repeat (find_rewrite || find_injection).
          inv_prop request_response_pair.
          exfalso; intuition eauto.
        * repeat (find_rewrite || find_injection).
          inv_prop request_response_pair.
          exfalso; intuition eauto.
      + intuition.
        repeat (find_rewrite || find_injection).
        inv_prop client_payload; inv_prop response_payload.
    }
    split.
    + inv_prop open_request_to; expand_def.
    handler_def; handler_def; try congruence.
    * inv_prop open_request_to; expand_def.
      eapply open_request_to_preserved; simpl; rewrite_update; eauto.
      find_eapply_lem_hyp cur_request_preserved_by_do_delayed_queries; congruence.
      handler_def;
        eauto using remove_preserve with datatypes.
    * inv_prop open_request_to; expand_def.
      eapply open_request_to_preserved; simpl; rewrite_update; eauto.
      -- repeat handler_def; simpl; congruence.
      -- intros.
        right.
        do 2 handler_def;
          simpl; autorewrite with list;
            eauto using remove_preserve with datatypes.
    * inv_prop open_request_to; expand_def.
      eapply open_request_to_preserved; simpl; rewrite_update; eauto.
      -- repeat handler_def; simpl; congruence.
      -- intros; right.
        do 2 handler_def;
          simpl; autorewrite with list;
            eauto using remove_preserve with datatypes.
    * assert ((snd (snd m)) = Notify \/ ~response_payload (snd (snd m)))
        by (find_injection; eauto).
      find_eapply_lem_hyp not_request_is_response.
      tauto.
    * assert ((snd (snd m)) = Notify \/ ~response_payload (snd (snd m)))
        by (find_injection; eauto).
      find_eapply_lem_hyp not_request_is_response.
      tauto.
    + eapply has_first_succ_preserved; simpl; rewrite_update;
        try eassumption.
      repeat find_rewrite; eauto.
      eauto.
      handler_def.
      find_apply_lem_hyp succ_list_preserved_by_do_delayed_queries.
      handler_def; try congruence.
      * repeat handler_def; simpl in *; congruence.
      * repeat handler_def; simpl in *; congruence.
      * assert (~response_payload (snd (snd m)))
          by (find_injection; eauto).
        find_eapply_lem_hyp not_request_is_response.
        tauto.
  - split.
    + inv_prop open_request_to; expand_def.
      eapply open_request_to_preserved; eauto;
        simpl; rewrite_update; auto.
    + inv_prop has_first_succ; expand_def.
      eapply has_first_succ_preserved; eauto.
      simpl; rewrite_update; auto.
Qed.

Lemma open_stabilize_request_until_step :
  forall gst h j,
    reachable_st gst ->
    all_first_succs_best gst ->
    wf_ptr j ->
    has_first_succ gst h j ->
    open_request_to gst h (addr_of j) GetPredAndSuccs ->
    live_node gst h ->
    (forall p succs, ~ In (GotPredAndSuccs p succs) (channel gst (addr_of j) h)) ->
    forall gst' l,
      labeled_step_dynamic gst l gst' ->
      all_first_succs_best gst' ->
      open_request_to gst' h (addr_of j) GetPredAndSuccs /\
      has_first_succ gst' h j /\
      (forall p succs, ~ In (GotPredAndSuccs p succs) (channel gst' (addr_of j) h)) \/
      open_request_to gst' h (addr_of j) GetPredAndSuccs /\
      has_first_succ gst' h j /\
      (exists p succs,
          In (GotPredAndSuccs p succs)
             (channel gst' (addr_of j) h) /\
          has_pred gst' (addr_of j) p /\
          has_succs gst' (addr_of j) succs).
Proof.
  intros.
  assert (~ In (addr_of j) (failed_nodes gst))
    by eauto using all_first_succs_best_first_succ_not_failed.
  assert (h <> addr_of j)
    by eauto using first_succ_never_self.
  assert (~ client_addr (addr_of j)).
  {
    eapply nodes_not_clients; eauto.
    find_apply_lem_hyp successor_nodes_always_valid.
    inv_prop has_first_succ.
    eapply H; intuition eauto.
    destruct (succ_list _); simpl in *; intuition congruence.
  }
  inv_prop labeled_step_dynamic.
  - left.
    destruct (addr_eq_dec h0 h); subst.
    + inv_prop open_request_to; expand_def.
      inv_prop has_first_succ; break_and.
      unfold timeout_constraint in *.
      inv_prop _timeout_constraint;
        try solve [
              repeat break_and_goal;
              [eapply open_request_to_preserved; simpl; rewrite_update; eauto;
               [simpl in *; repeat (find_rewrite || find_injection);
                repeat handler_def; congruence
               |repeat handler_def; simpl; try congruence;
                intuition eauto using remove_preserve]
              |eapply has_first_succ_preserved; simpl; rewrite_update; eauto;
               repeat (handler_def; try congruence)
              |intuition;
               find_apply_lem_hyp in_channel_in_msgs;
               find_apply_lem_hyp in_app_or;
               unfold send in *;
               break_or_hyp; eauto;
               find_apply_lem_hyp in_map_iff; expand_def]].
      assert (Request dst p = (Request (addr_of j) GetPredAndSuccs))
        by eauto using at_most_one_request_timeout_invariant.
      find_injection.
      tauto.
    + repeat break_and_goal;
        unfold open_request_to, has_first_succ; simpl; rewrite_update; eauto.
      intuition.
      find_apply_lem_hyp in_channel_in_msgs.
      find_apply_lem_hyp in_app_or.
      unfold send in *.
      break_or_hyp; eauto.
      find_apply_lem_hyp in_map_iff; expand_def.
      repeat handler_def;
        unfold make_request, send_keepalives in *;
        try find_apply_lem_hyp option_map_Some; expand_def;
        try find_apply_lem_hyp in_concat; expand_def;
        try find_apply_lem_hyp in_map_iff; expand_def;
        try find_apply_lem_hyp option_map_None; expand_def;
          simpl in *; try intuition congruence.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
  - remember (apply_handler_result (fst (snd m)) (st, ms, newts, clearedts) [ChordSemantics.e_recv m] (update_msgs gst (xs ++ ys))) as gst'.
    assert (open_request_to gst' h (addr_of j) GetPredAndSuccs /\
            has_first_succ gst' h j)
      by (handler_def; eauto using open_stabilize_request_until_step_recv_half).
    cut ((forall p succs,
             ~ In (GotPredAndSuccs p succs) (channel gst' (addr_of j) h)) \/
         (exists p succs,
             In (GotPredAndSuccs p succs) (channel gst' (addr_of j) h) /\
             has_pred gst' (addr_of j) p /\ has_succs gst' (addr_of j) succs));
      [tauto|].
    destruct (addr_eq_dec (fst (snd m)) h); subst.
    + left; intuition.
      find_apply_lem_hyp channel_contents.
      simpl in *.
      find_apply_lem_hyp in_app_or; intuition.
      * find_apply_lem_hyp in_map_iff; expand_def.
        unfold send in *; find_injection.
        congruence.
      * find_eapply_prop channel.
        apply channel_contents.
        find_rewrite.
        intuition eauto with *.
    + remember (apply_handler_result (fst (snd m)) (st, ms, newts, clearedts) [ChordSemantics.e_recv m] (update_msgs gst (xs ++ ys))) as gst'.
      destruct (addr_eq_dec (fst (snd m)) (addr_of j)).
      * cut ((forall p succs, ~ In (h, GotPredAndSuccs p succs) ms) \/
             (exists p succs, In (h, GotPredAndSuccs p succs) ms /\
                         has_pred gst' (addr_of j) p /\
                         has_succs gst' (addr_of j) succs)).
        { intros; break_or_hyp; [left|right]; intuition.
          - find_apply_lem_hyp channel_contents.
            simpl in *.
            repeat find_rewrite.
            find_apply_lem_hyp in_app_or; break_or_hyp.
            + find_apply_lem_hyp in_map_iff; expand_def.
              unfold send in *; find_injection; eauto.
            + find_eapply_prop channel.
              apply channel_contents.
              repeat find_rewrite.
              find_apply_lem_hyp in_app_or; break_or_hyp;
                eauto with datatypes.
          - expand_def.
            do 2 eexists.
            repeat split; eauto.
            apply channel_contents.
            apply in_or_app; left.
            apply in_map_iff.
            repeat find_rewrite.
            eexists; eauto.
        }
        assert (Hexdec: {Forall (fun x => forall p succs, fst x <> h \/ snd x <> GotPredAndSuccs p succs) ms} +
                        {Exists (fun x => ~ (forall p succs, fst x <> h \/ snd x <> GotPredAndSuccs p succs)) ms}).
        {
          apply Forall_Exists_dec.
          destruct x as [h' msg];
            destruct (addr_eq_dec h h'); subst;
              destruct msg; simpl;
                try (left; intuition congruence).
          right; intro Hneq; do 2 insterU Hneq; break_or_hyp; eauto.
        }
        destruct Hexdec.
        -- pose proof (iffLR (Forall_forall _ _) f).
           left; intuition.
           eapply_prop_hyp In In.
           tauto.
        -- find_apply_lem_hyp Exists_exists; expand_def.
           right.
           destruct x, (addr_eq_dec a h), _p; subst;
             try solve [simpl in *; exfalso; eapply_prop not; intuition congruence
                       |exfalso; intuition].
           do 2 eexists; split; eauto.
           handler_def.
           find_eapply_lem_hyp recv_handler_GotPredAndSuccs_response_accurate; eauto.
           break_and; split;
             [eapply has_pred_intro
             |eapply has_succs_intro];
             simpl; try rewrite_update; eauto.
      * left.
        unfold open_request_to, has_first_succ.
        inv_prop open_request_to; inv_prop has_first_succ; expand_def.
        repeat break_and_goal;
          simpl; rewrite_update;
            try solve [eauto|do 3 eexists; eauto].
        intuition.
        find_eapply_lem_hyp in_channel_in_msgs.
        find_apply_lem_hyp in_app_or; break_or_hyp.
        -- find_apply_lem_hyp in_map_iff; expand_def.
           unfold send in *; congruence.
        -- simpl in *.
           find_apply_lem_hyp in_app_or.
           find_eapply_prop channel.
           eapply in_msgs_in_channel.
           repeat find_rewrite.
           intuition eauto with datatypes.
  - left; repeat break_and_goal; eauto.
    intuition.
    find_eapply_prop channel.
    find_apply_lem_hyp in_channel_in_msgs.
    apply in_msgs_in_channel.
    simpl in *; unfold send in *.
    eauto.
    intuition eauto using in_channel_in_msgs, in_msgs_in_channel.
    find_injection; tauto.
  - left; repeat break_and_goal; eauto.
    intuition.
    find_apply_lem_hyp in_channel_in_msgs.
    simpl in *; unfold send in *.
    find_eapply_prop channel.
    apply in_msgs_in_channel.
    repeat find_rewrite.
    find_apply_lem_hyp in_app_or.
    intuition eauto with datatypes.
Admitted.

Lemma open_stabilize_request_until_response_weak :
  forall ex h j,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    wf_ptr j ->
    live_node (occ_gst (hd ex)) h ->
    has_first_succ (occ_gst (hd ex)) h j ->
    open_request_to (occ_gst (hd ex)) h (addr_of j) GetPredAndSuccs ->
    (forall p succs,
        ~ In (GotPredAndSuccs p succs)
          (channel (occ_gst (hd ex)) (addr_of j) h)) ->
    weak_until
      (now (fun occ =>
              (forall p succs,
                  ~ In (GotPredAndSuccs p succs)
                     (channel (occ_gst occ) (addr_of j) h)) /\
              open_request_to (occ_gst occ) h (addr_of j) GetPredAndSuccs /\
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
  cofix c.
  intros.
  destruct ex as [o [o' ex]].
  inv_prop lb_execution.
  assert (phase_one o)
    by repeat (invcs_prop always; eauto).
  assert (phase_one o')
    by repeat (invcs_prop always; eauto).
  find_eapply_lem_hyp open_stabilize_request_until_step; try eassumption.
  break_or_hyp.
  - break_and.
    constructor;
      solve [simpl in *; eauto|apply c; invar_eauto].
  - constructor;
      solve [simpl in *; eauto|constructor; auto].
Qed.
Hint Resolve open_stabilize_request_until_response_weak.

Lemma open_stabilize_request_eventual_response :
  forall ex h j,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    wf_ptr j ->
    has_first_succ (occ_gst (hd ex)) h j ->
    open_request_to (occ_gst (hd ex)) h (addr_of j) GetPredAndSuccs ->
    (forall p succs,
        ~ In (GotPredAndSuccs p succs)
          (channel (occ_gst (hd ex)) (addr_of j) h)) ->
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
Admitted.
Hint Resolve open_stabilize_request_eventual_response.

Lemma open_stabilize_request_until_response :
  forall ex h j,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    wf_ptr j ->
    live_node (occ_gst (hd ex)) h ->
    has_first_succ (occ_gst (hd ex)) h j ->
    open_request_to (occ_gst (hd ex)) h (addr_of j) GetPredAndSuccs ->
    (forall p succs,
        ~ In (GotPredAndSuccs p succs)
          (channel (occ_gst (hd ex)) (addr_of j) h)) ->
    until
      (now (fun occ =>
              (forall p succs,
                  ~ In (GotPredAndSuccs p succs)
                     (channel (occ_gst occ) (addr_of j) h)) /\
              open_request_to (occ_gst occ) h (addr_of j) GetPredAndSuccs /\
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
  intros.
  eapply until_weak_until_eventually; eauto.
Qed.

Lemma open_stabilize_request_eventually_gets_response :
  forall ex h j,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    always (now phase_one) ex ->
    wf_ptr j ->
    live_node (occ_gst (hd ex)) h ->
    has_first_succ (occ_gst (hd ex)) h j ->
    open_stabilize_request_to_first_succ (occ_gst (hd ex)) h ->
    (forall p succs,
        ~ In (GotPredAndSuccs p succs)
          (channel (occ_gst (hd ex)) (addr_of j) h)) ->
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

Lemma has_first_succ_sigma :
  forall gst gst' h s,
    has_first_succ gst h s ->
    sigma gst h = sigma gst' h ->
    has_first_succ gst' h s.
Proof.
  intros.
  unfold has_first_succ in *.
  break_exists_exists. congruence.
Qed.

Lemma has_first_succ_succ_list :
  forall gst gst' h s st st',
    has_first_succ gst h s ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    succ_list st = succ_list st' ->
    has_first_succ gst' h s.
Proof.
  intros.
  unfold has_first_succ in *.
  break_exists. intuition. repeat find_rewrite.
  find_inversion. eexists; intuition eauto. congruence.
Qed.


(* query invariants for live_successor_changed_improves *)
Lemma stabilize_query_to_first_succ :
  forall gst,
    reachable_st gst ->
    forall h s st p,
      sigma gst h = Some st ->
      cur_request st = Some (s, Stabilize, p) ->
      has_first_succ gst h s.
Proof.
  induction 1; intros.
  - unfold initial_st in *.
    find_apply_lem_hyp sigma_initial_st_start_handler; eauto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; congruence.
  - inversion H0; subst; eauto.
    + subst. simpl in *.
      update_destruct; subst; rewrite_update; simpl in *; eauto.
      * find_inversion. simpl in *. congruence.
      * eapply has_first_succ_sigma; eauto.
        simpl in *. now rewrite_update.
    + eapply has_first_succ_sigma; eauto.
    + simpl in *.
      update_destruct; subst; rewrite_update; simpl in *; eauto;
        [|eapply has_first_succ_sigma; simpl in *; rewrite_update; eauto].
      repeat (handler_def || handler_simpl;
              try solve [eapply has_first_succ_sigma; eauto; simpl in *;
                         rewrite_update; congruence];
              try solve [eapply has_first_succ_succ_list; simpl; rewrite_update; eauto]).
      * unfold has_first_succ. simpl. rewrite_update. eexists; intuition eauto.
        simpl. find_apply_lem_hyp option_map_Some.
        break_exists. intuition.
        congruence.
      * unfold has_first_succ. simpl. rewrite_update. eexists; intuition eauto.
        simpl. find_apply_lem_hyp option_map_Some.
        break_exists. intuition.
        congruence.
    + repeat (handler_def || handler_simpl;
              try (update_destruct; subst; rewrite_update);
              repeat find_rewrite;
              repeat find_inversion; simpl in *; eauto; try congruence;
              try solve [eapply has_first_succ_sigma; eauto; simpl in *;
                         rewrite_update; congruence];
              try solve [eapply has_first_succ_succ_list; simpl; rewrite_update; eauto]).
    + eapply has_first_succ_sigma; eauto.
    + eapply has_first_succ_sigma; eauto.
Qed.

Lemma hd_error_make_succs :
  forall x l,
    hd_error (make_succs x l) = Some x.
Proof.
  intros. unfold make_succs. unfold chop_succs.
  assert (exists n, SUCC_LIST_LEN = S n). {
    destruct SUCC_LIST_LEN eqn:?; eauto.
    pose proof succ_list_len_lower_bound; omega.
  }
  break_exists. find_rewrite. auto.
Qed.

Lemma stabilize2_query_to_better_succ :
  forall gst,
    reachable_st gst ->
    forall h s s' st p,
      sigma gst h = Some st ->
      cur_request st = Some (s', Stabilize2 s', p) ->
      has_first_succ gst h s ->
      ptr_between (ptr st) s' s.
Proof.
induction 1; intros.
  - unfold initial_st in *.
    find_apply_lem_hyp sigma_initial_st_start_handler; eauto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; congruence.
  - inversion H0; subst; eauto.
    + subst. simpl in *.
      update_destruct; subst; rewrite_update; simpl in *; eauto.
      * find_inversion. simpl in *. congruence.
      * find_eapply_lem_hyp has_first_succ_sigma; eauto.
        simpl. now rewrite_update.
    + simpl in *.
      update_destruct; subst; rewrite_update; simpl in *; eauto;
        [|find_eapply_lem_hyp has_first_succ_sigma; simpl; eauto;
          now rewrite_update].
      repeat (handler_def || handler_simpl;
              try solve [find_eapply_lem_hyp has_first_succ_sigma; eauto;
                         simpl; now rewrite_update];
              try solve [eapply_lem_prop_hyp has_first_succ_succ_list has_first_succ;
                         simpl in *; rewrite_update; eauto]).
    + repeat (handler_def || handler_simpl;
              try (update_destruct; subst; rewrite_update);
              repeat find_rewrite;
              repeat find_inversion; simpl in *; eauto; try congruence;
              try solve [find_eapply_lem_hyp has_first_succ_sigma; eauto;
                         simpl; now rewrite_update];
              try solve [eapply_lem_prop_hyp has_first_succ_succ_list has_first_succ;
                         simpl in *; rewrite_update; eauto]).
      unfold has_first_succ in *.
      break_exists. simpl in *.
      intuition.  rewrite_update. find_inversion.
      simpl in *.
      find_rewrite_lem hd_error_make_succs. congruence.
Qed.

Lemma has_first_succ_inj :
  forall gst h s s',
    has_first_succ gst h s ->
    has_first_succ gst h s' ->
    s = s'.
Proof.
  intros.
  unfold has_first_succ in *.
  break_exists. intuition. congruence.
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
  intros. invcs H0; simpl in *; eauto.
  - destruct (addr_eq_dec h0 h);
      [| find_eapply_lem_hyp has_first_succ_sigma; simpl; rewrite_update;
         eauto using has_first_succ_inj].
    subst. unfold timeout_handler_l in *.
    break_let. find_inversion.
    repeat (handler_def || handler_simpl;
            try solve [eapply_lem_prop_hyp has_first_succ_sigma @update; simpl; rewrite_update;
                         eauto using has_first_succ_inj];
              try solve [eapply_lem_prop_hyp has_first_succ_succ_list @update;
                         simpl; rewrite_update;
                         eauto using has_first_succ_inj]).
    * find_copy_eapply_lem_hyp has_first_succ_intro; repeat find_rewrite; simpl; eauto.
      find_eapply_lem_hyp stabilize_query_to_first_succ; eauto.
      eapply_lem_prop_hyp has_first_succ_inj s; [|eauto]. subst.
      solve_by_inversion. (* on the timeout constraint *)
    * find_copy_eapply_lem_hyp has_first_succ_intro; repeat find_rewrite; simpl; eauto.
      find_eapply_lem_hyp stabilize_query_to_first_succ; eauto.
      eapply_lem_prop_hyp has_first_succ_inj s; [|eauto]. subst.
      solve_by_inversion. (* on the timeout constraint *)
  - destruct (addr_eq_dec (fst (snd m)) h);
      [| find_eapply_lem_hyp has_first_succ_sigma; simpl; rewrite_update;
         eauto using has_first_succ_inj].
    subst.
    repeat (handler_def || handler_simpl;
              repeat find_rewrite;
              repeat find_inversion; simpl in *; eauto; try congruence;
              try solve [eapply_lem_prop_hyp has_first_succ_sigma @update; simpl; rewrite_update;
                         eauto using has_first_succ_inj];
              try solve [eapply_lem_prop_hyp has_first_succ_succ_list @update;
                         simpl; rewrite_update;
                         eauto using has_first_succ_inj]).
    + exfalso.
      find_eapply_lem_hyp stabilize_query_to_first_succ; eauto.
      eapply_lem_prop_hyp has_first_succ_inj s; [|eauto]; subst.
      unfold has_first_succ in *.
      break_exists; simpl in *; rewrite_update; intuition; find_inversion.
      simpl in *.
      find_rewrite_lem hd_error_make_succs.
      find_inversion. repeat find_rewrite. find_inversion.
      find_apply_lem_hyp hd_error_tl_exists. break_exists.
      find_eapply_lem_hyp WfPtrSuccListInvariant.wf_ptr_succ_list_invariant; eauto.
      repeat find_reverse_rewrite.
      find_apply_lem_hyp wf_ptr_eq. auto.
    + exfalso.
      find_eapply_lem_hyp stabilize_query_to_first_succ; eauto.
      eapply_lem_prop_hyp has_first_succ_inj s; [|eauto]; subst.
      unfold has_first_succ in *.
      break_exists; simpl in *; rewrite_update; intuition; find_inversion.
      simpl in *.
      find_rewrite_lem hd_error_make_succs.
      find_inversion. repeat find_rewrite. find_inversion.
      find_apply_lem_hyp hd_error_tl_exists. break_exists.
      find_eapply_lem_hyp WfPtrSuccListInvariant.wf_ptr_succ_list_invariant; eauto.
      repeat find_reverse_rewrite.
      find_apply_lem_hyp wf_ptr_eq. auto.
    + exfalso.
      find_eapply_lem_hyp stabilize_query_to_first_succ; eauto.
      eapply_lem_prop_hyp has_first_succ_inj s; [|eauto]; subst.
      unfold has_first_succ in *.
      break_exists; simpl in *; rewrite_update; intuition; find_inversion.
      simpl in *.
      find_rewrite_lem hd_error_make_succs.
      find_inversion. repeat find_rewrite. find_inversion.
      find_apply_lem_hyp hd_error_tl_exists. break_exists.
      find_eapply_lem_hyp WfPtrSuccListInvariant.wf_ptr_succ_list_invariant; eauto.
      repeat find_reverse_rewrite.
      find_apply_lem_hyp wf_ptr_eq. auto.
    + find_copy_eapply_lem_hyp stabilize2_param_matches; eauto. subst.
      find_eapply_lem_hyp stabilize2_query_to_better_succ; eauto.
      find_copy_apply_lem_hyp ptr_correct; auto.
      repeat find_rewrite.
      unfold has_first_succ in *.
      break_exists; simpl in *; rewrite_update; intuition; find_inversion.
      simpl in *. find_rewrite_lem hd_error_make_succs. congruence.
    + exfalso.
      find_eapply_lem_hyp cur_request_join2_not_joined; eauto.
      find_eapply_lem_hyp nodes_not_joined_have_no_successors; eauto.
      unfold has_first_succ in *. break_exists; intuition.
      repeat find_rewrite. find_inversion. find_rewrite.
      simpl in *. discriminate.
  - find_eapply_lem_hyp has_first_succ_sigma; simpl; eauto.
    find_eapply_lem_hyp has_first_succ_inj; eauto.
  - find_eapply_lem_hyp has_first_succ_sigma; simpl; eauto.
    find_eapply_lem_hyp has_first_succ_inj; eauto.
(*
This says that a new live successor at a host has to be between the host and its
old successor, provided the old one is live.

DIFFICULTY: 3
USED: In phase two (a_before_pred_merge_point).
*)
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

  (*
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
  Implied by pred error nonincreasing (or maybe the other way around?)

  DIFFICULTY: 4
  USED: In phase two.
  *)
  Admitted.
  *)

  (*
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
  *)

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
    inv_prop query_request.
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

  (*
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
  *)

  Ltac eapply_prop' P :=
    match goal with
    | H: P _ |- _ => eapply H
    | H: P _ _ |- _ => eapply H
    | H: P _ _ _ |- _ => eapply H
    | H: P _ _ _ _ |- _ => eapply H
    | H: context[P] |- _ => eapply H
    end.

  (*
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
        * exfalso.
          find_apply_lem_hyp hd_error_None.
          eapply (nodes_have_nonempty_succ_lists (occ_gst o')); invar_eauto.
  Qed.
  *)

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

  (*
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
  *)

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

  (*
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
  *)

  (*
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
  *)

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

  (*
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
  *)

  (*
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
      simpl in *.
      eapply_lem_prop_hyp open_request_with_response_on_wire_closed_or_preserved labeled_step_dynamic;
        try eassumption; eauto using pair_GetPredAndSuccs.
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
  *)

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
  intuition.
  - find_apply_lem_hyp between_between_bool_equiv. congruence.
  - destruct (between_bool x y z) eqn:?; auto.
    find_apply_lem_hyp between_between_bool_equiv. congruence.
Qed.

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

(*
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
    apply unroll_between_neq_swap_false.
    admit.
    unfold ptr_between in *.
    apply between_ends_neq_unroll_between;
      rewrite wf_ptr_hash_eq;
      admit.
  - unfold open_stabilize_request_to_first_succ. intros.
    cut (h = dst).
    { intros; subst; auto. }
    inv_prop has_first_succ.
    break_and.
    find_apply_lem_hyp hd_error_tl_exists. break_exists.
    congruence.
Admitted.
*)

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

(*
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
    admit.
  }
  destruct (pointer_eq_dec x p').
  - subst.
    unfold better_succ, better_pred in *.
    intuition.
    apply between_xyx; auto.
  - auto using better_pred_better_succ; eauto.
Admitted.
*)

Fixpoint max_cmp {A : Type} (cmp : A -> A -> bool) (l : list A) (x : option A) :=
  match l with
  | [] => x
  | y :: l =>
    match x with
    | None => max_cmp cmp l (Some y)
    | Some x => if cmp x y then max_cmp cmp l (Some y) else max_cmp cmp l (Some x)
    end
  end.

Lemma max_cmp_ret :
  forall A cmp (l : list A) x,
  (exists y,
      max_cmp cmp l x = Some y) \/
  l = [] /\ max_cmp cmp l x = x.
Proof.
  induction l; intros; auto; try congruence.
  left. simpl.
  repeat break_match; subst; simpl in *; eauto;
  match goal with
  | |- context [ max_cmp _ _ (Some ?x) ] =>
    specialize (IHl (Some x))
  end; intuition; subst; simpl; eauto.
Qed.

Lemma max_cmp_empty :
  forall A cmp (l : list A) x,
    max_cmp cmp l x = None ->
    l = [].
Proof.
  intros. specialize (max_cmp_ret A cmp l x); intros; intuition.
  break_exists; congruence.
Qed.

Lemma between_trans :
  forall a b c d,
    ptr_between a b c ->
    ptr_between a c d ->
    ptr_between a b d.
Proof.
  intros.
  invcs H; invcs H0;
    try solve [econstructor; eauto using lt_trans];
    congruence.
Qed.


Lemma between_trans' :
  forall a b c d,
    ptr_between a b c ->
    ptr_between b d c ->
    ptr_between a d c.
Proof.
  intros.
  invcs H; invcs H0;
    try solve [econstructor; eauto using lt_trans];
    congruence.
Qed.

Lemma ptr_between_bool_trans :
  forall a b c d,
    ptr_between_bool a b c = true ->
    ptr_between_bool a c d = true ->
    ptr_between_bool a b d = true.
Proof.
  eauto using ptr_between_ptr_between_bool, ptr_between_bool_true, between_trans.
Qed.

Lemma ptr_between_bool_trans' :
  forall a b c d,
    ptr_between_bool a b c = true ->
    ptr_between_bool b d c = true ->
    ptr_between_bool a d c = true.
Proof.
  eauto using ptr_between_ptr_between_bool, ptr_between_bool_true, between_trans'.
Qed.

Lemma max_cmp_in :
  forall A cmp (l : list A) x r,
    max_cmp cmp l x = Some r ->
    x = Some r \/
    In r l.
Proof.
  induction l; intros; auto.
  simpl in *; repeat break_match; auto; subst;
    find_apply_hyp_hyp; intuition; solve_by_inversion.
Qed.

Lemma max_cmp_correct :
  forall A cmp (wf : A -> Prop),
    (forall a b c, wf a -> wf b -> wf c -> cmp a b = true -> cmp b c = true -> cmp a c = true) ->
    (forall a b, wf a -> wf b -> cmp a b = true -> cmp b a = false) ->
    (forall a b, wf a -> wf b -> cmp a b = true \/ cmp b a = true \/ a = b) ->
    forall (l : list A) x r,
      (forall a, In a l -> wf a) ->
      (forall x', x = Some x' -> wf x') ->
      max_cmp cmp l x = Some r ->
      forall y,
        (In y l \/ x = Some y) ->
        r = y \/ cmp y r = true.
Proof.
  intros A cmp wf Htrans Hasymm Htotal.
  induction l; intros; simpl in *.
  - intuition. subst. solve_by_inversion.
  - repeat break_match; subst.
    + specialize (IHl (Some a) r). concludes.
      forward IHl; [intros; find_inversion; auto|].
      repeat concludes.
      intuition; subst; eauto.
      find_inversion.
      specialize (IHl a). concludes.
      intuition; subst; auto.
      destruct (cmp y r) eqn:?; auto.
      erewrite Htrans in Heqb0; eauto.
      find_apply_lem_hyp max_cmp_in. intuition.
    + specialize (IHl (Some a0) r). concludes.
      forward IHl; [intros; find_inversion; auto|].
      repeat concludes.
      intuition; subst; eauto.
      specialize (IHl a0). concludes.
      intuition; subst; auto.
      * specialize (Htotal y a0); repeat concludes; intuition; try congruence.
      * assert (cmp y a0 = true \/ y = a0) by
          (specialize (Htotal y a0); repeat concludes; intuition; congruence).
        intuition; subst; eauto. right.
        eapply (Htrans y a0 r); eauto.
        find_apply_lem_hyp max_cmp_in. intuition.
    + intuition; subst; eauto; try congruence.
      * specialize (IHl (Some y) r). repeat concludes.
        forward IHl; [intros; find_inversion; auto|].
        eauto.
      * specialize (IHl (Some a) r). repeat concludes.
        forward IHl; [intros; find_inversion; auto|].
        eauto.
Qed.

Lemma max_cmp_None_correct :
  forall A cmp (wf : A -> Prop),
    (forall a b c, wf a -> wf b -> wf c ->  cmp a b = true -> cmp b c = true -> cmp a c = true) ->
    (forall a b, wf a -> wf b -> cmp a b = true -> cmp b a = false) ->
    (forall a b, wf a -> wf b -> cmp a b = true \/ cmp b a = true \/ a = b) ->
    forall (l : list A) r y,
      (forall x, In x l -> wf x) ->
      max_cmp cmp l None = Some r ->
      In y l ->
      r <> y ->
      cmp y r = true.
Proof.
  intros. find_eapply_lem_hyp max_cmp_correct; eauto; intuition; congruence.
Qed.

Definition possible_preds_lst gst l :=
  forall p,
    (live_node gst (addr_of p) /\ wf_ptr p) <-> In p l.

Lemma better_pred_trans:
  forall gst h a b c,
    better_pred gst h a b ->
    better_pred gst h b c ->
    better_pred gst h a c.
Proof.
  intros.
  invcs H.
  invcs H0. unfold better_pred. intuition.
  eauto using between_trans'.
Qed.

Lemma better_pred_bool_trans:
  forall h a b c,
    better_pred_bool h a b = true ->
    better_pred_bool h b c = true ->
    better_pred_bool h a c = true.
Proof.
  unfold better_pred_bool.
  eauto using ptr_between_bool_trans'.
Qed.

Open Scope id.
Lemma ptr_between_antisym':
  forall h a b : pointer, ptr_between a b h -> ~ ptr_between b a h.
Proof.
  intros. intro.
  invcs H; invcs H0; intuition;
    match goal with
    | H : ?a < ?b, H' : ?b < ?a |- _ =>
      eapply lt_asymm; [apply H | apply H']
    end.
Qed.

Lemma ptr_between_antisym'':
  forall a b c : pointer, ptr_between a b c -> ~ ptr_between a c b.
Proof.
  intros. intro.
  invcs H; invcs H0; intuition;
    match goal with
    | H : ?a < ?b, H' : ?b < ?a |- _ =>
      eapply lt_asymm; [apply H | apply H']
    end.
Qed.

Close Scope id.

Lemma ptr_between_bool_antisym':
  forall h a b : pointer, ptr_between_bool a b h = true -> ptr_between_bool b a h = false.
Proof.
  eauto using ptr_between_bool_true, not_ptr_between, ptr_between_antisym'.
Qed.

Lemma better_pred_bool_antisym':
  forall h a b : pointer, better_pred_bool h a b = true -> better_pred_bool h b a = false.
Proof.
  unfold better_pred_bool.
  eauto using ptr_between_bool_antisym'.
Qed.

(*
Lemma better_pred_bool_total':
  forall h a b : pointer,
    wf_ptr h ->
    wf_ptr a -> wf_ptr b ->
    better_pred_bool h a b = true \/ better_pred_bool h b a = true \/ a = b.
Proof.
  intros.
  destruct (pointer_eq_dec a b); auto.
  assert (id_of a <> id_of b) by admit.
  destruct (better_pred_bool h a b) eqn:?; auto.
  eauto using better_pred_bool_antisymmetric.
Admitted.
*)

(*
Lemma correct_pred_exists' :
  forall gst h l,
    wf_ptr h ->
    possible_preds_lst gst l ->
    l <> [] ->
    exists p,
      wf_ptr p /\
      live_node gst (addr_of p) /\
      pred_correct gst h (Some p).
Proof.
  intros. destruct (max_cmp (better_pred_bool h) l None) eqn:?.
  + exists p. find_copy_apply_lem_hyp max_cmp_in; break_or_hyp; try congruence.
    copy_eapply_prop_hyp possible_preds_lst In. intuition.
    unfold pred_correct. eexists; intuition eauto.
    apply better_pred_bool_true_better_pred; auto.
    eapply max_cmp_None_correct with (wf := wf_ptr); eauto using better_pred_bool_trans, better_pred_bool_antisym', better_pred_bool_total';
      intros; match goal with
              | H : possible_preds_lst _ _ |- _ =>
                apply H; auto
              end.
  + find_apply_lem_hyp max_cmp_empty.
    congruence.
Qed.
*)

Lemma live_ptrs_possible_preds_lst :
  forall gst,
    possible_preds_lst gst (live_ptrs gst).
Proof.
  intros. unfold live_ptrs.
  unfold live_addrs. unfold possible_preds_lst.
  intros. split.
  - intuition.
    in_crush; [symmetry; eauto using wf_ptr_eq|].
    apply filter_In; intuition.
    apply live_node_equiv_live_node_bool. auto.
  - intros.
    in_crush; eauto using make_pointer_wf.
    find_apply_lem_hyp filter_In.
    intuition.
    find_apply_lem_hyp live_node_equiv_live_node_bool. auto.
Qed.

Lemma map_empty :
  forall A B (f : A -> B) l,
    map f l = [] ->
    l = [].
Proof.
  intros. destruct l; simpl in *; congruence.
Qed.

Lemma nonempty_filter_exists :
  forall A f (l : list A),
    filter f l <> [] ->
    exists x,
      In x l /\ f x = true.
Proof.
  induction l; intros; simpl in *; try congruence.
  - break_match.
    + eexists; intuition eauto.
    + intuition. break_exists_exists; intuition.
Qed.

Lemma exists_filter_nonempty :
  forall A f (l : list A),
    (exists x,
      In x l /\
      f x = true) ->
    filter f l <> [].
Proof.
  intros.
  break_exists. break_and.
  cut (In x (filter f l)); intuition; repeat find_rewrite; try solve_by_inversion.
  apply filter_In. intuition.
Qed.

Theorem live_node_preserved_by_recv_step :
  forall gst h src st msg gst' e st' ms nts cts xs ys,
    live_node gst h ->
    Some st = sigma gst h ->
    recv_handler src h st msg = (st', ms, nts, cts) ->
    gst' = apply_handler_result h (st', ms, nts, cts) e (update_msgs gst (xs ++ ys)) ->
    live_node gst' h.
Proof using.
  intuition.
  eapply when_apply_handler_result_preserves_live_node; [| | | |eauto]; eauto.
  - eauto using apply_handler_result_updates_sigma.
  - eapply joined_preserved_by_recv_handler.
    * eauto.
    * break_live_node.
      find_rewrite.
      find_injection.
      auto.
Qed.

Lemma always_exists_live_node :
  forall gst,
    reachable_st gst ->
    exists h,
      live_node gst h.
Proof.
  intros.
  find_apply_lem_hyp zave_invariant_holds.
  inv_prop zave_invariant.
  pose proof succ_list_len_lower_bound.
  inv_prop sufficient_principals; break_and.
  inv_prop principals; break_and.
  destruct x; simpl in *; try omega.
  inv_prop Forall.
  unfold principal in *.
  eexists; intuition eauto.
Qed.

Lemma live_addrs_not_empty :
  forall gst,
    reachable_st gst ->
    live_addrs gst <> [].
Proof.
  intros.
  find_apply_lem_hyp always_exists_live_node.
  apply exists_filter_nonempty.
  break_exists_exists. find_copy_apply_lem_hyp live_node_equiv_live_node_bool.
  unfold live_node in *.  intuition.
Qed.

Lemma live_ptrs_not_empty :
  forall gst,
    reachable_st gst ->
    live_ptrs gst <> [].
Proof.
  intuition.
  eapply live_addrs_not_empty; eauto.
  unfold live_ptrs in *.
  eauto using map_empty.
Qed.

Lemma always_possible_preds_lst :
  forall gst,
    reachable_st gst ->
    exists l,
      l <> [] /\
      possible_preds_lst gst l.
Proof.
  intros. exists (live_ptrs gst).
  intuition; eauto using live_ptrs_possible_preds_lst.
  eapply live_ptrs_not_empty; eauto.
Qed.

(*
Lemma correct_pred_exists :
  forall gst h,
    reachable_st gst ->
    wf_ptr h ->
    exists p,
      wf_ptr p /\
      live_node gst (addr_of p) /\
      pred_correct gst h (Some p).
Proof.
  intros.
  find_apply_lem_hyp always_possible_preds_lst. break_exists; intuition.
  eauto using correct_pred_exists'.
Qed.
(*
This is mostly a fact about the definition of pred_correct and shouldn't require
any invariants besides "there are at least 2 live joined nodes in the network".

DIFFICULTY: 3
USED: In phase two.
*)
*)

Lemma correct_pred_unique :
  forall gst h p p',
    reachable_st gst ->
    wf_ptr p ->
    wf_ptr p' ->
    live_node gst (addr_of p) ->
    live_node gst (addr_of p') ->
    pred_correct gst h (Some p) ->
    pred_correct gst h (Some p') ->
    p = p'.
Proof.
  intros.
  destruct (pointer_eq_dec p p'); auto.
  destruct (pointer_eq_dec p' p); auto.
  unfold pred_correct in *. break_exists_name p1. break_exists_name p2. intuition.
  repeat find_inversion.
  eapply_prop_hyp p1 @eq; auto.
  eapply_prop_hyp p2 @eq; auto.
  find_apply_lem_hyp better_pred_elim. intuition.
  find_apply_lem_hyp better_pred_elim. intuition.
  find_eapply_lem_hyp ptr_between_antisym'. intuition.
Qed.
(*
This is mostly a fact about the definition of pred_correct and shouldn't require
any tricky invariants.

DIFFICULTY: 3
USED: In phase two.
*)

Lemma correct_first_succ_unique :
  forall gst h p p',
    reachable_st gst ->
    wf_ptr p ->
    wf_ptr p' ->
    live_node gst (addr_of p) ->
    live_node gst (addr_of p') ->
    first_succ_correct gst h (Some p) ->
    first_succ_correct gst h (Some p') ->
    p = p'.
Proof.
  intros.
  destruct (pointer_eq_dec p p'); auto.
  destruct (pointer_eq_dec p' p); auto.
  unfold first_succ_correct in *. break_exists_name p1. break_exists_name p2. intuition.
  repeat find_inversion.
  eapply_prop_hyp p1 @eq; auto.
  eapply_prop_hyp p2 @eq; auto.
  unfold better_succ in *. intuition. unfold ptr_between in *.
  find_eapply_lem_hyp ptr_between_antisym''. intuition.
(*
This is mostly a fact about the definition of first_succ_correct and shouldn't
require any tricky invariants.

DIFFICULTY: 3
USED: In phase two.
*)
Qed.

Lemma first_succs_correct_succ_right :
  forall gst h s,
    reachable_st gst ->
    all_first_succs_best gst ->
    first_succs_correct gst ->
    wf_ptr h ->
    wf_ptr s ->
    live_node gst (addr_of h) ->
    live_node gst (addr_of s) ->
    first_succ_correct gst h (Some s) ->
    has_first_succ gst (addr_of h) s.
Proof.
  intros. unfold first_succs_correct in *.
  copy_eapply_lem_prop_hyp live_node_means_state_exists h.
  break_exists.
  copy_eapply_prop_hyp first_succ_correct sigma; eauto.
  copy_eapply_prop_hyp all_first_succs_best h.
  unfold first_succ_is_best_succ in *. break_exists. intuition.
  unfold best_succ in *. break_exists. intuition.
  repeat find_rewrite. repeat find_inversion. repeat find_rewrite. simpl in *.
  find_copy_eapply_lem_hyp WfPtrSuccListInvariant.wf_ptr_succ_list_invariant; eauto.
  find_copy_eapply_lem_hyp (correct_first_succ_unique gst h s); eauto.
  subst. unfold has_first_succ.
  eexists; intuition eauto. repeat find_rewrite. reflexivity.
(*
This is really a proof about first_succ_correct and has_first_succ and shouldn't
require any invariants.

DIFFICULTY: 2
USED: In phase two.
*)
Qed.

(*
Lemma all_first_succs_correct_finds_pred :
  forall gst h,
    reachable_st gst ->
    all_first_succs_best gst ->
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
  find_copy_eapply_lem_hyp correct_pred_exists; [|eauto].
  break_exists_exists.
  intuition eauto.
  eapply first_succs_correct_succ_right; auto.
  now apply best_pred_is_best_first_succ.
Qed.
*)

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

Lemma phase_one_all_first_succs_best :
  forall ex,
    always (now phase_one) ex ->
    all_first_succs_best (occ_gst (hd ex)).
Proof.
  intros. unfold phase_one in *.
  destruct ex. simpl in *.
  find_eapply_lem_hyp always_now. simpl in *. auto.
Qed.

(*
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
(*
  intros.
  find_copy_apply_lem_hyp all_first_succs_correct_finds_pred; auto using phase_one_all_first_succs_best.
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
      * inv_prop better_pred. expand_def.
        cut (Some x <> Some p); [congruence|].
        eapply wrong_pred_not_correct_pred; eauto.
      * find_apply_lem_hyp pred_never_self; auto.
      * unfold pred_correct in *.
        expand_def.
        find_injection.
        unfold better_pred in *; expand_def.
        apply H17; try by intuition eauto; subst.
        -- break_and.
           unfold ptr_between in *.
           intro; subst.
           find_eapply_lem_hyp wrong_pred_not_correct_pred; eauto.
           assert (addr_of h <> addr_of x1)
             by (eapply pred_never_self; eauto).
           assert (id_of h <> id_of x1) by admit.
           admit.
        -- admit.
  - inv_prop wrong_pred. expand_def.
    find_copy_eapply_lem_hyp pred_same_until_improvement; eauto.
    find_apply_lem_hyp weak_until_Cons. break_or_hyp.
    + apply E0; eauto.
    + apply E_next, IHeventually; invar_eauto; eauto;
        (* these are all manageable *)
        admit.
*)
Admitted.
*)

(*
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
This should follow from something like this:

    forall gst,
      reachable_st gst ->
      ~ first_succs_correct gst ->
      exists a b j,
        merge_point gst a b j.

DIFFICULTY: Ryan
USED: Crucially in phase two.
*)
Admitted.
*)

(*
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
  (*
  intros; intro.
  assert (all_first_succs_best (occ_gst (hd ex)))
    by (inv_prop always; destruct ex; auto).
  find_apply_lem_hyp error_means_merge_point_or_wrong_pred; auto.
  expand_def.
  - find_eapply_lem_hyp error_decreases_when_succs_right; eauto.
    eexists; eauto using live_node_in_active, pred_improvement_suffices.
  - inv_prop merge_point; break_and.
    find_apply_lem_hyp error_decreases_at_merge_point; eauto.
    unfold pred_or_succ_improves_abj in *.
    repeat (find_apply_lem_hyp eventually_or_tl_or; auto; try break_or_hyp);
      eexists; eauto using live_node_in_active.
*)
Admitted.
*)

(*
Lemma phase_two_nonzero_error_continuous_drop :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ now circular_wait) ex ->
    always (now phase_one) ex ->
    continuously (nonzero_error_causes_measure_drop pred_and_first_succ_error) ex.
Proof.
  (*
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
*)
Admitted.
*)

(*
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
Admitted.
*)

Lemma phase_two_without_phase_one :
  forall ex : infseq occurrence,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ now circular_wait) ex ->
    continuously (now phase_two) ex.
Proof.
  (*
  intros.
  find_copy_eapply_lem_hyp phase_one_continuously; eauto.
  apply eventually_idempotent.
  lift_eventually phase_two_continuously.
  - intros.
    unfold and_tl in *; break_and.
    repeat (split; invar_eauto).
  - firstorder.
*)
Admitted.
