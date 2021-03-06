Require Import Omega.
Require Import List.

Require Import StructTact.StructTactics.
Require Import StructTact.FilterMap.
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.
Require Import Chord.InfSeqTactics.
Require Import Chord.Chord.
Require Import Chord.LabeledLemmas.

(** This shouldn't live here but I'm not sure where it should live *)
Lemma nat_strong_ind :
  forall (P : nat -> Prop),
    (forall n, (forall m, m < n -> P m) -> P n) ->
    forall n, P n.
Proof.
  intros P Himp.
  intros.
  (* generalize induction hypothesis *)
  cut (forall m, m < n -> P m); [now auto|].
  induction n.
  - easy.
  - firstorder.
Qed.


Section Measure.

  Variable measure : global_state -> nat.
  Notation "| gst |" := (measure gst) (at level 50).

  Definition measure_bounded (n : nat) : infseq occurrence -> Prop :=
    always (now (fun o => |occ_gst o| <= n)).

  Definition measure_nonincreasing (o o' : occurrence) : Prop :=
    |occ_gst o'| <= |occ_gst o|.

  Definition measure_decreasing (o o' : occurrence) : Prop :=
    |occ_gst o'| < |occ_gst o|.

  Definition measure_zero (o : occurrence) : Prop :=
    |occ_gst o| = 0.

  Definition zero_or_eventually_decreasing : infseq occurrence -> Prop :=
    now measure_zero \/_
    eventually (consecutive measure_decreasing).

  Lemma measure_nonincreasing_stays_zero :
    forall o o',
      measure_nonincreasing o o' ->
      measure_zero o ->
      measure_zero o'.
  Proof.
    unfold measure_nonincreasing, measure_zero.
    intros.
    omega.
  Qed.

  Lemma measure_zero_stays_zero :
    forall ex,
      always (consecutive measure_nonincreasing) ex ->
      now measure_zero ex ->
      always (now measure_zero) ex.
  Proof.
    cofix c.
    intros.
    constructor; auto.
    do 2 destruct ex; simpl in *.
    apply c.
    - eauto using always_invar.
    - inv_prop always.
      unfold consecutive in *.
      simpl.
      eauto using measure_nonincreasing_stays_zero.
  Qed.

  Lemma measure_bounded_hd_elim :
    forall m n ex,
      measure_bounded n ex ->
      |occ_gst (hd ex)| = m ->
      m <= n.
  Proof.
    intros; destruct ex.
    now inv_prop measure_bounded.
  Qed.

  Lemma measure_bounded_monotonic :
    forall m n ex,
      m <= n ->
      measure_bounded m ex ->
      measure_bounded n ex.
  Proof.
    cofix c.
    intros.
    constructor; destruct ex as [o [o' ex]]; simpl in *.
    - inv_prop measure_bounded; simpl in *.
      omega.
    - eapply c; eauto.
      eapply always_invar; eauto.
  Qed.

  (** If the measure never increases and you can bound the measure of the first
      state, you can bound the entire sequence. *)
  Lemma nonincreasing_preserves_bound :
    forall ex,
      always (consecutive measure_nonincreasing) ex ->
      forall n,
        |occ_gst (hd ex)| <= n ->
        measure_bounded n ex.
  Proof.
    cofix c.
    constructor; destruct ex as [o [o' ex]]; simpl in *; [omega|].
    eapply c.
    - eauto using always_invar.
    - inv_prop measure_nonincreasing.
      unfold measure_nonincreasing in *.
      simpl in *.
      omega.
  Qed.

  (** If the measure never increases, you can bound the entire sequence by the
      measure of the first state. *)
  Lemma nonincreasing_global :
    forall ex,
      always (consecutive measure_nonincreasing) ex ->
      forall n,
        |occ_gst (hd ex)| = n ->
        measure_bounded n ex.
  Proof.
    auto using Nat.eq_le_incl, nonincreasing_preserves_bound.
  Qed.

  (** If the measure never increases and drops infinitely often, then it will
      eventually be less than its initial value (provided the initial value is
      nonzero). *)
  Lemma measure_drops :
    forall ex,
      always (consecutive measure_nonincreasing) ex ->
      zero_or_eventually_decreasing ex ->
      forall n,
        |occ_gst (hd ex)| = S n ->
        eventually (now (fun o => |occ_gst o| < S n)) ex.
  Proof.
    intros.
    unfold zero_or_eventually_decreasing in *.
    find_copy_apply_lem_hyp nonincreasing_global; auto.
    invc H0.
    - destruct ex.
      simpl in *.
      congruence.
    - match goal with
      | H : eventually (consecutive measure_decreasing) _ |- _ =>
        induction H
      end.
      + destruct s as [o [o' s]].
        apply E_next; apply E0.
        unfold measure_decreasing in *.
        simpl in *; omega.
      + simpl.
        destruct s as [o s].
        destruct (lt_dec (|occ_gst o|) (|occ_gst x|)).
        * apply E_next; apply E0.
          simpl in *; omega.
        * assert (|occ_gst o| = |occ_gst x|).
          {
            find_apply_lem_hyp not_lt.
            apply Nat.le_antisymm; auto.
            inv_prop (always (consecutive measure_nonincreasing)).
            unfold measure_nonincreasing in *.
            auto.
          }
          apply E_next.
          simpl in *.
          repeat find_rewrite.
          eapply IHeventually; eauto;
            try eapply always_invar; eauto.
  Qed.

  Lemma less_than_Sn_bounded_n :
    forall n ex,
      always (consecutive measure_nonincreasing) ex ->
      now (fun occ => |occ_gst occ| < S n) ex ->
      measure_bounded n ex.
  Proof.
    intros.
    remember (|occ_gst (hd ex)|) as m.
    eapply measure_bounded_monotonic;
      [|eauto using nonincreasing_global].
    destruct ex; simpl in *; omega.
  Qed.

  Lemma measure_bound_drops :
    forall n ex,
      measure_bounded (S n) ex ->
      always (consecutive measure_nonincreasing) ex ->
      zero_or_eventually_decreasing ex ->
      eventually (measure_bounded n) ex.
  Proof.
    intros.
    destruct ex as [o ex].
    destruct (|occ_gst o|) eqn:?H.
    - apply E0.
      eapply measure_bounded_monotonic with (m:=0); [omega|].
      eapply nonincreasing_global; eauto.
    - find_copy_eapply_lem_hyp nonincreasing_global; eauto.
      eapply eventually_monotonic_simple.
      {
        intros; eapply (measure_bounded_monotonic n0 n); eauto.
        apply le_S_n.
        eapply measure_bounded_hd_elim; eauto.
      }
      eapply eventually_monotonic; try eapply less_than_Sn_bounded_n; eauto using always_invar.
      eapply measure_drops; eauto.
  Qed.

  Lemma measure_bounded_zero :
    forall ex,
      measure_bounded 0 ex ->
      always (now measure_zero) ex.
  Proof.
    cofix c.
    intros; constructor.
    - inv_prop measure_bounded.
      destruct ex; simpl in *.
      unfold measure_zero; omega.
    - destruct ex.
      simpl in *.
      apply c.
      eapply always_invar; eauto.
  Qed.

  (** TODO(ryan) move to infseq *)
  Lemma eventually_idempotent :
    forall T (P : infseq T -> Prop) ex,
      eventually (eventually P) ex ->
      eventually P ex.
  Proof.
    intros T P ex H_ee.
    induction H_ee.
    - assumption.
    - now apply E_next.
  Qed.

  (* Lemma decreasing_inf_often_or_zero_invar_when_nonincreasing : *)
    (* forall o ex, *)
      (* always (consecutive measure_nonincreasing) (Cons o ex) -> *)
      (* zero_or_eventually_decreasing (Cons o ex) -> *)
      (* zero_or_eventually_decreasing ex. *)
  (* Proof. *)
    (* unfold zero_or_eventually_decreasing. *)
    (* intros. *)
    (* inv_prop or_tl. *)
    (* - left. *)
      (* find_apply_lem_hyp measure_zero_stays_zero; auto. *)
      (* find_apply_lem_hyp always_invar. *)
      (* now inv_prop always. *)
    (* - right; eapply inf_often_invar; eauto. *)
  (* Qed. *)

  Lemma measure_decreasing_to_zero' :
    forall n ex,
      always (consecutive measure_nonincreasing) ex ->
      always zero_or_eventually_decreasing ex ->
      measure_bounded n ex ->
      eventually (now measure_zero) ex.
  Proof.
    intros n.
    induction n using nat_strong_ind.
    destruct n; subst_max.
    - intros.
      apply E0.
      find_apply_lem_hyp measure_bounded_zero.
      inv_prop always.
      assumption.
    - intros.
      destruct ex.
      find_copy_apply_lem_hyp measure_bound_drops;
        auto;
        try now apply always_now.
      pose proof (H n).
      forwards.
      omega.
      specialize (H4 H5); clear H5.
      eapply eventually_idempotent.
      lift_eventually H4.
      + unfold and_tl; intros; break_and_goal; break_and;
          eauto using always_invar.
      + split; auto.
  Qed.

  Lemma measure_decreasing_to_zero :
    forall ex,
      always zero_or_eventually_decreasing ex ->
      always (consecutive measure_nonincreasing) ex ->
      continuously (now measure_zero) ex.
  Proof.
    intros.
    remember (|occ_gst (hd ex)|) as n.
    find_copy_eapply_lem_hyp nonincreasing_global; auto.
    find_copy_eapply_lem_hyp measure_decreasing_to_zero'; eauto.
    lift_eventually measure_zero_stays_zero.
    eauto using always_invar.
  Qed.

  (* TODO(ryan) move to infseq *)
  Lemma eventually_and_tl_comm :
    forall T (P Q : infseq T -> Prop) s,
      eventually (P /\_ Q) s ->
      eventually (Q /\_ P) s.
  Proof.
    intros until 0.
    apply eventually_monotonic_simple.
    intros.
    now rewrite and_tl_comm.
  Qed.

  (* TODO(ryan) move to infseq *)
  Lemma always_and_tl_comm :
    forall T (P Q : infseq T -> Prop) s,
      always (P /\_ Q) s ->
      always (Q /\_ P) s.
  Proof.
    intros until 0.
    apply always_monotonic.
    intros.
    now rewrite and_tl_comm.
  Qed.

  Definition measure_x x occ := |occ_gst occ| = x.

  Set Bullet Behavior "Strict Subproofs".

  Require Import Classical.
  Lemma always_or_eventually :
    forall T P (s : infseq T),
      always P s \/ eventually (not_tl P) s.
  Proof.
    intros.
    destruct (classic (always P s)); eauto using not_always_eventually_not.
  Qed.

  Lemma eventually_exists :
    forall T A (P : A -> T -> Prop) (s : infseq T),
      eventually (now (fun o => exists x, P x o)) s ->
      exists x,
        eventually (now (fun o => P x o)) s.
  Proof.
    intros.
    induction H.
    - destruct s. simpl in *.
      break_exists_exists.
      apply E0. simpl. auto.
    - break_exists_exists.
      apply E_next. auto.
  Qed.

  Lemma eventually_exists' :
    forall T A (P : A -> infseq T -> Prop) (s : infseq T),
      eventually (fun s => exists x, P x s) s ->
      exists x,
        eventually (P x) s.
  Proof.
    intros.
    induction H.
    - break_exists_exists.
      eauto using E0.
    - break_exists_exists. eauto using E_next.
  Qed.

  Lemma eventually_pure_and :
    forall T (Q : Prop) (P : T -> Prop) (s : infseq T),
      eventually (now (fun o => Q /\ P o)) s ->
      Q /\ eventually (now P) s.
  Proof.
    induction 1.
    - destruct s; simpl in *; intuition.
      eauto using E0.
    - intuition. eauto using E_next.
  Qed.
  
  Lemma measure_nonincreasing_eventually_stable' :
    forall n ex,
      (now (measure_x n) ex) ->
      always (consecutive measure_nonincreasing) ex ->
      exists x,
        continuously (now (measure_x x)) ex.
  Proof.
    induction n using nat_strong_ind.
    intros.
    destruct (always_or_eventually _ (now (measure_x n)) ex).
    - eauto using always_continuously.
    - find_copy_eapply_lem_hyp nonincreasing_preserves_bound; eauto.
      assert (|occ_gst (hd ex)| = n).
      {
        unfold now in *. break_match; repeat find_rewrite; simpl; auto.
      }
      repeat find_rewrite.
      assert (exists m, m < n /\ eventually (now (measure_x m)) ex).
      {
        unfold measure_bounded in *.
        find_eapply_lem_hyp cumul_eventually_always; eauto.
        assert (eventually (now (fun o => exists m, m < n /\ measure_x m o)) ex).
        {
          eapply eventually_monotonic_simple; [|eauto].
          intros.
          unfold now; break_match. subst.
          exists (|occ_gst o|). unfold measure_x. intuition.
          unfold and_tl,not_tl in *. intuition. simpl in *.
          unfold measure_x in *.
          omega.
        }
        find_apply_lem_hyp eventually_exists.
        break_exists_exists.
        eauto using eventually_pure_and.
      }
      break_exists. intuition.
      match goal with
      | H : eventually (now _) _ |- _ =>
        eapply eventually_monotonic with
            (J := (always (consecutive measure_nonincreasing)))
            (Q := (fun ex => exists x, continuously (now (measure_x x)) ex))
          in H
      end; eauto using always_invar.
      find_apply_lem_hyp eventually_exists'.
      break_exists_exists. 
      unfold continuously in *.
      eauto using eventually_idempotent.
  Qed.
      
  Lemma measure_nonincreasing_eventually_stable :
    forall ex,
      always (consecutive measure_nonincreasing) ex ->
      exists x,
        continuously (now (measure_x x)) ex.
  Proof.
    intros.
    assert (now (measure_x (|occ_gst (hd ex)|)) ex).
    { unfold measure_x. destruct ex; simpl; auto. }
    eauto using measure_nonincreasing_eventually_stable'.
  Qed.
      
End Measure.

Section LocalMeasure.
  Variable local_measure : addr -> global_state -> nat.
  Notation "| h 'in' gst |" := (local_measure h gst) (at level 50).

  Definition sum (l : list nat) :=
    fold_left Nat.add l 0.

  Definition max (l : list nat) :=
    fold_left Nat.max l 0.

  Lemma fold_left_acc_comm :
    forall a l,
      fold_left Nat.add l a = a + fold_left Nat.add l 0.
  Proof.
    intros.
    generalize a.
    induction l; [auto|].
    simpl.
    intros.
    rewrite IHl; symmetry; rewrite IHl.
    auto with arith.
  Qed.

  Lemma fold_left_max_comm :
    forall a l,
      fold_left Nat.max l a = Nat.max a (fold_left Nat.max l 0).
  Proof.
    intros.
    generalize a.
    induction l; intros.
    - simpl; zify; omega.
    - simpl.
      rewrite IHl; symmetry; rewrite IHl.
      zify; omega.
  Qed.

  Lemma sum_cons :
    forall n l,
      sum (n :: l) = n + sum l.
  Proof.
    unfold sum.
    intros; simpl.
    now rewrite fold_left_acc_comm.
  Qed.

  Lemma max_cons_le :
    forall n l,
      n <= max (n :: l).
  Proof.
    intros. generalize n; clear n.
    induction l; intros; simpl in *; auto.
    unfold max in *. simpl in *.
    eapply le_trans; [eapply Nat.le_max_l|]; eauto.
  Qed.

  Lemma max_cons_cases :
    forall n l,
      max (n :: l) = n /\
      max l <= n \/
      max (n :: l) = max l /\
      n <= max l.
  Proof.
    intros. unfold max.
    repeat (rewrite fold_symmetric; eauto using Max.max_assoc, Max.max_comm).
    simpl.
    match goal with
    | |- context [Nat.max ?n ?m] =>
      destruct (Nat.max_spec n m)
    end; intuition.
  Qed.

  Lemma sum_app :
    forall l l',
      sum (l ++ l') = sum l + sum l'.
  Proof.
    unfold sum.
    intros; simpl.
    now rewrite fold_left_app, fold_left_acc_comm.
  Qed.

  Lemma sum_disjoint :
    forall xs x ys,
      sum (xs ++ x :: ys) = sum xs + x + sum ys.
  Proof.
    intros.
    now rewrite sum_app, sum_cons, Nat.add_assoc.
  Qed.

  Lemma sum_map_mono :
    forall X (f g : X -> nat) l,
      (forall x, In x l -> f x <= g x) ->
      sum (map f l) <= sum (map g l).
  Proof.
    intros.
    induction l; [auto|].
    rewrite !map_cons, !sum_cons.
    apply Nat.add_le_mono; auto with datatypes.
  Qed.

  Lemma max_map_mono :
    forall X (f g : X -> nat) l,
      (forall x, In x l -> f x <= g x) ->
      max (map f l) <= max (map g l).
  Proof.
    intros.
    induction l; [auto|].
    forwards. eauto with datatypes. concludes.
    pose proof (max_cons_le (g a) (map g l)).
    assert (f a <= g a) by eauto with datatypes.
    pose proof (max_cons_cases (f a) (map f l)).
    pose proof (max_cons_cases (g a) (map g l)).

    rewrite !map_cons.
    intuition omega.
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
    induction l0; simpl;
      firstorder using Nat.nlt_0_r, lt_n_Sm_le, lt_le_trans.
  Qed.

  Lemma fold_max_const_is_const :
    forall l c,
      (forall x, In x l -> x = c) ->
      fold_left Nat.max l c = c.
  Proof.
    unfold max.
    induction l; intros.
    - cbn in *; omega.
    - replace a with c; [|symmetry; auto with datatypes].
      simpl.
      rewrite Max.max_idempotent.
      eauto with datatypes.
  Qed.

  Lemma max_nonempty_const_is_const :
    forall l c,
      (forall x, In x l -> x = c) ->
      length l > 0 ->
      max l = c.
  Proof.
    unfold max.
    intros.
    destruct l as [|a l].
    - cbn in *; omega.
    - replace a with c; [|symmetry; auto with datatypes].
      cbn; apply fold_max_const_is_const; auto with datatypes.
  Qed.

  Lemma max_map_bound :
    forall X (f : X -> nat) b l,
      (forall x, In x l -> f x <= b) ->
      max (map f l) <= b.
  Proof.
    intros.
    destruct l as [| h l].
    - auto with arith.
    - replace b with (max (map (fun _ => b) (h :: l)));
        auto using max_map_mono.
      eapply max_nonempty_const_is_const; simpl; auto with arith.
      intros.
      break_or_hyp; [congruence|].
      find_apply_lem_hyp in_map_iff.
      break_exists; break_and; congruence.
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
    induction l using list_strong_ind; destruct l.
    - easy.
    - intros.
      find_apply_lem_hyp in_inv; break_or_hyp.
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

  Lemma max_of_nats_bounds_list :
    forall l n,
      max l = n ->
      forall x,
        In x l ->
        x <= n.
  Proof.
    unfold max.
    induction l using list_strong_ind; destruct l as [|a l].
    - easy.
    - intros.
      find_apply_lem_hyp in_inv; break_or_hyp.
      + simpl.
        rewrite fold_left_max_comm.
        zify; omega.
      + assert (x <= fold_left Nat.max l 0)
          by firstorder.
        simpl. rewrite fold_left_max_comm.
        zify; omega.
  Qed.

  Lemma max_of_nats_zero_means_zero :
    forall l,
      max l = 0 ->
      forall x,
        In x l ->
        x = 0.
  Proof.
    intros.
    symmetry.
    apply le_n_0_eq.
    eapply max_of_nats_bounds_list; eauto.
  Qed.

  Lemma sum_of_zeros_is_zero :
    forall l,
      Forall (fun n => n = 0) l ->
      sum l = 0.
  Proof.
    intros.
    induction l; auto.
    inv_prop Forall; auto.
  Qed.

  Lemma sum_nonzero_implies_addend_nonzero :
    forall l,
      sum l > 0 ->
      exists x,
        In x l /\
        x > 0.
  Proof.
    induction l as [|hd rest].
    - cbn.
      intros; omega.
    - intros; rewrite sum_cons in *.
      destruct hd eqn:?H.
      + firstorder.
      + exists hd; firstorder.
  Qed.

  Definition global_measure (gst : global_state) : nat :=
    sum (map (fun h => |h in gst|) (active_nodes gst)).

  Notation "| gst |" := (global_measure gst) (at level 50).

  Definition max_measure (gst : global_state) : nat :=
    max (map (fun h => |h in gst|) (active_nodes gst)).

  Lemma max_measure_bounds_measures :
    forall gst e,
      max_measure gst = e ->
      forall h,
        In h (active_nodes gst) ->
        |h in gst| <= e.
  Proof.
    intros.
    unfold max_measure in *.
    eapply max_of_nats_bounds_list; eauto.
    rewrite in_map_iff.
    eauto.
  Qed.

  Definition max_measure_nonzero_eventually_all_locals_below (ex : infseq occurrence) : Prop :=
    forall err,
      max_measure (occ_gst (hd ex)) = S err ->
      forall h,
        In h (active_nodes (occ_gst (hd ex))) ->
        eventually (now (fun o => |h in occ_gst o| <= err)) ex.

  Definition some_local_measure_drops (ex : infseq occurrence) :=
    exists h,
      In h (active_nodes (occ_gst (hd ex))) /\
      eventually (consecutive (measure_decreasing (local_measure h))) ex.

  Definition local_measure_nonincreasing (h : addr) : infseq occurrence -> Prop :=
    consecutive (measure_nonincreasing (local_measure h)).

  Definition local_measures_nonincreasing (ex : infseq occurrence) : Prop :=
    forall h,
      In h (active_nodes (occ_gst (hd ex))) ->
      local_measure_nonincreasing h ex.

  Lemma map_Forall_comm :
    forall (X Y : Type) (f : X -> Y) P l,
      Forall P (map f l) <-> Forall (fun x => P (f x)) l.
  Proof.
    intros; split; intro;
    induction l; constructor;
      inv_prop Forall;
      eauto.
  Qed.

  Lemma local_all_zero_global_zero :
    forall gst,
      Forall (fun h => |h in gst| = 0) (active_nodes gst) <-> |gst| = 0.
  Proof.
    intros; split; intro.
    - apply sum_of_zeros_is_zero.
      now apply map_Forall_comm.
    - apply Forall_forall.
      intros.
      eapply sum_of_nats_zero_means_all_zero; eauto.
      change (|x in gst|) with ((fun y => |y in gst|) x).
      now apply in_map.
  Qed.

  Lemma measure_mono :
    forall gst gst',
      nodes gst' = nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      (forall h, In h (active_nodes gst) -> |h in gst| <= |h in gst'|) ->
      |gst| <= |gst'|.
  Proof.
    intros.
    unfold global_measure, active_nodes in *.
    repeat find_rewrite.
    now apply sum_map_mono.
  Qed.

  Lemma local_nonincreasing_causes_global_nonincreasing :
    forall ex,
      lb_execution ex ->
      local_measures_nonincreasing ex ->
      consecutive (measure_nonincreasing global_measure) ex.
  Proof.
    unfold local_measures_nonincreasing, local_measure_nonincreasing, measure_nonincreasing.
    intros.
    destruct ex as [o [o' ex]]; simpl.
    inv_prop lb_execution.
    find_copy_apply_lem_hyp labeled_step_dynamic_preserves_active_nodes.
    eapply measure_mono; repeat find_rewrite;
      eauto using labeled_step_dynamic_preserves_nodes, labeled_step_dynamic_preserves_failed_nodes.
    intros; unfold active_nodes in *.
    repeat find_reverse_rewrite; simpl in *; eauto.
  Qed.

  Lemma max_measure_mono :
    forall gst gst',
      nodes gst' = nodes gst ->
      failed_nodes gst' = failed_nodes gst ->
      (forall h, In h (active_nodes gst) -> |h in gst| <= |h in gst'|) ->
      max_measure gst <= max_measure gst'.
  Proof.
    intros.
    unfold max_measure, active_nodes in *.
    repeat find_rewrite.
    now apply max_map_mono.
  Qed.

  Lemma local_nonincreasing_causes_max_nonincreasing :
    forall ex,
      lb_execution ex ->
      local_measures_nonincreasing ex ->
      consecutive (measure_nonincreasing max_measure) ex.
  Proof.
    unfold local_measures_nonincreasing, local_measure_nonincreasing, measure_nonincreasing.
    intros.
    destruct ex as [o [o' ex]]; simpl.
    inv_prop lb_execution.
    find_copy_apply_lem_hyp labeled_step_dynamic_preserves_active_nodes.
    eapply max_measure_mono; repeat find_rewrite;
      eauto using labeled_step_dynamic_preserves_nodes, labeled_step_dynamic_preserves_failed_nodes.
    intros; unfold active_nodes in *.
    repeat find_reverse_rewrite; simpl in *; eauto.
  Qed.

  Lemma local_always_nonincreasing_causes_max_always_nonincreasing :
    forall ex,
      lb_execution ex ->
      always local_measures_nonincreasing ex ->
      always (consecutive (measure_nonincreasing max_measure)) ex.
  Proof.
    cofix c; intros; constructor; destruct ex.
    - apply local_nonincreasing_causes_max_nonincreasing; eauto.
      apply always_now'; eauto.
    - apply c; eauto using always_invar, lb_execution_invar.
  Qed.

  Lemma local_dropping_makes_global_drop :
    forall h o o',
      active_nodes (occ_gst o) = active_nodes (occ_gst o') ->
      (forall h', In h' (active_nodes (occ_gst o)) ->
             measure_nonincreasing (local_measure h') o o') ->
      In h (active_nodes (occ_gst o)) ->
      measure_decreasing (local_measure h) o o' ->
      measure_decreasing global_measure o o'.
  Proof.
    unfold measure_decreasing, measure_nonincreasing, global_measure.
    intros.
    find_apply_lem_hyp in_split; break_exists.
    repeat find_rewrite.
    rewrite !map_app, !map_cons, !sum_disjoint.
    apply Nat.add_lt_le_mono;
      try apply Nat.add_le_lt_mono;
      assumption || apply sum_map_mono; auto with datatypes.
  Qed.

  Lemma local_dropping_makes_global_drop_ex :
    forall h ex,
      lb_execution ex ->
      always local_measures_nonincreasing ex ->
      In h (active_nodes (occ_gst (hd ex))) ->
      consecutive (measure_decreasing (local_measure h)) ex ->
      consecutive (measure_decreasing global_measure) ex.
  Proof.
    intros.
    destruct ex as [o [o' ex]].
    inv_prop lb_execution.
    inv_prop always.
    eapply local_dropping_makes_global_drop;
      eauto using labeled_step_dynamic_preserves_active_nodes.
  Qed.

  Definition nonzero_error_causes_measure_drop (ex : infseq occurrence) :=
     |occ_gst (hd ex)| > 0 ->
     some_local_measure_drops ex.

  Lemma local_measure_causes_eventual_drop :
    forall ex,
      lb_execution ex ->
      always local_measures_nonincreasing ex ->
      nonzero_error_causes_measure_drop ex ->
      zero_or_eventually_decreasing global_measure ex.
  Proof.
    intros.
    destruct (|occ_gst (hd ex)|) as [| err] eqn:?H;
      [left|right].
    - destruct ex; assumption.
    - pose proof (gt_Sn_O err); repeat find_reverse_rewrite.
      assert (some_local_measure_drops ex) by auto.
      unfold some_local_measure_drops in *; break_exists_name h; break_and.
      lift_eventually (local_dropping_makes_global_drop_ex h);
        firstorder using lb_execution_invar, always_invar.
      inv_prop lb_execution; simpl.
      find_copy_apply_lem_hyp labeled_step_dynamic_preserves_active_nodes.
      now repeat find_reverse_rewrite.
  Qed.

  Lemma local_measure_always_causes_eventual_drop :
    forall ex,
      lb_execution ex ->
      always local_measures_nonincreasing ex ->
      always nonzero_error_causes_measure_drop ex ->
      always (zero_or_eventually_decreasing global_measure) ex.
  Proof.
    intros.
    lift_always local_measure_causes_eventual_drop.
    repeat apply always_and_tl;
      eauto using always_always, always_inv, lb_execution_invar.
  Qed.

  Lemma local_measure_causes_measure_zero :
    forall ex,
      lb_execution ex ->
      always local_measures_nonincreasing ex ->
      always nonzero_error_causes_measure_drop ex ->
      continuously (now (measure_zero global_measure)) ex.
  Proof.
    intros.
    eapply measure_decreasing_to_zero.
    - now apply local_measure_always_causes_eventual_drop.
    - lift_always local_nonincreasing_causes_global_nonincreasing.
      apply always_and_tl; eauto using always_inv, lb_execution_invar.
  Qed.

  (* TODO(ryan) move to infseq *)
  Lemma continuously_forall_list_comm :
    forall (A B : Type) (P : A -> infseq B -> Prop) l ex,
      (forall x, In x l -> (continuously (P x) ex)) ->
      continuously (fun ex' => forall x, In x l -> P x ex') ex.
  Proof.
    induction l as [| a l].
    - intros.
      apply E0.
      eapply always_monotonic; try eapply always_true; intros.
      exfalso; auto.
    - intros.
      pose proof (IHl ex).
      forwards. auto with datatypes. concludes.
      assert (continuously (P a) ex)
        by auto with datatypes.
      cut (continuously ((fun ex' => forall x, In x l -> P x ex') /\_ P a) ex).
      {
        apply continuously_monotonic.
        intros.
        unfold and_tl in *; break_and.
        find_apply_lem_hyp in_inv; break_or_hyp; auto.
      }
      apply continuously_and_tl; eauto.
  Qed.

  Lemma always_forall_list_comm :
    forall (A B : Type) (P : A -> infseq B -> Prop) ex l,
      (forall x, In x l -> (always (P x) ex)) ->
      always (fun ex' => forall x, In x l -> P x ex') ex.
  Proof.
    intros.
    generalize dependent l.
    induction l as [| a l].
    - intros; eapply always_monotonic; try eapply always_true; intros.
      exfalso; auto.
    - intros.
      forward IHl. eauto with datatypes. concludes.
      assert (always (P a) ex)
        by auto with datatypes.
      cut (always ((fun ex' => forall x, In x l -> P x ex') /\_ P a) ex).
      {
        apply always_monotonic.
        intros.
        unfold and_tl in *; break_and.
        find_apply_lem_hyp in_inv; break_or_hyp; auto.
      }
      apply always_and_tl; eauto.
  Qed.

  Lemma measure_eventually_bounded_continuously_bounded :
    forall ex h n,
      always (local_measure_nonincreasing h) ex ->
      eventually (fun ex' => |h in occ_gst (hd ex')| <= n) ex ->
      continuously (fun ex' => |h in occ_gst (hd ex') | <= n) ex.
  Proof.
    intros.
    induction H0.
    - apply E0.
      apply nonincreasing_preserves_bound in H0; eauto.
      unfold measure_bounded in *.
      eapply always_monotonic; eauto.
      intros [o s']; auto.
    - apply E_next.
      unfold continuously in *.
      find_apply_lem_hyp always_Cons; tauto.
  Qed.

  Lemma all_measures_nonincreasing_always_each_nonincreasing :
    forall (ex : infseq occurrence) (h : addr),
      lb_execution ex ->
      In h (active_nodes (occ_gst (hd ex))) ->
      always local_measures_nonincreasing ex ->
      always (consecutive (measure_nonincreasing (local_measure h))) ex.
  Proof.
    cofix c; intros; constructor; destruct ex.
    - find_apply_lem_hyp always_Cons; break_and.
      unfold local_measures_nonincreasing, local_measure_nonincreasing in *.
      auto.
    - simpl. apply c; eauto using lb_execution_invar, always_invar.
      inv_prop lb_execution.
      erewrite <- labeled_step_dynamic_preserves_active_nodes; eauto.
  Qed.

  Lemma local_drops_below_bound :
    forall ex h n,
      lb_execution ex ->
      In h (active_nodes (occ_gst (hd ex))) ->
      always local_measures_nonincreasing ex ->
      |h in (occ_gst (hd ex))| <= S n ->
      eventually (consecutive (measure_decreasing (local_measure h))) ex ->
      continuously (fun ex' => |h in (occ_gst (hd ex'))| <= n) ex.
  Proof.
    intros.
    assert (always (consecutive (measure_nonincreasing (local_measure h))) ex)
      by eauto using all_measures_nonincreasing_always_each_nonincreasing.
    eapply measure_eventually_bounded_continuously_bounded; auto.
    destruct (|h in (occ_gst (hd ex))|) as [|k] eqn:?.
    - fold (measure_zero (local_measure h) (hd ex)) in *.
      destruct ex.
      change (measure_zero (local_measure h) (hd (Cons o ex)))
        with (now (measure_zero (local_measure h)) (Cons o ex)) in *.
      apply E0.
      invcs_prop measure_zero.
      omega.
    - cut (eventually (fun ex' => |h in occ_gst (hd ex')| < S k) ex).
      {
        apply eventually_monotonic_simple.
        intros; omega.
      }
      cut (eventually (measure_bounded (local_measure h) k) ex).
      {
        apply eventually_monotonic_simple.
        unfold measure_bounded.
        intros. destruct s.
        find_apply_lem_hyp always_Cons; break_and.
        cbn in *.
        omega.
      }
      eapply measure_bound_drops; firstorder.
      eapply less_than_Sn_bounded_n; auto.
      destruct ex; simpl in *; omega.
  Qed.

  Lemma always_bound_on_local_measures_bounds_max :
    forall n ex,
      lb_execution ex ->
      always
         (fun ex' =>
            forall h,
              In h (active_nodes (occ_gst (hd ex))) ->
              |h in occ_gst (hd ex')| <= n)
         ex ->
      always (fun ex' => max_measure (occ_gst (hd ex')) <= n) ex.
  Proof.
    intros.
    remember (active_nodes (occ_gst (hd ex))) as l.
    find_copy_apply_lem_hyp (active_nodes_always_identical l ex); eauto.
    generalize dependent ex.
    cofix c. intros.
    constructor; destruct ex.
    - unfold max_measure.
      repeat find_apply_lem_hyp always_Cons; break_and.
      eapply max_map_bound.
      now repeat find_reverse_rewrite.
    - repeat find_apply_lem_hyp always_Cons; break_and.
      apply c; cbn; eauto using lb_execution_invar.
      now find_eapply_lem_hyp always_now'.
  Qed.

  Lemma continuously_bound_on_local_measures_bounds_max :
    forall n ex,
      lb_execution ex ->
      continuously
         (fun ex' =>
            forall h,
              In h (active_nodes (occ_gst (hd ex))) ->
              |h in occ_gst (hd ex')| <= n)
         ex ->
      continuously (fun ex' => max_measure (occ_gst (hd ex')) <= n) ex.
  Proof.
    intros.
    remember (active_nodes (occ_gst (hd ex))) as l.
    find_copy_apply_lem_hyp (active_nodes_always_identical (active_nodes (occ_gst (hd ex))) ex); eauto.
    match goal with
    | H: continuously _ _ |- _ => induction H
    end.
    - apply E0.
      apply always_bound_on_local_measures_bounds_max; eauto.
      now replace (active_nodes (occ_gst (hd s))) with l.
    - apply E_next.
      apply IHeventually; eauto using lb_execution_invar, always_invar, active_nodes_always_identical.
      destruct s.
      repeat (find_apply_lem_hyp always_Cons; break_and).
      cbn in *.
      congruence.
  Qed.

  Lemma continuously_bound_on_local_measures_max_measure_bounded :
    forall n ex,
      lb_execution ex ->
      continuously
         (fun ex' =>
            forall h,
              In h (active_nodes (occ_gst (hd ex))) ->
              |h in occ_gst (hd ex')| <= n)
         ex ->
      eventually (measure_bounded max_measure n) ex.
  Proof.
    intros.
    cut (continuously (fun ex' => max_measure (occ_gst (hd ex')) <= n) ex).
    {
      unfold measure_bounded.
      eapply continuously_monotonic.
      intros.
      destruct s; auto.
    }
    find_apply_lem_hyp continuously_bound_on_local_measures_bounds_max; auto.
  Qed.

  Lemma max_measure_continuously_decreasing_bound :
    forall ex n,
      lb_execution ex ->
      always local_measures_nonincreasing ex ->
      always max_measure_nonzero_eventually_all_locals_below ex ->
      max_measure (occ_gst (hd ex)) = S n ->
      eventually (measure_bounded max_measure n) ex.
  Proof.
    intros.
    apply continuously_bound_on_local_measures_max_measure_bounded; auto.
    apply continuously_forall_list_comm; intros.
    apply measure_eventually_bounded_continuously_bounded;
      eauto using all_measures_nonincreasing_always_each_nonincreasing.
    find_apply_lem_hyp always_now'.
    apply_prop_hyp max_measure_nonzero_eventually_all_locals_below max_measure.
    eauto.
    apply_prop_hyp eventually In.
    eapply eventually_monotonic_simple; eauto.
    intros [o s]; auto.
  Qed.

  Theorem local_measure_causes_max_measure_zero :
    forall ex,
      lb_execution ex ->
      always local_measures_nonincreasing ex ->
      always max_measure_nonzero_eventually_all_locals_below ex ->
      continuously (now (measure_zero max_measure)) ex.
  Proof.
    intros.
    destruct ex.
    remember (max_measure (occ_gst o)) as n eqn:Hmax; symmetry in Hmax.
    generalize dependent o.
    generalize dependent ex.
    induction n using nat_strong_ind; destruct n; intros.
    - apply E0.
      apply measure_zero_stays_zero; eauto using local_always_nonincreasing_causes_max_always_nonincreasing.
    - find_copy_eapply_lem_hyp max_measure_continuously_decreasing_bound; eauto.
      induction 0.
      + destruct s as [o' s].
        remember (max_measure (occ_gst o')) as k eqn:Hk; symmetry in Hk.
        eapply H; try eapply Hk; auto with arith.
        unfold measure_bounded in *.
        find_apply_lem_hyp always_Cons; break_and.
        simpl in *.
        omega.
      + apply E_next, IHeventually;
          eauto using lb_execution_invar, always_invar.
  Qed.

  Lemma and_tl_always_P :
    forall T (P Q : infseq T -> Prop) ex,
      always (P /\_ Q) ex ->
      always P ex.
  Proof.
    intros T P Q.
    cofix c; intros.
    constructor; destruct ex.
    - invc_prop and_tl.
      firstorder.
    - simpl.
      apply c.
      eauto using always_invar.
  Qed.

  Lemma always_and_tl_eq :
    forall T (P Q : infseq T -> Prop) ex,
      always (P /\_ Q) ex <-> (always P /\_ always Q) ex.
  Proof.
    split; intros.
    - split; eapply and_tl_always_P; eauto using always_and_tl_comm.
    - inv_prop and_tl; eapply always_and_tl; eauto.
  Qed.

  Lemma always_continuously_and_tl :
    forall T (P Q : infseq T -> Prop) s,
      continuously (P /\_ Q) s ->
      eventually (always P /\_ always Q) s.
  Proof.
    intros.
    unfold continuously in *.
    eapply eventually_monotonic_simple; [|eauto].
    intros.
    now apply always_and_tl_eq.
  Qed.

  Lemma local_measure_causes_measure_zero_continuosly :
    forall ex,
      lb_execution ex ->
      continuously local_measures_nonincreasing ex ->
      continuously nonzero_error_causes_measure_drop ex ->
      continuously (now (measure_zero global_measure)) ex.
  Proof.
    intros.
    pose proof local_measure_causes_measure_zero.
    prep_always_monotonic.
    apply eventually_idempotent.
    eapply eventually_monotonic_simple; eauto.
    match goal with
    | |- eventually (always ?P /\_ always ?Q /\_ ?R) ex =>
      cut (continuously (P /\_ Q /\_ R) ex)
    end.
    - intros.
      find_apply_lem_hyp always_continuously_and_tl.
      eapply eventually_monotonic_simple; [|eauto].
      firstorder.
      + eapply always_and_tl_eq.
        apply always_and_tl_comm.
        eauto.
      + find_apply_lem_hyp always_and_tl_eq; inv_prop and_tl.
        inv_prop lb_execution; auto.
    - repeat apply continuously_and_tl; auto.
      apply always_continuously.
      apply always_inv;
        eauto using lb_execution_invar.
  Qed.

End LocalMeasure.
