Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.

Require Import Chord.Chord.

Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.

Set Bullet Behavior "Strict Subproofs".

Theorem valid_ptrs_global_start_invariant :
  chord_start_invariant valid_ptrs_global.
Proof.
  unfold chord_start_invariant.
  intros.
  destruct (start_handler _ _) as [[?st ?ms] ?newts] eqn:?H; subst res0.
  find_eapply_lem_hyp update_for_start_definition; expand_def.
  find_copy_eapply_lem_hyp valid_ptrs_global_elim; break_and.
  apply valid_ptrs_global_intro; try intro h'; intros; subst_max.
  - eapply valid_ptrs_timeouts_preserved; eauto.
    + intros.
      simpl in *.
      admit.
      (*
      match goal with
      | [H: context[Request ?k ?m] |- _] =>
        destruct (addr_eq_dec h h'), (timeout_eq_dec t (Request k m)); subst
      end.
      * right.
        do 2 constructor.
        apply valid_ptr_intro.
        -- apply make_pointer_valid.
        -- repeat find_rewrite.
           simpl; tauto.
      * exfalso.
        tuple_inversion.
        repeat find_rewrite.
        find_rewrite_lem update_same.
        find_eapply_lem_hyp in_inv.
        break_or_hyp; auto.
      * repeat find_rewrite.
        find_erewrite_lem update_diff.
        tauto.
      * repeat find_rewrite.
        find_erewrite_lem update_diff.
        tauto.
      *)
    + intros.
      repeat find_rewrite.
      auto with datatypes.
  - destruct (addr_eq_dec h h'); subst.
    + destruct (sigma _ _) as [a |] eqn:?H; constructor.
      * repeat find_rewrite.
        find_rewrite_lem update_same.
        find_injection.
        find_eapply_lem_hyp start_handler_valid_ptrs_state; eauto;
          repeat find_rewrite; auto with datatypes.
    + repeat find_rewrite.
      rewrite update_diff; auto.
      match goal with
      | [H: context[lift_pred_opt] |- _] =>
        pose proof (H h')
      end.
      find_apply_lem_hyp lift_pred_opt_elim;
        break_or_hyp; try break_exists; break_and.
      * repeat find_rewrite.
        constructor.
        eapply valid_ptrs_state_nodes_subset; eauto.
        find_rewrite.
        intros; auto with datatypes.
      * admit.
  - admit. (* net case *)
  - admit. (* trace case *)
Admitted.

Theorem valid_ptrs_global_inductive :
  forall gst,
    reachable_st gst ->
    valid_ptrs_global gst.
Proof using.
  intros.
  induction H.
  - admit.
  - unfold valid_ptrs_global; repeat break_and_goal.
    + eapply valid_ptrs_global_timeouts; eauto.
    + intros;
        destruct (sigma _ _) eqn:H_st;
        constructor;
        eapply valid_ptrs_global_sigma; eauto.
    + eapply valid_ptrs_global_net; eauto.
    + eapply valid_ptrs_global_trace; eauto.
Admitted.
