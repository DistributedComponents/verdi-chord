Require Import List.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.SystemReachable.

Require Import Chord.SystemLemmas.
Require Import Chord.HandlerLemmas.
Require Import Chord.LabeledLemmas.

Set Bullet Behavior "Strict Subproofs".

Theorem nodes_have_state_preserved :
  forall gst gst',
    (forall h, In h (nodes gst) -> exists st, sigma gst h = Some st) ->
    step_dynamic gst gst' ->
    (forall h, In h (nodes gst') -> exists st, sigma gst' h = Some st).
Proof using.
  intros.
  break_step.
  - destruct (addr_eq_dec h h0).
    + subst_max.
      apply update_for_start_sigma_h_exists.
    + find_rewrite_lem update_for_start_nodes_eq.
      find_apply_lem_hyp in_inv.
      break_or_hyp; try (exfalso; eauto; fail).
      find_apply_hyp_hyp.
      break_exists_exists.
      eapply update_for_start_sigma_h_n; eauto.
  - eauto.
  - destruct (addr_eq_dec h h0).
    * eexists.
      now apply update_eq.
    * apply_prop_hyp In (In h).
      break_exists_exists.
      now eauto using sigma_ahr_passthrough.
  - destruct (addr_eq_dec (fst (snd m)) h).
    * eexists.
      now apply update_eq.
    * simpl.
      find_apply_hyp_hyp.
      break_exists_exists.
      repeat find_reverse_rewrite.
      now apply update_diff.
  - admit.
  - admit.
Admitted.

Lemma nodes_have_state :
  forall gst h,
    In h (nodes gst) ->
    reachable_st gst ->
    exists st,
      sigma gst h = Some st.
Proof.
  intros.
  generalize dependent h.
  induct_reachable_st; intros.
  - unfold initial_st in *; break_and.
    destruct (start_handler h (nodes gst)) as [[? ?] ?] eqn:?.
    eapply_prop_hyp start_handler start_handler; auto.
    break_and; eauto.
  - eapply nodes_have_state_preserved; eauto.
Qed.
