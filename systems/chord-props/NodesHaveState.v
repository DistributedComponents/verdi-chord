Require Import List.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.SystemReachable.

Require Import Chord.SystemLemmas.
Require Import Chord.HandlerLemmas.
Require Import Chord.LabeledLemmas.

Set Bullet Behavior "Strict Subproofs".

Lemma run_init_for_creates_st :
  forall l h gst,
    NoDup l ->
    In h l ->
    In h (nodes (fold_left run_init_for l gst)) ->
    exists st,
      sigma (fold_left run_init_for l gst) h = Some st.
Proof.
  induction l; intros.
  - easy.
  - simpl in *.
    break_or_hyp.
    + unfold run_init_for.
      assert (~ In h l)
        by now apply NoDup_cons_iff.
      rewrite fold_left_for_each_not_in;
        eauto using sigma_apply_handler_result_diff.
      destruct (start_handler h initial_nodes) as [[? ?] ?].
      eauto using apply_handler_result_updates_sigma.
    + eapply IHl; eauto.
      eapply NoDup_cons_iff; eauto.
Qed.

Lemma in_run_init_for_nodes_in_l_or_acc :
  forall l h gst,
    In h (nodes (fold_left run_init_for l gst)) ->
    In h l \/ In h (nodes gst).
Proof.
  induction l; intros.
  - tauto.
  - simpl in *.
    find_apply_lem_hyp IHl.
    unfold run_init_for in *.
    erewrite <- apply_handler_result_preserves_nodes in * by eauto.
    tauto.
Qed.

Lemma initial_st_node_in_initial_nodes :
  forall h,
    In h (nodes initial_st) ->
    In h initial_nodes.
Proof.
  unfold initial_st.
  intros.
  find_apply_lem_hyp in_run_init_for_nodes_in_l_or_acc.
  tauto.
Qed.

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
  - unfold initial_st in *.
    apply run_init_for_creates_st;
      eauto using initial_nodes_NoDup, initial_st_node_in_initial_nodes.
  - eapply nodes_have_state_preserved; eauto.
Qed.
