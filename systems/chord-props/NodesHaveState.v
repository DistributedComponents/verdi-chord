Require Import List.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.SystemReachable.

Require Import Chord.SystemLemmas.
Require Import Chord.HandlerLemmas.

Set Bullet Behavior "Strict Subproofs".

Definition nodes_have_state_invariant (gst : global_state) :=
  forall h, In h (nodes gst) ->
       exists st,
         sigma gst h = Some st.
Hint Unfold nodes_have_state_invariant.

Theorem nodes_have_state_preserved :
  forall gst,
    reachable_st gst ->
    nodes_have_state_invariant gst.
Proof using.
  eapply chord_net_invariant; do 2 autounfold; intros;
    repeat find_rewrite;
    repeat (update_destruct; rewrite_update);
      eauto with datatypes.
  simpl in *; break_or_hyp;
    congruence || eauto.
Qed.

Lemma nodes_have_state :
  forall gst h,
    In h (nodes gst) ->
    reachable_st gst ->
    exists st,
      sigma gst h = Some st.
Proof.
  intros.
  now eapply nodes_have_state_preserved.
Qed.
Hint Resolve nodes_have_state.

Lemma only_nodes_have_state :
  forall gst h st,
    sigma gst h = Some st ->
    reachable_st gst ->
    In h (nodes gst).
Proof.
  intros.
  generalize dependent st.
  generalize dependent h.
  pattern gst.
  eapply chord_net_invariant; do 2 autounfold; intros;
    repeat find_rewrite;
    repeat handler_simpl;
    eauto with datatypes.
  inv_prop initial_st.
  break_and.
  destruct (In_dec addr_eq_dec h (nodes gst0)); eauto.
  assert (sigma gst0 h = None) by auto.
  congruence.
Qed.
Hint Resolve only_nodes_have_state.

Lemma in_failed_in_nodes :
  forall gst h,
    reachable_st gst ->
    In h (failed_nodes gst) ->
    In h (nodes gst).
Proof.
  induction 1; intros.
  - unfold initial_st in *.
    intuition; repeat find_rewrite; solve_by_inversion.
  - invcs H0; intuition.
    subst. auto.
Qed.
