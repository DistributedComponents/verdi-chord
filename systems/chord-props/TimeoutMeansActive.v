Require Import List.

Require Import StructTact.StructTactics.

Require Import Chord.Chord.
Require Import Chord.SystemReachable.

Require Import Chord.HandlerLemmas.

Definition timeout_means_active_invariant (gst : global_state) : Prop :=
  forall h t,
    In t (timeouts gst h) ->
    In h (nodes gst).
Hint Unfold timeout_means_active_invariant.

Theorem timeout_means_active_inductive :
  forall gst,
    reachable_st gst ->
    timeout_means_active_invariant gst.
Proof using.
  eapply chord_net_invariant; autounfold; intros;
    repeat find_rewrite;
    repeat handler_simpl.
  inv_prop initial_st; expand_def.
  destruct (In_dec addr_eq_dec h (nodes gst)); auto.
  assert (timeouts gst h = nil).
  auto.
  repeat find_rewrite.
  exfalso; eapply in_nil; eauto.
Qed.

Lemma timeout_means_active :
  forall gst,
    reachable_st gst ->
    forall t h,
      In t (timeouts gst h) ->
      In h (nodes gst).
Proof.
  intros.
  eapply timeout_means_active_inductive; eauto.
Qed.
