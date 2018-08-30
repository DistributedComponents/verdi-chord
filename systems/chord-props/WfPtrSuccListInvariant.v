Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.ListTactics.

Require Import Chord.Chord.

Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.
Require Import Chord.QueryTargetsJoined.

Lemma wf_ptr_succ_list_invariant' :
  forall gst h st p,
    reachable_st gst ->
    sigma gst h = Some st ->
    In p (succ_list st) ->
    wf_ptr p.
Proof.
  intros.
  cut (all_ptrs wf_ptr gst); eauto using pointers_wf.
  intros.
  inv_prop all_ptrs. eauto.
Qed.

Lemma wf_ptr_succ_list_invariant :
  forall gst h st p rest,
    reachable_st gst ->
    sigma gst h = Some st ->
    succ_list st = p :: rest ->
    wf_ptr p.
Proof.
  intros.
  eapply wf_ptr_succ_list_invariant'; eauto. find_rewrite. in_crush.
Qed.
