Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.ListTactics.

Require Import Chord.Chord.

Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.

Lemma wf_ptr_succ_list_invariant' :
  forall gst h st p,
    reachable_st gst ->
    sigma gst h = Some st ->
    In p (succ_list st) ->
    wf_ptr p.
Proof.
(*
IGNORE

This invariant says pointers in successor lists are well-formed. It
should be inductive if we tack on something about the contents of
GotPredAndSuccs/GotSuccList messages.

DIFFICULTY: 3
USED: In phase one.
*)
Admitted.


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
