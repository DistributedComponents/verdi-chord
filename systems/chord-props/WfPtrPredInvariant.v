Require Import List.
Import ListNotations.

Require Import Chord.Chord.

Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.

Lemma wf_ptr_pred_invariant :
  forall gst h st p,
    reachable_st gst ->
    sigma gst h = Some st ->
    pred st = Some p ->
    wf_ptr p.
Proof.
(* 
This lemma says the same thing as wf_ptr_succ_list_invariant, but for
predecessor pointers instead of successor pointers.

DIFFICULTY: 3
USED: Nowhere? I think I could use it in phase two to lift some assumptions.
 *)
Admitted.
