Require Import List.
Import ListNotations.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.

Lemma ptr_correct :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    ptr st = make_pointer h.
Proof.
(*
This is a very good and easy invariant.  At a node h, ptr st is a copy
of a pointer to h. It's set when the node starts up and never changed
anywhere.

DIFFICULTY: 1
USED: In phase two.
*)
Admitted.
