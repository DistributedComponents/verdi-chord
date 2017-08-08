Require Import List.
Import ListNotations.

Require Import Chord.Chord.

Require Import Chord.ChordSystemReachable.

Theorem nodes_not_joined_have_no_successors :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    joined st = false ->
    succ_list st = [].
Proof.
(*
Nodes do not set their successor lists until they finish joining. I don't really
know what invariants are needed here but they shouldn't be too complicated?

DIFFICULTY: 2
USED: In phase one
*)
Admitted.
