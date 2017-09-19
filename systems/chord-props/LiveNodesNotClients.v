Require Import Chord.Chord.
Require Import Chord.SystemReachable.

Lemma live_nodes_not_clients :
  forall gst h,
    reachable_st gst ->
    live_node gst h ->
    ~ client_addr h.
Proof.
(*
This is an easy invariant because of the constraint
  ~ client_addr h
in the Start rule.

DIFFICULTY: 1
USED: In phase two.
*)
Admitted.
Hint Resolve live_nodes_not_clients.
