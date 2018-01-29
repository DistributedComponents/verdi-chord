Require Import Chord.Chord.
Require Import Chord.SystemReachable.
Require Import Chord.FirstSuccNeverSelf.
Require Import Chord.PredNeverSelfInvariant.

Set Bullet Behavior "Strict Subproofs".

Lemma successors_are_live_nodes :
  forall gst h s,
    reachable_st gst ->
    has_first_succ gst h s ->
    live_node gst (addr_of s).
Proof using.
(*
  This won't be inductive as written. We'll have to generalize to all nodes in
  successor lists and possibly do some accounting for how joining works.

  DIFFICULTY: Ryan.
  USED: In phase two.
 *)
Admitted.
