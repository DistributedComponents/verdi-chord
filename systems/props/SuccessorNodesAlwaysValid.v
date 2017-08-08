Require Import List.
Import ListNotations.

Require Import Chord.Chord.

Require Import Chord.ChordSystemReachable.

Definition successor_nodes_valid (gst : global_state) : Prop :=
  forall h p st,
    In p (succ_list st) ->
    sigma gst h = Some st ->
    In (addr_of p) (nodes gst) /\
    exists pst, sigma gst (addr_of p) = Some pst /\
           joined pst = true.

Lemma successor_nodes_always_valid :
  forall gst,
    reachable_st gst ->
    successor_nodes_valid gst.
Proof.
(*
This invariant says every successor list pointer points to a node
that's both live and has joined st = true.  It will require some
strengthening before it's inductive.
- Need to add somethine about the contents of GotPredAndSuccs messages
- Need to say nodes only end up in a sucessor list if they've joined

DIFFICULTY: 3
USED: In phase one.
*)
Admitted.
