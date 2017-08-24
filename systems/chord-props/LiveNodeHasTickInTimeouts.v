Require Import List.
Import ListNotations.

Require Import InfSeqExt.infseq.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.

Lemma live_node_has_Tick_in_timeouts' :
  forall gst h,
    reachable_st gst ->
    live_node gst h ->
    In Tick (timeouts gst h).
Proof.
(*
New nodes have no Tick.
A node with no Tick sets joined = true iff it also registers a Tick.
Having a Tick is preserved by the step.
DIFFICULTY: 3
USED: In phase one.
*)

Admitted.


Lemma live_node_has_Tick_in_timeouts :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    live_node (occ_gst (hd ex)) h ->
    In Tick (timeouts (occ_gst (hd ex)) h).
Proof.
  eauto using live_node_has_Tick_in_timeouts'.
Qed.
