Require Import List.

Require Import InfSeqExt.infseq.

Require Import Chord.Chord.
Import Chord.Chord.Chord.
Import ChordIDSpace.
Require Import Chord.ChordProof.
Require Import Chord.ChordSemantics.
Import ChordSemantics.
Import ConstrainedChord.

Definition nodes_have_live_succs (gst : global_state) : Prop :=
  forall h st,
    live_node gst h ->
    sigma gst h = Some st ->
    exists s,
      live_node gst (addr_of s) /\
      In s (succ_list st).

Theorem nodes_always_have_live_succs :
  forall ex,
    lb_execution ex ->
    reachable_st ex.(hd).(occ_gst) ->
    always (now (fun occ => nodes_have_live_succs occ.(occ_gst))) ex.
Proof.
Admitted.