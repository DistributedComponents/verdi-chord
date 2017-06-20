Require Import List.
Import ListNotations.

Require Import InfSeqExt.infseq.

Require Import Chord.Chord.
Import Chord.Chord.Chord.
Import ChordIDSpace.
Require Import Chord.ChordProof.
Require Import Chord.ChordSemantics.
Import ChordSemantics.
Import ConstrainedChord.
Require Import Chord.ChordValidPointersInvariant.

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

Definition circular_wait : occurrence -> Prop.
Admitted.

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
Admitted.


Lemma wf_ptr_succ_list_invariant :
  forall gst h st p rest,
    reachable_st gst ->
    sigma gst h = Some st ->
    succ_list st = p :: rest ->
    wf_ptr p.
Proof.
Admitted.

Definition nonempty_succ_lists (gst : global_state) : Prop :=
  forall h st,
    sigma gst h = Some st ->
    joined st = true ->
    succ_list st <> [].

Lemma nodes_have_nonempty_succ_lists :
  forall gst,
    reachable_st gst ->
    nonempty_succ_lists gst.
Proof.
Admitted.