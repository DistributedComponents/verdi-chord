Require Import List.
Import ListNotations.

Require Import InfSeqExt.infseq.

Require Import Chord.Chord.
Require Import Chord.ChordPromises.
Require Import Chord.ChordValidPointersInvariant.
Require Import Chord.ChordLabeledLemmas.
Require Import Chord.ChordHandlerLemmas.
Require Import Chord.ChordSystemLemmas.
Require Import Chord.LiveNodesStayLive.

Definition no_msgs_from (h : addr) (occ : occurrence) :=
  forall dst,
    channel (occ_gst occ) h dst = [].

Definition no_msgs_from_dead_nodes (occ : occurrence) :=
  forall h,
    In h (failed_nodes (occ_gst occ)) ->
    no_msgs_from h occ.

Lemma no_msgs_from_dead_nodes_elim :
  forall occ,
    no_msgs_from_dead_nodes occ ->
    forall src dst,
      In src (failed_nodes (occ_gst occ)) ->
      channel (occ_gst occ) src dst = [].
Proof.
  unfold no_msgs_from_dead_nodes, no_msgs_from.
  auto.
Qed.

Lemma dead_nodes_go_quiet :
  forall ex,
    lb_execution ex ->
    continuously (now no_msgs_from_dead_nodes) ex.
Proof.
  (* measure argument on number of msgs from h with nonincreasing obvious,
     eventual drop due to the fact that any given message in the network is
     eventually delivered *)
Admitted.
