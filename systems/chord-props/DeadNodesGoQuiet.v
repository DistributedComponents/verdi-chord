Require Import List.
Import ListNotations.

Require Import InfSeqExt.infseq.

Require Import Chord.Chord.

Require Import Chord.LabeledLemmas.
Require Import Chord.ChannelLemmas.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.

Require Import Chord.LiveNodesStayLive.
Require Import Chord.ValidPointersInvariant.

Require Import mathcomp.ssreflect.ssreflect.

Definition no_msgs_to_live_from (h : addr) (occ : occurrence) :=
  forall dst, live_node (occ_gst occ) dst -> channel (occ_gst occ) h dst = [].

Definition no_msgs_to_live_from_dead_nodes (occ : occurrence) :=
  forall h, In h (failed_nodes (occ_gst occ)) -> no_msgs_to_live_from h occ.

Definition msg_from_length (h : addr) (dst : addr) (occ : occurrence) : nat :=
  length (channel (occ_gst occ) h dst).

Lemma no_msgs_from_dead_nodes_elim :
  forall occ, no_msgs_to_live_from_dead_nodes occ ->
    (forall src, In src (failed_nodes (occ_gst occ)) ->
     forall dst, live_node (occ_gst occ) dst ->
     channel (occ_gst occ) src dst = []).
Proof.
  unfold no_msgs_to_live_from_dead_nodes, no_msgs_to_live_from.
  auto.
Qed.

Lemma dead_nodes_go_quiet :
  forall ex,
    lb_execution ex ->
    continuously (now no_msgs_to_live_from_dead_nodes) ex.
Proof.
  (* measure argument on number of msgs from h with nonincreasing obvious,
     eventual drop due to the fact that any given message in the network is
     eventually delivered *)
Admitted.
