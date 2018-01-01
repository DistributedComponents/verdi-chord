Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.

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
IGNORE

This invariant says every successor list pointer points to a node
that's both live and has joined st = true.  It will require some
strengthening before it's inductive.
- Need to add somethine about the contents of GotPredAndSuccs messages
- Need to say nodes only end up in a sucessor list if they've joined

DIFFICULTY: 3
USED: In phase one.
*)
Admitted.

Lemma active_successors_are_live_nodes :
  forall gst,
    reachable_st gst ->
    forall h p st,
      In p (succ_list st) ->
      sigma gst h = Some st ->
      ~ In (addr_of p) (failed_nodes gst) ->
      live_node gst (addr_of p).
Proof.
  intros.
  find_apply_lem_hyp successor_nodes_always_valid.
  assert (exists pst, sigma gst (addr_of p) = Some pst /\ joined pst = true)
    by firstorder.
  firstorder using live_node_characterization.
Qed.