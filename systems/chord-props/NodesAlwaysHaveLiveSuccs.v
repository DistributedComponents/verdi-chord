Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.

Require Import Chord.Chord.

Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.

Definition nodes_have_live_succs (gst : global_state) : Prop :=
  forall h st,
    live_node gst h ->
    sigma gst h = Some st ->
    exists s,
      live_node gst (addr_of s) /\
      In s (succ_list st).

Theorem nodes_always_have_live_succs :
  forall gst,
    reachable_st gst ->
    nodes_have_live_succs gst.
Proof.
(*
In Zave's paper, this is one half of the inductive invariant. The
other half of the invariant is SufficientPrincipals. So it's provable,
but it will require coming up with an inductive invariant that works
for verdi-chord.

DIFFICULTY: 5
USED: below to prove node successor lists are nonempty, which is used
in phase one.
 *)
Admitted.

Definition nonempty_succ_lists (gst : global_state) : Prop :=
  forall h st,
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    joined st = true ->
    succ_list st <> [].

Lemma nodes_have_nonempty_succ_lists :
  forall gst,
    reachable_st gst ->
    nonempty_succ_lists gst.
Proof.
  unfold nonempty_succ_lists.
  intros.
  find_apply_lem_hyp nodes_always_have_live_succs;
    eauto using live_node_characterization.
  break_exists.
  intro.
  repeat find_rewrite.
  intuition.
Qed.
