Require Import List.
Require Import Omega.
Require Import StructTact.StructTactics.

Require Import Chord.Chord.
Require Import Chord.SystemReachable.

Definition sufficient_principals (gst : global_state) : Prop :=
  exists ps,
    principals gst ps /\
    length ps > SUCC_LIST_LEN.

Definition zave_invariant (gst : global_state) : Prop :=
  sufficient_principals gst /\
  live_node_in_succ_lists gst.

Theorem zave_invariant_holds :
  forall gst,
    reachable_st gst ->
    zave_invariant gst.
Proof.
Admitted.

Lemma first_succ_and_others_distinct :
  forall gst h st s1 s2 xs ys,
    reachable_st gst ->
    sigma gst h = Some st ->
    succ_list st = xs ++ s1 :: ys ->
    In s2 (xs ++ ys) ->
    addr_of s1 <> addr_of s2.
Proof.
Admitted.
Hint Resolve first_succ_and_others_distinct.
