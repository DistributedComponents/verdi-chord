Require Import List.
Import ListNotations.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.

Definition joined_for_query (q : query) :=
  match q with
  | Join p => false
  | Join2 p => false
  | _ => true
  end.

Theorem cur_request_matches_joined :
  forall gst,
    reachable_st gst ->
    forall h st p q m,
      sigma gst h = Some st ->
      cur_request st = Some (p, q, m) ->
      joined st = joined_for_query q.
Admitted.

Theorem cur_request_join_not_joined :
  forall gst,
    reachable_st gst ->
    forall h st p q m,
      sigma gst h = Some st ->
      cur_request st = Some (p, Join q, m) ->
      joined st = false.
Proof.
  eauto using cur_request_matches_joined.
Qed.

Theorem cur_request_join2_not_joined :
  forall gst,
    reachable_st gst ->
    forall h st p q m,
      sigma gst h = Some st ->
      cur_request st = Some (p, Join2 q, m) ->
      joined st = false.
Proof.
  eauto using cur_request_matches_joined.
Qed.

Theorem nodes_not_joined_have_no_successors :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    joined st = false ->
    succ_list st = [].
Proof.
(*
Nodes do not set their successor lists until they finish joining. I don't really
know what invariants are needed here but they shouldn't be too complicated?

DIFFICULTY: 2
USED: In phase one
*)
Admitted.
