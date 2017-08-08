Require Import List.
Import ListNotations.

Require Import Chord.Chord.

Require Import Chord.ChordSystemReachable.

Theorem stabilize_only_with_first_succ :
  forall gst h st dst,
    reachable_st gst ->
    sigma gst h = Some st ->
    In (Request dst GetPredAndSuccs) (timeouts gst h) ->
    exists s,
      addr_of s = dst /\
      cur_request st = Some (s, Stabilize, GetPredAndSuccs) /\
      hd_error (succ_list st) = Some s.
Proof.
  intros. eexists. repeat split.
(*
This lemma says that if we have an appropriate Request timeout, we
have all the other trappings of a Stabilize request. It's going to be
some work to prove because we have to show that
- whenever we register timeouts we also set the other stuff
- when the timeout isn't removed, the other stuff doesn't change

DIFFICULTY: 3
USED: In phase one.
*)
Admitted.
