Require Import Chord.Chord.
Require Import Chord.SystemReachable.

Theorem stabilize2_param_matches :
  forall gst dst h st ns p,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, Stabilize2 ns, p) ->
    dst = ns.
Proof.
Admitted.
