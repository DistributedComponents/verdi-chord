Require Import List.
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

Theorem join2_param_matches :
  forall gst dst h st ns p,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, Join2 ns, p) ->
    dst = ns.
Proof.
Admitted.

Theorem succs_joined :
  forall gst h st s,
    reachable_st gst ->
    sigma gst h = Some st ->
    In s (succ_list st) ->
    exists st__s,
      sigma gst (addr_of s) = Some st__s /\
      joined st__s = true.
Proof.
Admitted.

Theorem stabilize_target_joined :
  forall gst h st dst m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, Stabilize, m) ->
    exists st__d,
      sigma gst (addr_of dst) = Some st__d /\
      joined st__d = true.
Proof.
Admitted.

Theorem stabilize2_target_joined :
  forall gst h st dst sdst m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, Stabilize2 sdst, m) ->
    exists st__d,
      sigma gst (addr_of dst) = Some st__d /\
      joined st__d = true.
Proof.
Admitted.

Theorem join2_target_joined :
  forall gst h st dst jdst m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, Join2 jdst, m) ->
    exists st__d,
      sigma gst (addr_of dst) = Some st__d /\
      joined st__d = true.
Proof.
Admitted.

Theorem live_node_in_succs_best_succ :
  forall gst h st l,
    reachable_st gst ->
    sigma gst h = Some st ->
    live_node gst l ->
    In l (map addr_of (succ_list st)) ->
    exists s, best_succ gst h s.
Proof.
  intros.
Admitted.
