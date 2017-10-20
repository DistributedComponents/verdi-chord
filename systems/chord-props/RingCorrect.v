Require Import Chord.Chord.
Require Import Chord.SystemReachable.

Definition at_least_one_ring (gst : global_state) : Prop :=
  exists h, ring_member gst h.

Definition at_most_one_ring (gst : global_state) : Prop :=
  forall x y,
    ring_member gst x ->
    ring_member gst y ->
    reachable gst x y.

Definition connected_appendages (gst : global_state) : Prop :=
  forall a, live_node gst a ->
       exists r, ring_member gst r /\ reachable gst a r.

Definition sufficient_principals (gst : global_state) : Prop :=
  exists ps,
    principals gst ps /\
    length ps > SUCC_LIST_LEN.

Definition state_invariant (gst : global_state) : Prop :=
  sufficient_principals gst /\
  live_node_in_succ_lists gst.
