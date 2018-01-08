Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.SystemReachable.

Set Bullet Behavior "Strict Subproofs".

Lemma nodes_same_hash_still_injective :
  forall gst gst',
    nodes gst = nodes gst' ->
    hash_injective_on gst ->
    hash_injective_on gst'.
Proof.
  unfold hash_injective_on.
  intros; repeat find_rewrite; auto.
Qed.
Hint Resolve nodes_same_hash_still_injective.

Theorem hash_injective_invariant :
  forall gst,
    reachable_st gst ->
    hash_injective_on gst.
Proof.
  eapply chord_net_invariant; do 2 autounfold; intros;
    try solve [inv_prop initial_st; tauto
              |eapply nodes_same_hash_still_injective; try eassumption;
               subst; auto].
  unfold hash_injective_on, start_constraint in *; intros.
  repeat find_rewrite; in_crush;
    exfalso; find_eapply_prop hash;
      solve [repeat find_rewrite; now apply in_map
            |repeat find_reverse_rewrite; now apply in_map].
Qed.
