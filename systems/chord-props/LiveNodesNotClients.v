Require Import List.
Require Import Chord.Chord.
Require Import Chord.SystemReachable.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.

Set Bullet Behavior "Strict Subproofs".

Lemma nodes_not_clients :
  forall gst,
    reachable_st gst ->
    forall h,
      In h (nodes gst) ->
      ~ client_addr h.
Proof.
  intros until 1.
  pattern gst.
  apply chord_net_invariant; autounfold; intros; simpl in *;
    try solve [repeat find_rewrite; eauto].
  - inv_prop initial_st; break_and.
    unfold not in *; eauto.
  - repeat find_rewrite.
    simpl in *; break_or_hyp; eauto.
Qed.
Hint Resolve nodes_not_clients.

Lemma live_nodes_not_clients :
  forall gst h,
    reachable_st gst ->
    live_node gst h ->
    ~ client_addr h.
Proof.
  intros. unfold live_node in *.
  intuition. eapply nodes_not_clients; eauto.
Qed.
Hint Resolve live_nodes_not_clients.
