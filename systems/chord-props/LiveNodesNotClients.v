Require Import List.
Require Import Chord.Chord.
Require Import Chord.SystemReachable.
Require Import StructTact.StructTactics.
Require Import StructTact.ListTactics.
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
  apply chord_net_invariant; do 2 autounfold; intros; simpl in *;
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

Lemma sent_non_client_message_means_in_nodes :
  forall gst src dst p,
    reachable_st gst ->
    ~ client_payload p ->
    In (src, (dst, p)) (msgs gst) ->
    In src (nodes gst).
Proof.
  intros.
  generalize dependent p.
  generalize dependent dst.
  generalize dependent src.
  pattern gst.
  apply chord_net_invariant; do 2 autounfold; simpl; intros;
    repeat find_rewrite; intuition eauto;
      try solve [
            find_apply_lem_hyp in_app_or; break_or_hyp;
            [find_apply_lem_hyp in_map_iff; break_exists; break_and;
             unfold send in *; find_injection; in_crush
            |in_crush; eauto with datatypes]
          ].
  - inv_prop initial_st; break_and.
    repeat find_rewrite.
    in_crush.
  - in_crush; eauto.
    unfold send in *.
    find_injection; tauto.
  - simpl in *.
    in_crush; eauto with datatypes.
Qed.
Hint Resolve sent_non_client_message_means_in_nodes.
