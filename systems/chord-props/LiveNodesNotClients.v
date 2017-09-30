Require Import List.
Require Import Chord.Chord.
Require Import Chord.SystemReachable.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.

Set Bullet Behavior "Strict Subproofs".

Lemma nodes_not_clients :
  forall gst h,
    reachable_st gst ->
    In h (nodes gst) ->
    ~ client_addr h.
Proof.
  intros. induct_reachable_st.
  - (* need to know that clients aren't initial nodes (probably has to be an axiom) *)
    admit.
  - intros.
    inversion H0; subst; simpl in *;
      intuition; subst; eauto.
Admitted.

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
