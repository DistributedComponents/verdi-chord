Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import InfSeqExt.infseq.

Require Import Chord.Chord.

Require Import Chord.LabeledLemmas.
Require Import Chord.ChannelLemmas.
Require Import Chord.HandlerLemmas.
Require Import Chord.LabeledMeasures.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.

Require Import Chord.LiveNodesStayLive.
Require Import Chord.ValidPointersInvariant.

Require Import mathcomp.ssreflect.ssreflect.

Definition no_msgs_to_live_from (h : addr) (occ : occurrence) :=
  forall dst, live_node (occ_gst occ) dst -> channel (occ_gst occ) h dst = [].

Definition no_msgs_to_live_from_dead_nodes (occ : occurrence) :=
  forall h, In h (failed_nodes (occ_gst occ)) -> no_msgs_to_live_from h occ.

Definition msg_from_length (h : addr) (dst : addr) (occ : occurrence) : nat :=
  length (channel (occ_gst occ) h dst).

Lemma no_msgs_from_dead_nodes_elim :
  forall occ, no_msgs_to_live_from_dead_nodes occ ->
    (forall src, In src (failed_nodes (occ_gst occ)) ->
     forall dst, live_node (occ_gst occ) dst ->
     channel (occ_gst occ) src dst = []).
Proof.
  unfold no_msgs_to_live_from_dead_nodes, no_msgs_to_live_from.
  auto.
Qed.

Lemma always_monotonic_complex :
  forall T (J P Q : infseq T -> Prop),
    (forall s, J s -> P s -> Q s) ->
    (forall x s, J (Cons x s) -> J s) ->
    forall s,
      J s ->
      always P s ->
      always Q s.
Proof.
  intros T J P Q PQ Jinvar.  cofix cf. intros (x, s) HJ HP.
  generalize (@always_Cons _ x s P HP); simpl; intros (a1, a2).
  constructor; simpl; eauto.
Qed.

Set Bullet Behavior "Strict Subproofs".

Lemma dead_nodes_go_quiet :
  forall ex,
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
    lb_execution ex ->
    continuously (now no_msgs_to_live_from_dead_nodes) ex.
Proof.
  intros. unfold continuously.
  unfold no_msgs_to_live_from_dead_nodes, no_msgs_to_live_from.
  remember (occ_gst (hd ex)) as gst.
  remember (fun occ => forall h, In h (failed_nodes gst) ->
                         forall dst, In dst (nodes gst) ->
                                ~ In dst (failed_nodes gst) ->
                                channel (occ_gst occ) h dst = []) as PP.
  remember (fun ex => lb_execution ex /\
                   nodes (occ_gst (hd ex)) = nodes gst /\
                   failed_nodes (occ_gst (hd ex)) = failed_nodes gst) as JJ.
  assert (forall s x, JJ (Cons x s) -> JJ s) as JJ_invar.
  {
    subst.
    intros.
    intuition; inv_prop lb_execution; auto; simpl in *;
      try solve [erewrite <- labeled_step_dynamic_preserves_failed_nodes; [|eauto]; eauto];
      try solve [erewrite <- labeled_step_dynamic_preserves_nodes; [|eauto]; eauto].
  }
  assert (JJ ex) by (subst; intuition).
  eapply eventually_monotonic with (J := JJ) (P := (always (now PP)));
    eauto.
  - intros.
    eapply always_monotonic_complex with
        (J := JJ) (P := (now PP)); eauto.
    intros. subst. intuition.
    destruct s0. simpl in *.
    intros.
    eapply H6; unfold live_node in *; intuition; repeat find_rewrite; eauto.
  - subst. clear JJ_invar.
    intuition.
  (* measure argument on number of msgs from h with nonincreasing obvious,
     eventual drop due to the fact that any given message in the network is
     eventually delivered *)
Admitted.
