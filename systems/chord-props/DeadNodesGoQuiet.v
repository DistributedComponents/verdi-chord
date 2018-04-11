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
Require Import Chord.NodesHaveState.
Require Import Classical.

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

Lemma hd_now :
  forall T (ex : infseq T) (P : T -> Prop),
    P (hd ex) ->
    now P ex.
Proof.
  intros.
  destruct ex. simpl in *. auto.
Qed.

Lemma Forall_continuously_commute:
  forall (T X : Type) (ex : infseq T) (L : list X) (P : X ->  T -> Prop),
    Forall (fun x => continuously (now (P x)) ex) L ->
    continuously (now (fun t => Forall (fun x => P x t) L)) ex.
Proof.
  induction L.
  - intros. simpl in *.
    unfold continuously. apply E0.
    apply always_inv;
      intros; apply hd_now;
      eauto using Forall_nil.
  - intros. simpl.
    inv_prop Forall.
    eapply continuously_monotonic with
        (P := and_tl (now (fun t => Forall (fun x => P x t) L))
                     (now (P a))).
    + intros. unfold and_tl in *. intuition.
      repeat find_apply_lem_hyp now_hd.
      apply hd_now. auto.
    + apply continuously_and_tl; auto.
Qed.

Lemma ForallPairs_nil :
  forall X (Q : X -> X -> Prop),
    ForallPairs Q [].
Proof.
  intros.
  unfold ForallPairs. simpl. intuition.
Qed.

Lemma ForallPairs_cons_intro :
  forall X (Q : X -> X -> Prop) L x,
    ForallPairs Q L ->
    Q x x ->
    Forall (fun y => Q y x) L ->
    Forall (fun y => Q x y) L ->
    ForallPairs Q (x :: L).
Proof.
  intros.
  unfold ForallPairs. intros.
  simpl in *.
  intuition; subst; intuition eauto;
    find_eapply_lem_hyp Forall_forall; eauto;
      simpl in *; auto.
Qed.

Lemma ForallPairs_cons_elim :
  forall X (Q : X -> X -> Prop) L x,
    ForallPairs Q (x :: L) ->
    Q x x /\
    Forall (fun y => Q y x) L /\
    Forall (fun y => Q x y) L /\
    ForallPairs Q L.
Proof.
  intros.
  unfold ForallPairs in *. simpl in *.
  intuition eauto;
    apply Forall_forall; eauto.
Qed.

Lemma ForallPairs_continuously_commute :
  forall T X (ex : infseq T) L (Q : X -> X -> T -> Prop),
    (forall x s, Q x x s) ->
    (ForallPairs (fun x y => continuously (now (Q x y)) ex) L) ->
    continuously (now (fun t => ForallPairs (fun x y => Q x y t) L)) ex.
Proof.
  induction L.
  - intros. simpl in *.
    unfold continuously. apply E0.
    apply always_inv; simpl in *;
      intros; apply hd_now; eauto using ForallPairs_nil.
  - intros. simpl.
    find_apply_lem_hyp ForallPairs_cons_elim. intuition.
    eapply continuously_monotonic with
        (P := and_tl (now (fun t => ForallPairs (fun x y => Q x y t) L))
                     (and_tl
                        (now (fun t => Forall (fun y => Q y a t) L))
                        (now (fun t => Forall (fun y => Q a y t) L)))).
    + intros. unfold and_tl in *. intuition.
      repeat find_apply_lem_hyp now_hd.
      apply hd_now.
      eauto using  ForallPairs_cons_intro.
    + apply continuously_and_tl; eauto.
      apply continuously_and_tl;
        eauto using Forall_continuously_commute.
Qed.

(* Stand back, I'm going to try classical logic *)
Lemma continuously_imp :
  forall T (P : Prop) (Q : T -> Prop) ex,
    (P ->  continuously (now Q) ex) ->
    continuously (now (fun x => P -> Q x)) ex.
Proof.
  unfold continuously. intros.
  destruct (classic P).
  - intuition.
    eapply eventually_monotonic_simple; [|eauto]; eauto.
    intros.
    eapply always_monotonic; [|eauto]; eauto.
    intros.
    eapply now_monotonic; [|eauto]; eauto.
  - apply E0. apply always_inv; intros; apply hd_now; intuition.
Qed.

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
  remember (fun occ h dst => ~ In dst (failed_nodes gst) ->
                          In h (failed_nodes gst) ->
                          channel (occ_gst occ) h dst = []) as R.
  remember (fun occ =>
              ForallPairs (R occ) (nodes gst)) as PP.
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
    eapply H6; unfold live_node in *; intuition; repeat find_rewrite;
      eauto using in_failed_in_nodes.
  - subst. clear JJ_invar.
    intuition.
    eapply ForallPairs_continuously_commute; [intuition|].
    unfold ForallPairs. intros.
    apply continuously_imp.
    intros.
    apply continuously_imp.
    intros.
    eapply dead_node_channel_empties_out'; eauto.
  (* measure argument on number of msgs from h with nonincreasing obvious,
     eventual drop due to the fact that any given message in the network is
     eventually delivered *)
Qed.
