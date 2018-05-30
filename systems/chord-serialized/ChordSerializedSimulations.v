Require Import List.

Require Import InfSeqExt.infseq.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Cheerios.Cheerios.

Require Import Chord.Chord.
Require Import Chord.ChordSerialized.
Require Import Chord.QueriesEventuallyStop.
Require Import Chord.SystemReachable.

(* useful definitions and lemmas *)
Definition serialize_msg (m : ChordSemantics.msg) : ChordSerializedSemantics.msg :=
  match m with
  | (src, (dst, m)) => (src, (dst, serialize_top (serialize m)))
  end.

Lemma serialize_revert_msg : forall m,
    (revert_msg (serialize_msg m)) = m.
Proof.
  intros.
  unfold serialize_msg.
  do 2 break_let.
  unfold revert_msg, revert_payload.
  rewrite serialize_deserialize_top_id.
  reflexivity.
Qed.

Lemma serialize_revert_msgs : forall l,
    map revert_msg (map serialize_msg l) = l.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite (serialize_revert_msg a), IHl.
    reflexivity.
Qed.

Definition serialize_event (e : ChordSemantics.event) :=
  match e with
  | ChordSemantics.e_send m => e_send (serialize_msg m)
  | ChordSemantics.e_recv m => e_recv (serialize_msg m)
  | ChordSemantics.e_timeout h t => e_timeout h t
  | ChordSemantics.e_fail h => e_fail h
  end.

Lemma serialize_revert_event : forall e,
    revert_event (serialize_event e) = e.
Proof.
  intros.
  unfold serialize_event, revert_event.
  break_match;
    break_match; try congruence;
    find_inversion;
    rewrite serialize_revert_msg;
    reflexivity.
Qed.

Lemma serialize_revert_events : forall l,
    map revert_event (map serialize_event l) = l.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite (serialize_revert_event a), IHl.
    reflexivity.
Qed.

Definition serialize_global_state (gst : ChordSemantics.global_state) :=
  {| nodes := ChordSemantics.nodes gst;
     failed_nodes := ChordSemantics.failed_nodes gst;
     timeouts := ChordSemantics.timeouts gst;
     sigma := ChordSemantics.sigma gst;
     msgs := map serialize_msg (ChordSemantics.msgs gst);
     trace := map serialize_event (ChordSemantics.trace gst) |}.

Lemma serialize_revert_global_state : forall gst,
    revert_global_state (serialize_global_state gst) = gst.
Proof.
  intros.
  unfold serialize_global_state, revert_global_state.
  simpl.
  rewrite serialize_revert_msgs.
  rewrite serialize_revert_events.
  assert ((fun h => ChordSemantics.timeouts gst h)= ChordSemantics.timeouts gst).
  - reflexivity.
  - find_rewrite.
    destruct gst.
    reflexivity.
Qed.

Lemma map_send_serialize : forall h ms,
    map (send h) (map serialize_dst_msg ms) = map serialize_msg (map (ChordSemantics.send h) ms).
Proof.
  intros.
  induction ms.
  - reflexivity.
  - simpl.
    break_let.
    rewrite IHms.
    unfold send.
    reflexivity.
Qed.

Lemma serialize_revert_payload : forall p,
    revert_payload (serialize_top (serialize p)) = p.
Proof.
  intros.
  unfold revert_payload.
  rewrite serialize_deserialize_top_id.
  reflexivity.
Qed.

Definition revert_dst_msg (m : addr * payload) :=
  match m with
  | (h, p) => (h, revert_payload p)
  end.

Lemma serialize_revert_dst_msg : forall m,
    revert_dst_msg (serialize_dst_msg m) = m.
Proof.
  intros.
  unfold revert_dst_msg, serialize_dst_msg.
  break_let.
  break_let.
  find_inversion.
  unfold revert_payload.
  rewrite serialize_deserialize_top_id.
  reflexivity.
Qed.

Lemma serialize_revert_dst_msgs : forall l,
    map revert_dst_msg (map serialize_dst_msg l) = l.
Proof.
  induction l.
  - reflexivity.
  - simpl.
    rewrite serialize_revert_dst_msg, IHl.
    reflexivity.
Qed.

Lemma serialize_timeout_constraint : forall gst h t,
    ChordSemantics.timeout_constraint gst h t ->
    timeout_constraint (serialize_global_state gst) h t.
Proof.
  unfold timeout_constraint.
  intros.
  rewrite serialize_revert_global_state.
  assumption.
Qed.

Lemma revert_msg_send_revert_dst_msg : forall h ms,
    map revert_msg (map (send h) ms) =
    map (ChordSemantics.send h) (map revert_dst_msg ms).
Proof.
  induction ms.
  - reflexivity.
  - unfold ChordSemantics.send, revert_dst_msg.
    simpl. break_let.
    rewrite IHms.
    reflexivity.
Qed.

(* simulation theorems *)
Lemma labeled_step_serialized_labeled_step: forall gst l gst',
    ChordSemantics.labeled_step_dynamic gst l gst' ->
    ChordSerializedSemantics.labeled_step_dynamic (serialize_global_state gst)
                                                  l
                                                  (serialize_global_state gst').
Proof.
  intros.
  inversion H.
  - eapply LTimeout; eauto.
    + unfold timeout_handler_l, serialize_res. repeat break_let.
      find_inversion.
      eauto.
    + subst_max.
      unfold serialize_global_state.
      simpl.
      do 2 rewrite map_app.
      rewrite map_send_serialize.
      reflexivity.
    + apply serialize_timeout_constraint.
      assumption.
  - apply (LDeliver_node (serialize_global_state gst) (serialize_global_state gst')
                         (serialize_msg m) h d
                         (map serialize_msg xs) (map serialize_msg ys)
                         (map serialize_dst_msg ms)
                         l st newts clearedts);
      try assumption.
    + simpl.
      subst_max. find_rewrite.
      rewrite map_app.
      reflexivity.
    + destruct m.
      subst_max.
      unfold serialize_msg.
      break_let.
      reflexivity.
    + unfold serialize_msg.
      do 2 break_let.
      simpl.
      unfold recv_handler_l.
      unfold serialize_res.
      repeat break_let.
      match goal with
      | H : context[revert_payload] |- _ => unfold revert_payload in H;
                                              rewrite serialize_deserialize_top_id in H
      end.
      simpl in *.
      find_rewrite.
      find_inversion.
      reflexivity.
    + subst_max.
      unfold serialize_global_state.
      simpl.
      repeat rewrite map_app.
      rewrite map_send_serialize.
      reflexivity.
  - eapply LInput; eauto.
    + unfold client_payload.
      match goal with
      | H : ChordSemantics.client_payload ?p |- _ => exists p
      end.
      intuition.
      unfold label_input.
      rewrite serialize_revert_payload.
      subst_max.
      reflexivity.
    + subst_max.
      unfold serialize_global_state, update_msgs_and_trace.
      simpl.
      rewrite map_app.
      simpl.
      reflexivity.
  - eapply LDeliver_client; eauto.
    + simpl. subst_max. find_rewrite.
      rewrite map_app. reflexivity.
    + subst_max.
      unfold serialize_msg. repeat break_let.
      reflexivity.
    + subst_max.
      unfold label_output, serialize_msg. repeat break_let.
      simpl. rewrite serialize_revert_payload. reflexivity.
    + subst_max.
      unfold serialize_global_state, update_msgs_and_trace.
      simpl.
      do 2 rewrite map_app.
      reflexivity.
Qed.

Lemma serialized_labeled_step_labeled_step: forall gst l gst',
    ChordSerializedSemantics.labeled_step_dynamic gst l gst' ->
    ChordSemantics.labeled_step_dynamic (revert_global_state gst)
                                        l
                                        (revert_global_state gst').
Proof.
  intros.
  inversion H.
  - unfold timeout_handler_l, serialize_res in *.
    repeat break_let.
    unfold revert_global_state.
    find_inversion.
    eapply ChordSemantics.LTimeout; eauto.
    unfold ChordSemantics.apply_handler_result. simpl.
    repeat rewrite map_app.
    rewrite revert_msg_send_revert_dst_msg.
    rewrite  serialize_revert_dst_msgs.
    reflexivity.
  - apply (ChordSemantics.LDeliver_node
             (revert_global_state gst) (revert_global_state gst')
             (revert_msg m) h d
             (map revert_msg xs) (map revert_msg ys) (map revert_dst_msg ms)
             l st newts clearedts);
      try assumption.
    + unfold revert_global_state. simpl.
      subst_max. find_rewrite.
      rewrite map_app. reflexivity.
    + subst_max.
      unfold revert_msg. repeat break_let.
      reflexivity.
    + unfold revert_msg, recv_handler_l, serialize_res in *.
      repeat break_let. simpl in *.
      subst_max. find_rewrite.
      find_inversion.
      rewrite serialize_revert_dst_msgs.
      reflexivity.
    + subst_max.
      unfold revert_global_state. simpl.
      repeat rewrite map_app.
      rewrite revert_msg_send_revert_dst_msg.
      reflexivity.
  - eapply ChordSemantics.LInput; eauto.
    + unfold client_payload in *.
      break_exists. intuition.
      unfold revert_payload. subst_max.
      rewrite serialize_deserialize_top_id. assumption.
    + subst_max.
      unfold revert_global_state, ChordSemantics.update_msgs_and_trace. simpl.
      repeat rewrite map_app.
      reflexivity.
  - eapply (ChordSemantics.LDeliver_client); eauto.
    + simpl. subst_max. find_rewrite.
      rewrite map_app.
      reflexivity.
    + subst_max. unfold revert_msg. repeat break_let.
      reflexivity.
    + subst_max.
      unfold label_output, revert_msg. repeat break_let.
      reflexivity.
    + subst_max.
      unfold revert_global_state, update_msgs_and_trace. simpl.
      repeat rewrite map_app.
      reflexivity.
Qed.

Lemma step_dynamic_serialized_step_dynamic : forall gst gst',
    step_dynamic gst gst' ->
    ChordSemantics.step_dynamic (revert_global_state gst) (revert_global_state gst').
Proof.
  intros.
  induction H.
  - eapply ChordSemantics.Start; eauto.
    unfold update_for_start in *.
    unfold ChordSemantics.update_for_start, revert_global_state.
    subst_max.
    simpl.
    repeat break_let.
    unfold ChordSemantics.send.
    repeat rewrite map_app.
    unfold send.
    simpl.
    rewrite serialize_revert_payload.
    reflexivity.
  - eapply ChordSemantics.Fail; eauto.
    subst_max.
    unfold revert_global_state, fail_node. simpl.
    reflexivity.
  - unfold timeout_handler, serialize_res in *. repeat break_let.
    eapply ChordSemantics.Timeout; eauto.
    subst_max.
    unfold revert_global_state, apply_handler_result. simpl.
    find_inversion.
    repeat rewrite map_app.
    rewrite revert_msg_send_revert_dst_msg.
    rewrite serialize_revert_dst_msgs.
    reflexivity.
  - unfold revert_global_state at 1.
    subst_max. find_rewrite.
    rewrite map_app. simpl.
    unfold fst, snd in *. repeat break_let.
    unfold recv_handler, serialize_res in *.
    repeat break_let. find_inversion.
    eapply ChordSemantics.Deliver_node; simpl; eauto.
    unfold revert_global_state. simpl.
    repeat rewrite map_app.
    rewrite revert_msg_send_revert_dst_msg.
    rewrite serialize_revert_dst_msgs.
    reflexivity.
  - unfold client_payload in *. break_exists. intuition.
    subst_max.
    eapply ChordSemantics.Input; eauto.
    unfold update_msgs_and_trace, ChordSemantics.update_msgs_and_trace, revert_global_state.
    simpl.
    rewrite map_app.
    simpl.
    rewrite serialize_revert_payload.
    reflexivity.
  - eapply ChordSemantics.Deliver_client; eauto.
    + simpl.
      repeat find_rewrite.
      rewrite map_app.
      reflexivity.
    + subst_max.
      unfold revert_msg. repeat break_let.
      reflexivity.
    + subst_max.
      unfold revert_global_state, update_msgs_and_trace, ChordSemantics.update_msgs_and_trace.
      simpl.
      repeat rewrite map_app.
      reflexivity.
Qed.
