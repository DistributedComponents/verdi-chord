Require Import List.

Require Import InfSeqExt.infseq.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Cheerios.Cheerios.

Require Import Chord.Chord.
Require Import Chord.ChordSerialized.
Require Import Chord.QueriesEventuallyStop.
Require Import Chord.ChordStabilization.
Require Import Chord.SystemReachable.

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

Definition serialize_revert_event : forall e,
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

Definition serialize_revert_events : forall l,
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

Definition serialize_revert_global_state : forall gst,
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

Definition labeled_step_serialized_labeled_step: forall gst l gst',
    ChordSemantics.labeled_step_dynamic gst l gst' ->
    ChordSerializedSemantics.labeled_step_dynamic (serialize_global_state gst)
                                                  l
                                                  (serialize_global_state gst').
Proof.
  intros.
  inversion H.
  - apply (LTimeout (serialize_global_state gst) (serialize_global_state gst')
                    h st t l st' (map serialize_dst_msg ms) newts clearedts);
      try assumption.
    + unfold timeout_handler_l.
      unfold serialize_res.
      repeat break_let.
      find_inversion.
      reflexivity.
    + match goal with
      | H : gst' = _ |- _ => rewrite H
      end.
      unfold serialize_global_state.
      simpl.
      rewrite map_app.
      rewrite map_send_serialize.
      rewrite map_app.
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
      match goal with
      | H : ChordSemantics.msgs gst = _ |- _ => rewrite H
      end.
      rewrite map_app.
      reflexivity.
    + destruct m.
      match goal with
      | H : _ = fst (snd _) |- _ => rewrite H
      end.
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
      simpl in H5.
      rewrite H5 in Heqp1.
      find_inversion.
      reflexivity.
    + match goal with
      | H : gst' = _ |- _ => rewrite H
      end.
      unfold serialize_global_state.
      simpl.
      repeat rewrite map_app.
      rewrite map_send_serialize.
      reflexivity.
  - apply (LInput (serialize_global_state gst) (serialize_global_state gst')
                  h (serialize_top (serialize i)) to (serialize_msg m) l);
      try assumption.
    + unfold client_payload, serialized_client_payload.
      exists i.
      split.
      * apply serialize_deserialize_top_id.
      * assumption.
    + match goal with
      | H : m = _ |- _ => rewrite H
      end.
      unfold ChordSemantics.send, send, serialize_msg.
      reflexivity.
    + match goal with
      | H : l = _ |- _ => rewrite H
      end.
      unfold label_input.
      unfold revert_payload.
      rewrite serialize_deserialize_top_id.
      reflexivity.
    + match goal with
      | H : gst' = _ |- _ => rewrite H
      end.
      unfold serialize_global_state, update_msgs_and_trace.
      simpl.
      rewrite map_app.
      simpl.
      reflexivity.
  - apply (LDeliver_client (serialize_global_state gst) (serialize_global_state gst')
                           h (map serialize_msg xs) (serialize_msg m) (map serialize_msg ys)
                           l);
      try assumption.
    + simpl.
      match goal with
      | H : ChordSemantics.msgs gst = _ |- _ => rewrite H
      end.
      rewrite map_app.
      reflexivity.
    + destruct m.
      simpl.
      break_let.
      simpl in *.
      assumption.
    + destruct m.
      simpl.
      repeat break_let.
      simpl in *.
      unfold label_output.
      rewrite serialize_revert_payload.
      assumption.
    + match goal with
      | H : gst' = _ |- _ => rewrite H
      end.
      unfold serialize_global_state, update_msgs_and_trace.
      simpl.
      do 2 rewrite map_app.
      reflexivity.
Qed.

Definition serialized_labeled_step_labeled_step: forall gst l gst',
    ChordSerializedSemantics.labeled_step_dynamic gst l gst' ->
    ChordSemantics.labeled_step_dynamic (revert_global_state gst)
                                        l
                                        (revert_global_state gst').
Proof.
  intros.
  inversion H.
  - apply (ChordSemantics.LTimeout (revert_global_state gst) (revert_global_state gst')
                                   h st t l st' (map revert_dst_msg ms) newts clearedts);
      try assumption.
    + unfold timeout_handler_l in *.
      unfold serialize_res in *.
      repeat break_let.
      find_inversion.
      rewrite serialize_revert_dst_msgs.
      reflexivity.
    + match goal with
      | H : gst' = _ |- _ => rewrite H
      end.
      unfold revert_global_state.
      simpl.
      repeat rewrite map_app.
      unfold update at 1.
      unfold update at 2.
      rewrite revert_msg_send_revert_dst_msg.
      reflexivity.
  - apply (ChordSemantics.LDeliver_node
             (revert_global_state gst) (revert_global_state gst')
             (revert_msg m) h d
             (map revert_msg xs) (map revert_msg ys) (map revert_dst_msg ms)
             l st newts clearedts);
      try assumption.
    + unfold revert_global_state. simpl.
      match goal with
      | H : ?x = _ |- context[?x] => rewrite H
      end.
      rewrite map_app. reflexivity.
    + match goal with
      | H : ?x = _ |- ?x = _ => rewrite H
      end.
      unfold revert_msg. repeat break_let.
      reflexivity.
    + unfold revert_msg, recv_handler_l, serialize_res in *.
      repeat break_let. simpl in *.
      match goal with
      | H : context[ChordSerializable.recv_handler_l] |- _ => rewrite H
      end.
      find_inversion.
      rewrite serialize_revert_dst_msgs.
      reflexivity.
    + match goal with
      | H : ?x = _ |- context[revert_global_state ?x] => rewrite H
      end.
      unfold revert_global_state. simpl.
      repeat rewrite map_app.
      unfold update at 1.
      unfold update at 2.
      rewrite revert_msg_send_revert_dst_msg.
      reflexivity.
  - apply (ChordSemantics.LInput
             (revert_global_state gst) (revert_global_state gst')
             h (revert_payload i) to (revert_msg m) l);
      try assumption.
    + unfold client_payload, serialized_client_payload in *.
      break_exists. break_and.
      unfold revert_payload.
      match goal with
      | H : context[deserialize] |- _ => rewrite H
      end.
      assumption.
    + match goal with
      | H : ?x = _ |- revert_msg ?x = _ => rewrite H
      end.
      unfold revert_msg, send, ChordSemantics.send.
      reflexivity.
    + match goal with
      | H : ?x = _ |- context[revert_global_state ?x] => rewrite H
      end.
      unfold revert_global_state, ChordSemantics.update_msgs_and_trace. simpl.
      repeat rewrite map_app.
      reflexivity.
  - apply (ChordSemantics.LDeliver_client
             (revert_global_state gst) (revert_global_state gst')
             h (map revert_msg xs) (revert_msg m) (map revert_msg ys) l);
      try assumption.
    + unfold revert_global_state. simpl.
      match goal with
      | H : ?x = _ |- context[?x] => rewrite H
      end.
      rewrite map_app. reflexivity.
    + match goal with
      | H : ?x = _ |- context[?x] => rewrite H
      end.
      unfold revert_msg. repeat break_let. reflexivity.
    + unfold label_output, revert_msg in *. repeat break_let.
      simpl in *. assumption.
    + match goal with
      | H : ?x = _ |- revert_global_state ?x = _ => rewrite H
      end.
      unfold revert_global_state, update_msgs_and_trace. simpl.
      repeat rewrite map_app.
      reflexivity.
Qed.

Lemma step_dynamic_step_dynamic_serialized : forall gst gst',
    ChordSemantics.step_dynamic gst gst' ->
    step_dynamic (serialize_global_state gst) (serialize_global_state gst').
Admitted.

Lemma step_dynamic_serialized_step_dynamic : forall gst gst',
    step_dynamic gst gst' ->
    ChordSemantics.step_dynamic (revert_global_state gst) (revert_global_state gst').
Proof.
  intros.
  induction H.
  - apply (ChordSemantics.Start h
                                (revert_global_state gst) (revert_global_state gst')
                                k); try assumption.
    + unfold update_for_start in *.
      unfold ChordSemantics.update_for_start, revert_global_state.
      match goal with
      | H : gst' = _ |- _ => rewrite H
      end.
      simpl.
      repeat break_let.
      unfold update at 1.
      unfold update at 2.
      unfold ChordSemantics.send.
      repeat rewrite map_app.
      unfold send.
      simpl.
      rewrite serialize_revert_payload.
      reflexivity.
  - apply (ChordSemantics.Fail h (revert_global_state gst) (revert_global_state gst'));
      try assumption.
    match goal with
    | H : gst' = _ |- _ => rewrite H
    end.
    unfold revert_global_state, fail_node. simpl.
    reflexivity.
  - apply (ChordSemantics.Timeout
             (revert_global_state gst) (revert_global_state gst')
             h st t  st' (List.map revert_dst_msg ms) newts clearedts);
      try assumption.
    + unfold timeout_handler, serialize_res in *.
      repeat break_let. find_inversion.
      rewrite serialize_revert_dst_msgs.
      reflexivity.
    + match goal with
      | H : gst' = _ |- _ => rewrite H
      end.
      unfold revert_global_state, apply_handler_result. simpl.
      unfold update at 1. unfold update at 2.
      repeat rewrite map_app.
      rewrite revert_msg_send_revert_dst_msg.
      reflexivity.
  - apply (ChordSemantics.Deliver_node
             (revert_global_state gst) (revert_global_state gst')
             (revert_msg m) h d
             (List.map revert_msg xs) (List.map revert_msg ys) (List.map revert_dst_msg ms)
             st newts clearedts); try assumption.
    + simpl.
      match goal with
      | H : msgs _ = _ |- _ => rewrite H
      end.
      rewrite map_app.
      reflexivity.
    + match goal with
      | H : ?x = _ |- ?x = _ => rewrite H
      end.
      unfold revert_msg.
      repeat break_let.
      reflexivity.
    + unfold recv_handler, serialize_res in *.
      unfold revert_msg. repeat break_let. simpl in *.
      find_inversion.
      match goal with
      | H : ?x = _ |- ?x = _ => rewrite H
      end.
      rewrite serialize_revert_dst_msgs.
      reflexivity.
    + match goal with
      | H : gst' = _ |- _ => rewrite H
      end.
      unfold apply_handler_result in *. unfold revert_global_state. simpl.
      unfold update at 1. unfold update at 2.
      repeat rewrite map_app.
      rewrite revert_msg_send_revert_dst_msg.
      reflexivity.
  - apply (ChordSemantics.Input
             (revert_global_state gst) (revert_global_state gst')
             h (revert_payload i) to (revert_msg m));
      try assumption.
    + unfold client_payload, serialized_client_payload in *.
      break_exists. break_and.
      unfold revert_payload.
      match goal with
      | H : deserialize_top _ _ = _ |- _ => rewrite H
      end.
      assumption.
    + match goal with
      | H : ?x = _ |- revert_msg ?x = _ => rewrite H
      end.
      unfold revert_msg, send, ChordSemantics.send.
      reflexivity.
    + match goal with
      | H : gst' = _ |- _ => rewrite H
      end.
      unfold update_msgs_and_trace, ChordSemantics.update_msgs_and_trace.
      unfold revert_global_state. simpl.
      rewrite map_app.
      reflexivity.
  - apply (ChordSemantics.Deliver_client
             (revert_global_state gst) (revert_global_state gst') h
             (List.map revert_msg xs) (revert_msg m) (List.map revert_msg ys));
      try assumption.
    + simpl.
      match goal with
      | H : msgs gst = _ |- _ => rewrite H
      end.
      rewrite map_app. reflexivity.
    + match goal with
      | H : h = _ |- _ => rewrite H
      end.
      unfold revert_msg. repeat break_match.
      reflexivity.
    + match goal with
      | H : gst' = _ |- _ => rewrite H
      end.
      unfold revert_global_state, update_msgs_and_trace, ChordSemantics.update_msgs_and_trace.
      simpl.
      repeat rewrite map_app.
      reflexivity.
Qed.