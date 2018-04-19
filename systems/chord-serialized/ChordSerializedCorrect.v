Require Import List.

Require Import InfSeqExt.infseq.
Require Import InfSeqExt.map.
Require Import InfSeqExt.exteq.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Cheerios.Cheerios.

Require Import Chord.Chord.
Require Import Chord.ChordSerialized.
Require Import Chord.ChordSerializedSimulations.
Require Import Chord.ChordStabilization.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.
Require Import Chord.QueriesEventuallyStop.

(* useful definitions and lemmas *)

Definition serialize_occurrence (occ : ChordSemantics.occurrence) :=
  {| occ_gst := serialize_global_state (ChordSemantics.occ_gst occ);
     occ_label := (ChordSemantics.occ_label occ) |}.

Definition revert_occurrence (occ : ChordSerializedSemantics.occurrence) :=
  {| ChordSemantics.occ_gst := revert_global_state (ChordSerializedSemantics.occ_gst occ);
     ChordSemantics.occ_label := (ChordSerializedSemantics.occ_label occ) |}.

Definition revert_serialize_occurrence o :=
  serialize_occurrence (revert_occurrence o).

Inductive reachable_st_serialized : global_state -> Prop :=
  reachableInitS : forall gst,
    initial_st (revert_global_state gst) -> reachable_st_serialized gst
| reachableStepS : forall gst gst',
    reachable_st_serialized gst ->
    ChordSerializedSemantics.step_dynamic gst gst' ->
    reachable_st_serialized gst'.

Lemma revert_reachable : forall ex : infseq occurrence,
    reachable_st_serialized (occ_gst (infseq.hd ex)) ->
    reachable_st (ChordSemantics.occ_gst (infseq.hd (map revert_occurrence ex))).
Proof.
  intros.
  destruct ex.
  simpl in *.
  induction H.
  - constructor.
    assumption.
  - eapply reachableStep; eauto.
    apply step_dynamic_serialized_step_dynamic.
    assumption.
Qed.

Lemma revert_lb_execution : forall ex,
    lb_execution ex ->
    ChordSemantics.lb_execution (map revert_occurrence ex).
Proof.
  cofix.
  intros.
  do 2 (destruct ex; rewrite map_Cons).
  constructor; inv H.
  - apply serialized_labeled_step_labeled_step.
    assumption.
  - rewrite <- map_Cons.
    apply revert_lb_execution.
    assumption.
Qed.

(* rewrite definitions for stabilization property *)
Definition live_node gst h :=
  In h (nodes gst) /\
  ~ In h (failed_nodes gst) /\
  (exists st : data, sigma gst h = Some st /\ joined st = true).

Definition correct_succs (gst : global_state) (h : pointer) (st : data) : Prop :=
  forall s xs ys s',
    wf_ptr h ->
    succ_list st = xs ++ s :: ys ->
    ptr_between h s' s ->
    live_node gst (addr_of s') ->
    wf_ptr s' ->
    In s' xs.

Definition better_pred (gst : global_state) (h p p' : pointer) : Prop :=
  wf_ptr h /\
  wf_ptr p /\
  wf_ptr p' /\
  live_node gst (addr_of p') /\
  ptr_between p p' h.


Definition pred_correct (gst : global_state) (h : pointer) (p : option pointer) : Prop :=
  exists p0,
    p = Some p0 /\
    forall p',
      p' <> p0 ->
      live_node gst (addr_of p') ->
      wf_ptr p' ->
      better_pred gst h p' p0.

Definition ideal (gst : global_state) : Prop :=
  forall h st,
    live_node gst (addr_of h) ->
    wf_ptr h ->
    sigma gst (addr_of h) = Some st ->
    correct_succs gst h st /\
    length (succ_list st) = Chord.SUCC_LIST_LEN /\
    pred_correct gst h (pred st).


(* more helper lemmas *)
Lemma revert_live_node : forall gst h, live_node (serialize_global_state gst) (addr_of h) ->
                                  ConstrainedChord.live_node gst (addr_of h).
Proof.
  intuition.
Qed.

Lemma preserves_ideal_gst : forall gst,
    ChordStabilization.ideal gst -> ideal (serialize_global_state gst).
Proof.
  unfold ChordStabilization.ideal, ideal.
  intros.
  apply H; assumption.
Qed.

Lemma serialize_ideal : forall occ,
    ChordStabilization.ideal (ChordSemantics.occ_gst occ) ->
    ideal (occ_gst (serialize_occurrence occ)).
Proof.
  destruct occ.
  simpl.
  apply preserves_ideal_gst.
Qed.

Lemma serialize_continuously_ideal : forall ex : infseq ChordSemantics.occurrence,
    continuously (now (fun o => ChordStabilization.ideal (ChordSemantics.occ_gst o))) ex ->
    continuously (now (fun o => ideal (occ_gst o)))
                 (map serialize_occurrence ex).
Proof.
  intros.
  eapply continuously_map; eauto.
  intros.
  destruct s. simpl in *.
  apply serialize_ideal.
  assumption.
Qed.

Lemma ideal_extensional : extensional (continuously (now (fun o => ideal (occ_gst o)))).
Proof.
  apply extensional_continuously.
  unfold extensional, now.
  intros.
  do 2 break_match.
  find_apply_lem_hyp exteq_inversion.
  break_and. subst_max.
  assumption.
Qed.

Definition blocked_by (gst : global_state) (s h : addr) : Prop :=
  In h (nodes gst) /\
  In s (nodes gst) /\
  exists st__h st__s dstp q m,
    sigma gst h = Some st__h /\
    sigma gst s = Some st__s /\
    cur_request st__h = Some (dstp, q, m) /\
    addr_of dstp = s /\
    In (h, m) (delayed_queries st__s).

Definition circular_wait occ :=
  has_cycle (blocked_by (occ_gst occ)).

Lemma revert_circular_wait : forall ex,
    always (~_ now circular_wait) ex ->
    always (~_ now QueriesEventuallyStop.circular_wait) (map revert_occurrence ex).
Proof.
  apply always_map.
  intros.
  eapply not_tl_map; eauto.
  unfold now. destruct s0.
  rewrite map_Cons.
  unfold QueriesEventuallyStop.circular_wait, circular_wait,
  QueriesEventuallyStop.blocked_by, blocked_by, has_cycle.
  intros. break_exists.
  eauto.
Qed.

Lemma revert_serialize_msgs : forall gst,
    serialize_global_state (revert_global_state gst) = gst ->
    List.map serialize_msg (List.map revert_msg (msgs gst)) = msgs gst.
Proof.
  unfold serialize_global_state, revert_global_state. simpl.
  intros.
  find_reverse_rewrite.
  simpl.
  rewrite serialize_revert_msgs.
  reflexivity.
Qed.

Lemma revert_serialize_trace : forall gst,
    serialize_global_state (revert_global_state gst) = gst ->
    List.map serialize_event
             (List.map revert_event (trace gst)) = trace gst.
Proof.
  destruct gst.
  unfold serialize_global_state, revert_global_state. simpl.
  intros.
  find_inversion.
  rewrite serialize_revert_events.
  reflexivity.
Qed.

Lemma serialize_send_revert_serialize : forall l h,
  List.map serialize_event
    (List.map revert_event
       (List.map e_send (List.map serialize_msg (List.map (ChordSemantics.send h) l)))) =
  List.map e_send (List.map serialize_msg (List.map (ChordSemantics.send h) l)).
Proof.
  induction l.
  - reflexivity.
  - intros.
    simpl. repeat break_let.
    unfold revert_msg, revert_payload.
    rewrite serialize_deserialize_top_id.
    rewrite IHl.
    reflexivity.
Qed.

Lemma revert_serialize_start_handler_msgs : forall h k d l0 l,
    start_handler h (k :: nil) = (d, l0, l) ->
    List.map serialize_msg (List.map revert_msg (List.map (send h) l0))
    = List.map (send h) l0.
Proof.
  unfold start_handler.
  intros. repeat break_let.
  find_inversion.
  rewrite map_send_serialize.
  rewrite serialize_revert_msgs.
  reflexivity.
Qed.

Lemma revert_serialize_start_handler_events : forall h k d l0 l,
    start_handler h (k :: nil) = (d, l0, l) ->
    List.map serialize_event
             (List.map revert_event (List.map e_send (List.map (send h) l0))) =
    List.map e_send (List.map (send h) l0).
Proof.
  unfold start_handler.
  intros. repeat break_let.
  find_inversion.
  rewrite map_send_serialize.
  rewrite serialize_send_revert_serialize.
  reflexivity.
Qed.

Lemma revert_serialize_timeout_handler : forall h st t st' ms newts clearedts,
      timeout_handler h st t = (st', ms, newts, clearedts) ->
      List.map serialize_msg (List.map revert_msg (List.map (send h) ms)) = List.map (send h) ms.
Proof.
  unfold timeout_handler, serialize_res.
  intros.
  repeat break_let.
  find_inversion.
  rewrite map_send_serialize.
  rewrite serialize_revert_msgs.
  reflexivity.
Qed.

Lemma revert_serialize_recv_handler : forall a0 a1 d p st ms newts clearedts,
      recv_handler a0 a1 d p = (st, ms, newts, clearedts) ->
      List.map serialize_msg (List.map revert_msg (List.map (send a1) ms)) = List.map (send a1) ms.
Proof.
  unfold recv_handler, serialize_res.
  intros.
  repeat break_let.
  find_inversion.
  rewrite map_send_serialize.
  rewrite serialize_revert_msgs.
  reflexivity.
Qed.

Lemma revert_serialize_msgs_l_aux : forall xs m ys,
    List.map serialize_msg (List.map revert_msg (xs ++ m :: ys)) = xs ++ m :: ys ->
    List.map serialize_msg (List.map revert_msg xs) = xs.
Proof.
  induction xs.
  - reflexivity.
  - intros. simpl.
    rewrite (IHxs m ys); inversion H.
    + repeat find_rewrite.
      reflexivity.
    + simpl in *.
      repeat find_rewrite.
      reflexivity.
Qed.

Lemma revert_serialize_msgs_mid_aux : forall xs m ys,
    List.map serialize_msg (List.map revert_msg (xs ++ m :: ys)) = xs ++ m :: ys ->
    serialize_msg (revert_msg m) = m.
Proof.
  induction xs.
  - simpl. intros.
    inversion H.
    repeat find_rewrite.
    reflexivity.
  - intros. simpl.
    rewrite (IHxs m ys); inversion H.
    + repeat find_rewrite.
      reflexivity.
    + simpl in *.
      repeat find_rewrite.
      reflexivity.
Qed.

Lemma revert_serialize_msgs_r_aux : forall xs m ys,
    List.map serialize_msg (List.map revert_msg (xs ++ m :: ys)) = xs ++ m :: ys ->
    List.map serialize_msg (List.map revert_msg ys) = ys.
Proof.
  induction xs.
  - simpl. intros.
    inversion H.
    repeat find_rewrite.
    reflexivity.
  - intros. simpl.
    rewrite (IHxs m ys); inversion H.
    + repeat find_rewrite.
      reflexivity.
    + simpl in *.
      repeat find_rewrite.
      reflexivity.
Qed.

Lemma revert_serialize_msgs_l : forall gst xs m ys,
  serialize_global_state (revert_global_state gst) = gst ->
      msgs gst = xs ++ m :: ys ->
      List.map serialize_msg (List.map revert_msg xs) = xs.
Proof.
  unfold serialize_global_state, revert_global_state. simpl in *.
  intros.
  destruct gst. simpl in *.
  find_inversion.
  erewrite revert_serialize_msgs_l_aux; eauto.
Qed.

Lemma revert_serialize_msgs_mid : forall gst xs m ys,
  serialize_global_state (revert_global_state gst) = gst ->
      msgs gst = xs ++ m :: ys ->
      serialize_msg (revert_msg m) = m.
Proof.
  unfold serialize_global_state, revert_global_state. simpl in *.
  intros.
  destruct gst. simpl in *.
  find_inversion.
  erewrite revert_serialize_msgs_mid_aux; eauto.
Qed.

Lemma revert_serialize_msgs_r : forall gst xs m ys,
  serialize_global_state (revert_global_state gst) = gst ->
      msgs gst = xs ++ m :: ys ->
      List.map serialize_msg (List.map revert_msg ys) = ys.
Proof.
  unfold serialize_global_state, revert_global_state. simpl in *.
  intros.
  destruct gst. simpl in *.
  find_inversion.
  erewrite revert_serialize_msgs_r_aux; eauto.
Qed.

Lemma reachable_revert_serialize_global_state : forall gst,
    reachable_st_serialized gst ->
    serialize_global_state (revert_global_state gst) = gst.
Proof.
  intros.
  induction H.
  - unfold initial_st in H.
    intuition.
    unfold serialize_global_state, revert_global_state.
    destruct gst. simpl in *.
    do 2 find_apply_lem_hyp map_eq_nil.
    subst_max.
    reflexivity.
  - inv_prop step_dynamic;
      subst_max.
    + unfold update_for_start. repeat break_let.
      unfold serialize_global_state, revert_global_state. simpl.
      repeat rewrite map_app.
      erewrite revert_serialize_start_handler_msgs;
        eauto.
      erewrite revert_serialize_start_handler_events;
        eauto.
      rewrite revert_serialize_msgs; try assumption.
      rewrite revert_serialize_trace; try assumption.
      reflexivity.
    + unfold fail_node.
      unfold serialize_global_state, revert_global_state. simpl.
      rewrite revert_serialize_msgs; try assumption.
      rewrite revert_serialize_trace; try assumption.
      reflexivity.
    + unfold apply_handler_result, serialize_global_state, revert_global_state.
      simpl.
      repeat rewrite map_app.
      erewrite revert_serialize_timeout_handler;
        eauto.
      rewrite revert_serialize_msgs; try assumption.
      rewrite revert_serialize_trace; try assumption.
      reflexivity.
    + unfold apply_handler_result, serialize_global_state, revert_global_state.
      simpl.
      repeat rewrite map_app.
      rewrite (revert_serialize_msgs_l gst xs m ys) at 1; try assumption.
      rewrite (revert_serialize_msgs_r gst xs m ys) at 1; try assumption.
      erewrite revert_serialize_trace; eauto.
      simpl.
      erewrite revert_serialize_msgs_mid; eauto.
      destruct m. destruct p. simpl in *.
      erewrite revert_serialize_recv_handler; eauto.
    + unfold update_msgs_and_trace, serialize_global_state, revert_global_state.
      simpl.
      repeat rewrite map_app.
      erewrite revert_serialize_msgs; eauto.
      erewrite revert_serialize_trace; eauto.
      simpl.
      unfold client_payload in *. break_exists. intuition.
      unfold revert_payload.
      match goal with
      | H : serialize_top _ = _ |- _ => rewrite <- H
      end.
      rewrite serialize_deserialize_top_id.
      reflexivity.
    + unfold update_msgs_and_trace, serialize_global_state, revert_global_state.
      simpl.
      repeat rewrite map_app. simpl.
      erewrite revert_serialize_msgs_l; eauto.
      erewrite revert_serialize_msgs_mid; eauto.
      erewrite revert_serialize_msgs_r; eauto.
      erewrite revert_serialize_trace; eauto.
Qed.

Lemma revert_serialize_exteq : forall ex,
    reachable_st_serialized (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    exteq (map serialize_occurrence (map revert_occurrence ex)) ex.
Proof.
  cofix.
  intros.
  destruct ex. do 2 rewrite map_Cons.
  unfold serialize_occurrence, revert_occurrence. simpl.
  erewrite reachable_revert_serialize_global_state; eauto.
  destruct o.
  constructor.
  apply revert_serialize_exteq.
  - destruct ex. simpl in *.
    inv_prop lb_execution.
    eapply reachableStepS; eauto.
    eapply labeled_step_is_unlabeled_step; eauto.
  - eapply lb_execution_invar; eauto.
Qed.

Lemma reachable_enabled' : forall l o,
    ChordSemantics.l_enabled l o -> l_enabled l (serialize_occurrence o).
Proof.
  unfold ChordSemantics.l_enabled, ChordSemantics.enabled, l_enabled, enabled.
  intros.
  break_exists.
  exists (serialize_global_state x).
  apply labeled_step_serialized_labeled_step.
  assumption.
Qed.

Lemma lb_execution_enabled : forall ex l,
    reachable_st_serialized (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    eventually (now (ChordSemantics.l_enabled l)) (map revert_occurrence ex) ->
    eventually (now (l_enabled l)) ex.
Proof.
  intros.
  assert (G : extensional (eventually (now (l_enabled l)))).
  { apply extensional_eventually.
    unfold extensional.
    intros.
    destruct s1, s2.
    inv_prop exteq.
     subst_max.
    unfold now in *. repeat break_match.
    assumption. }
  unfold extensional in *.
  apply (G (map serialize_occurrence (map revert_occurrence ex))).
  - eapply revert_serialize_exteq; eauto.
  - eapply eventually_map; eauto.
    intros.
    destruct s. simpl in *.
    apply reachable_enabled'.
    assumption.
Qed.

Lemma revert_always_eventually_enabled : forall ex l,
    reachable_st_serialized (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    always (eventually (now (ChordSemantics.l_enabled l))) (map revert_occurrence ex) ->
    always (eventually (now (l_enabled l))) ex.
Proof.
  cofix.
  constructor.
  - inv_prop always.
    apply lb_execution_enabled; assumption.
  - destruct ex. rewrite map_Cons in *.
    apply revert_always_eventually_enabled.
    + simpl.
      destruct ex.
      simpl in *.
      inv_prop lb_execution. simpl in *.
      eapply reachableStepS; eauto.
      * eapply labeled_step_is_unlabeled_step. eauto.
      * eapply lb_execution_invar. eauto.
    + inv_prop always.
      assumption.
Qed.

Lemma revert_strong_local_fairness : forall ex,
    reachable_st_serialized (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    strong_local_fairness ex ->
    ChordSemantics.strong_local_fairness (map revert_occurrence ex).
Proof.
  unfold strong_local_fairness, ChordSemantics.strong_local_fairness.
  intros.
  assert (inf_occurred l ex).
  - match goal with
    | H : context[inf_occurred] |- _ => apply H
    end.
    unfold inf_enabled, inf_often.
    unfold ChordSemantics.inf_enabled, inf_often in *.
    apply revert_always_eventually_enabled;
      assumption.
  - unfold ChordSemantics.inf_occurred, inf_often.
    unfold inf_occurred, inf_often in *.
    eapply always_map; eauto.
    intros.
    eapply eventually_map; eauto.
    unfold occurred, ChordSemantics.occurred.
    destruct s0. rewrite map_Cons.
    tauto.
Qed.

(* top-level correctness property *)
Theorem chord_serialized_stabilization :
  forall ex : infseq.infseq occurrence,
    reachable_st_serialized (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    continuously (now (fun o => ideal (occ_gst o))) ex.
Proof.
  intros.
  match goal with
  | _ : _ |- continuously ?P _ =>
    assert (G : extensional (continuously P)) by (exact ideal_extensional)
  end.
  unfold extensional in G.
  apply (G (map serialize_occurrence (map revert_occurrence ex))).
  - eapply revert_serialize_exteq; eauto.
  - apply serialize_continuously_ideal.
    apply ChordStabilization.chord_stabilization.
    + apply revert_reachable.
      assumption.
    + apply revert_lb_execution.
      assumption.
    + apply revert_strong_local_fairness;
        assumption.
    + apply revert_circular_wait. assumption.
Qed.
