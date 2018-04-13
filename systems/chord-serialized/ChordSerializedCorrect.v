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

Require Import FunctionalExtensionality.


(* liveness *)
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
  - apply (reachableStep (revert_global_state gst)).
    + assumption.
    + apply step_dynamic_serialized_step_dynamic.
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


Definition deserialize_msg_hard (m : msg) :=
  match m with
  | (src, (dst, m)) => match @deserialize_top ChordSerializable.payload (@deserialize ChordSerializable.payload _) m with
                      | None => None
                      | Some m' => Some (src, (dst, m'))
                      end
  end.

Definition valid_msg' := fun m => exists m', deserialize_msg_hard m = Some m'.

Definition valid_msg := fun m => exists m', serialize_msg m' = m.

Lemma Forall_app : forall {A} (l1 l2 : list A) P,
    Forall P l2 -> Forall P l1 -> Forall P (l1 ++ l2).
Proof.
  induction l1.
  - intros.
    assumption.
  - intros.
    simpl.
    constructor;
      inversion H0.
    + assumption.
    + apply IHl1.
      * assumption.
      * assumption.
Qed.

Lemma Forall_app_inv_l : forall {A} (l1 l2 : list A) P,
    Forall P (l1 ++ l2) -> Forall P l1.
Proof.
  induction l1.
  - constructor.
  - simpl. intros.
    constructor;
      inversion H.
    + assumption.
    + apply (IHl1 l2).
      assumption.
Qed.

Lemma Forall_app_inv_r : forall {A} (l1 l2 : list A) P,
    Forall P (l1 ++ l2) -> Forall P l2.
Proof.
  induction l1.
  - intros.
    assumption.
  - simpl. intros.
    apply IHl1.
    inversion H.
    assumption.
Qed.

Lemma Forall_remove_mid : forall {A : Type} (l1 : list A) a l2 P,
    Forall P (l1 ++ a :: l2) -> Forall P (l1 ++ l2).
Proof.
  induction l1.
  - simpl. intros.
    inversion H.
    assumption.
  - simpl.
    intros.
    inversion H.
    constructor.
    + assumption.
    + match goal with
      | H : Forall P (l1 ++ ?x :: l2) |- _ => apply (IHl1 x)
      end.
      assumption.
Qed.

Lemma Forall_map_serialize : forall msgs,
    Forall valid_msg (List.map serialize_msg msgs).
Proof.
  intros.
  induction msgs0.
  - constructor.
  - rewrite List.map_cons.
    constructor.
    + unfold valid_msg.
      eauto.
    + assumption.
Qed.


Lemma revert_serialize_compose_exteq : forall ex,
    exteq (map serialize_occurrence (map revert_occurrence ex))
          (map revert_serialize_occurrence ex).
Proof.
  cofix.
  intros.
  destruct ex.
  do 3 rewrite map_Cons.
  constructor.
  intuition.
Qed.

(* Sanity check: redefine ideal for our system *)

(* helper functions *)
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

Lemma revert_live_node : forall gst h, live_node (serialize_global_state gst) (addr_of h) ->
                                  ConstrainedChord.live_node gst (addr_of h).
Proof.
  intuition.
Qed.

Lemma revert_serialize_live_node : forall o h,
    live_node (occ_gst o) (addr_of h) ->
    live_node (occ_gst (revert_serialize_occurrence o)) (addr_of h).
Proof.
  intuition.
Qed.

Lemma serialize_correct_succs : forall gst h st,
    ChordCorrectPhaseThree.correct_succs gst h st ->
    correct_succs (serialize_global_state gst) h st.
Proof.
  unfold correct_succs, ChordCorrectPhaseThree.correct_succs.
  intros.
  apply (H s xs ys);
    assumption.
Qed.

Lemma serialize_pred_correct : forall gst h st,
    ChordCorrectPhaseTwo.pred_correct gst h (pred st) ->
    pred_correct (serialize_global_state gst) h (pred st).
Proof.
  unfold ChordCorrectPhaseTwo.pred_correct, pred_correct.
  unfold ChordCorrectPhaseTwo.better_pred, better_pred.
  intros.
  break_exists. intuition.
  exists x.
  split.
  - assumption.
  - intros.
    specialize H1 with p'. apply H1 in H.
    intuition; try assumption.
    apply revert_live_node. assumption.
    assumption.
Qed.

Lemma revert_serialize_pred_correct : forall o h st,
    sigma (occ_gst (revert_serialize_occurrence o)) (addr_of h) = Some st ->
    sigma (occ_gst o) (addr_of h) = Some st.
Proof.
  -intuition.
Qed.

Lemma preserves_ideal_gst : forall gst,
    ChordStabilization.ideal gst -> ideal (serialize_global_state gst).
Proof.
  unfold ChordStabilization.ideal.
  intros.
  unfold ideal.
  intros.
  specialize H with h st.
  match goal with
  | H : live_node _ _ |- _ => apply revert_live_node in H
  end.
  apply (H H0 H1 H2).
Qed.

Lemma serialize_ideal : forall occ,
    ChordStabilization.ideal (ChordSemantics.occ_gst occ) ->
    ideal (occ_gst (serialize_occurrence occ)).
Proof.
  destruct occ.
  simpl.
  apply preserves_ideal_gst.
Qed.

Lemma serialize_ideal_seq : forall ex,
    (now (fun o => ChordStabilization.ideal (ChordSemantics.occ_gst o))) ex ->
    (now (fun o => ideal (occ_gst o))) (map serialize_occurrence ex).
Proof.
  unfold now. intros.
  destruct ex. rewrite map_Cons.
  apply serialize_ideal. assumption.
Qed.

Lemma serialize_continuously_now : forall (ex : infseq ChordSemantics.occurrence)
                                     (P : ChordSemantics.occurrence -> Prop)
                                     (P' : occurrence -> Prop),
    (forall occ, P occ -> P' (serialize_occurrence occ)) ->
    (forall s, now P s -> now P' (map serialize_occurrence s)) ->
    continuously (now P) ex ->
    continuously (now P') (map serialize_occurrence ex).
Proof.
  intros.
  apply continuously_map with (P := (now P));
    assumption.
Qed.

Theorem serialize_continuously_ideal : forall ex : infseq ChordSemantics.occurrence,
    continuously (now (fun o => ChordStabilization.ideal (ChordSemantics.occ_gst o))) ex ->
    continuously (now (fun o => ideal (occ_gst o)))
                 (map serialize_occurrence ex).
Proof.
  intros.
  match goal with
  | H : continuously (now ?P) _ |- _ => apply (serialize_continuously_now _ P)
  end.
  - apply serialize_ideal.
  - apply serialize_ideal_seq.
  - assumption.
Qed.

Lemma ideal_extensional : extensional (continuously (now (fun o => ideal (occ_gst o)))).
Proof.
  apply extensional_continuously.
  unfold extensional, now.
  intros.
  do 2 break_match.
  apply exteq_inversion in H.
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
  apply (@always_map _ _ _ (~_ now circular_wait)).
  intros.
  apply (@not_tl_map _ _ _ (now circular_wait)).
  - unfold now. destruct s0.
    rewrite map_Cons.
    unfold QueriesEventuallyStop.circular_wait, circular_wait.
    unfold QueriesEventuallyStop.blocked_by, blocked_by, has_cycle.
    intros. break_exists.
    eauto.
  - assumption.
Qed.

Definition now_ideal := now (fun o => ideal (occ_gst o)).

Lemma a : forall ex,
    continuously now_ideal
                 (map revert_serialize_occurrence ex) ->
    continuously now_ideal ex.
Proof.
  intros.
  assert (extensional now_ideal).
  { unfold extensional, now_ideal, now.
    destruct s1, s2. simpl.
    intros.
    match goal with
    | H : exteq _ _ |- _ => inversion H
    end.
    subst_max. assumption.
  }
  apply (@continuously_map_conv _ _ (revert_serialize_occurrence) _ now_ideal).
  - assumption.
  - assumption.
  - destruct s.
    unfold now_ideal, now.
    rewrite map_Cons.
    unfold ideal. intros.
    assert (correct_succs (occ_gst (revert_serialize_occurrence o)) h st /\
            length (succ_list st) = SUCC_LIST_LEN /\
            pred_correct (occ_gst (revert_serialize_occurrence o)) h (pred st)).
    {
      apply H1;
        intuition.
    }
    intuition.
  - assumption.
Qed.

Lemma revert_serialize_update_for_start : forall gst h k,
serialize_global_state (revert_global_state gst) = gst  ->
    List.map serialize_msg
            (List.map revert_msg
                      (ChordSerializedSystem.msgs (update_for_start gst h (start_handler h (k :: nil)))))
    = ChordSerializedSystem.msgs (update_for_start gst h (start_handler h (k :: nil))).
  intros.
  destruct gst.
  unfold serialize_global_state, revert_global_state in *. simpl in *.
  unfold revert_payload.
  rewrite serialize_deserialize_top_id.
  find_inversion.
  unfold send.
  do 2 rewrite H1.
  reflexivity.
Qed.



Lemma revert_serialize_msgs : forall gst,
    serialize_global_state (revert_global_state gst) = gst ->
    List.map serialize_msg (List.map revert_msg (msgs gst)) = msgs gst.
Proof.
  unfold serialize_global_state, revert_global_state. simpl.
  intros.
  destruct gst. simpl in *.
  symmetry in H.
  find_inversion.
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
    unfold serialize_msg at 1.
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
    do 2 match goal with
         | H : List.map _ _ = nil |- _ => apply map_eq_nil in H;
                                          rewrite H
         end.
    reflexivity.
  - match goal with
    | H : step_dynamic _ _ |- _ => inversion H
    end;
      subst_max.
(*
      destruct gst';
      simpl.
     *)
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
    + unfold apply_handler_result.
      simpl.
    + admit.
    + admit.
    + admit.
Admitted.

Lemma reachable_enabled : forall o l x,
    reachable_st_serialized (occ_gst o) ->
    ChordSemantics.labeled_step_dynamic (ChordSemantics.occ_gst (revert_occurrence o)) l x ->
    exists gst' : global_state, labeled_step_dynamic (occ_gst o) l gst'.
Proof.
  intros.
  apply labeled_step_serialized_labeled_step in H0.
  destruct o.
  unfold revert_occurrence in H0. simpl in *.
  rewrite reachable_revert_serialize_global_state in H0.
  - eexists. eauto.
  - assumption.
Qed.

Lemma lb_execution_enabled : forall ex l,
    reachable_st_serialized (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    eventually (now (ChordSemantics.l_enabled l)) (map revert_occurrence ex) ->
    eventually (now (l_enabled l)) ex.
Proof.
  intros.
  remember (map revert_occurrence ex) as ex'.
  revert Heqex'.
  match goal with
  | H : eventually _ _ |- _ => induction H
  end.
  - intros.
    constructor.
    destruct ex.
    subst_max. simpl in *.
    unfold ChordSemantics.l_enabled, ChordSemantics.enabled, l_enabled, enabled in *.
    break_exists.
    eapply reachable_enabled;
      eauto.
  - intros.
    apply IHeventually.
    admit.
Admitted.

Lemma revert_always_eventually_enabled : forall ex l,
    reachable_st_serialized (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    always (eventually (now (ChordSemantics.l_enabled l))) (map revert_occurrence ex) ->
    always (eventually (now (l_enabled l))) ex.
Proof.
  cofix.
  constructor.
  - match goal with
    | H : always _ _ |- _ => inversion H
    end.
    apply lb_execution_enabled; assumption.
  - destruct ex. rewrite map_Cons in *.
    apply revert_always_eventually_enabled.
    + simpl.
      destruct ex.
      simpl in *.
      match goal with
      | H : lb_execution _ |- _ => inversion H
      end. simpl in *.
      apply (reachableStepS (occ_gst o)).
      * assumption.
      * apply (labeled_step_is_unlabeled_step _ (occ_label o)); try assumption.
      * eapply lb_execution_invar. eauto.
    + match goal with
    | H : always _ _ |- _ => inversion H
      end.
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
    match goal with
    | H : always ?P _ |- _ => apply (@always_map _ _ _ P)
    end.
    + apply eventually_map.
      unfold occurred, ChordSemantics.occurred.
      destruct s. rewrite map_Cons.
      tauto.
    + assumption.
Qed.



Theorem chord_serialized_stabilization :
  forall ex : infseq.infseq occurrence,
    reachable_st_serialized (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    continuously now_ideal (map revert_serialize_occurrence ex).
Proof.
  intros.
  assert (extensional (continuously (now (fun o => ideal (occ_gst o))))) by
      (exact ideal_extensional).
  match goal with
  | H : extensional _ |- _ => unfold extensional in H
  end.

  apply H3 with (s1 := map serialize_occurrence (map revert_occurrence ex)).
  - apply revert_serialize_compose_exteq.
  - unfold now_ideal.
    apply serialize_continuously_ideal.
    apply ChordStabilization.chord_stabilization.
    + apply revert_reachable.
      assumption.
    + apply revert_lb_execution.
      assumption.
    + apply revert_strong_local_fairness;
        assumption.
    + apply revert_circular_wait. assumption.
Qed.
