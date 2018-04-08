Require Import List.

Require Import InfSeqExt.infseq.
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

(* liveness *)
Definition serialize_occurrence (occ : ChordSemantics.occurrence) :=
  {| occ_gst := serialize_global_state (ChordSemantics.occ_gst occ);
     occ_label := (ChordSemantics.occ_label occ) |}.

Definition revert_occurrence (occ : ChordSerializedSemantics.occurrence) :=
  {| ChordSemantics.occ_gst := revert_global_state (ChordSerializedSemantics.occ_gst occ);
     ChordSemantics.occ_label := (ChordSerializedSemantics.occ_label occ) |}.

Lemma serialize_revert_occurrence : forall occ,
    revert_occurrence (serialize_occurrence occ) = occ.
Proof.
  intros.
  unfold serialize_occurrence, revert_occurrence, revert_global_state.
  simpl.
  rewrite serialize_revert_msgs.
  rewrite serialize_revert_events.
  destruct occ. simpl.
  destruct occ_gst0. reflexivity.
Qed.

Require Import InfSeqExt.map.
Require Import InfSeqExt.exteq.

Definition lift_occurrence_prop (P : ChordSemantics.occurrence -> Prop) :
  ChordSerializedSemantics.occurrence -> Prop :=
  fun occ => P (revert_occurrence occ).

Definition lift_seq_prop (P : infseq.infseq ChordSemantics.occurrence -> Prop) :
           infseq.infseq ChordSerializedSemantics.occurrence -> Prop :=
  fun s => P (map revert_occurrence s).

Lemma serialize_revert_occurrence_seq : forall (s : infseq ChordSemantics.occurrence),
    exteq s (map revert_occurrence (map serialize_occurrence s)).
Proof.
  cofix.
  intros.
  destruct s.
  rewrite map_Cons.
  rewrite map_Cons.
  rewrite serialize_revert_occurrence.
  constructor.
  apply serialize_revert_occurrence_seq.
Qed.

Lemma serialize_revert_map : forall P s,
    extensional P -> P s -> P (map revert_occurrence (map serialize_occurrence s)).
Proof.
  intros.
  unfold extensional in *.
  apply (H s).
  - apply serialize_revert_occurrence_seq.
  - assumption.
Qed.

Lemma preserves_always : forall (seq : infseq.infseq ChordSemantics.occurrence) P,
    extensional P -> always P seq ->
    always (lift_seq_prop P) (map.map serialize_occurrence seq).
Proof.
  intros.
  apply (@always_map _ _ serialize_occurrence P).
  - intros.
    unfold lift_seq_prop.
    apply serialize_revert_map;
      assumption.
  - assumption.
Qed.

Lemma preserves_eventually : forall (seq : infseq ChordSemantics.occurrence)
                               (P : infseq ChordSemantics.occurrence -> Prop),
    extensional P -> eventually P seq ->
    eventually (lift_seq_prop P) (map.map serialize_occurrence seq).
Proof.
  intros.
  apply (@eventually_map _ _ serialize_occurrence P).
  - intros.
    unfold lift_seq_prop.
    apply serialize_revert_map; assumption.
  - assumption.
Qed.


Lemma preserves_continuously : forall (seq : infseq ChordSemantics.occurrence)
                                 (P : infseq ChordSemantics.occurrence -> Prop),
    extensional P -> continuously P seq ->
    continuously (lift_seq_prop P) (map.map serialize_occurrence seq).
Proof.
  intros.
  unfold continuously.
  apply (@continuously_map _ _ serialize_occurrence P).
  - intros.
    unfold lift_seq_prop.
    apply serialize_revert_map; assumption.
  - assumption.
Qed.

Lemma preserves_now : forall (seq : infseq ChordSemantics.occurrence)
                        (P : ChordSemantics.occurrence -> Prop),
    infseq.now P seq ->
    now (lift_occurrence_prop P) (map.map serialize_occurrence seq).
Proof.
  intros.
  unfold continuously.
  apply (@now_map _ _ _ (lift_occurrence_prop P)).
  unfold now in *.
  destruct seq. simpl.
  unfold lift_occurrence_prop.
  rewrite serialize_revert_occurrence.
  assumption.
Qed.

Lemma preserves_continuously_now : forall (seq : infseq ChordSemantics.occurrence)
                                     P  ,
    continuously (now P) seq ->
    continuously (lift_seq_prop (now P)) (map serialize_occurrence seq).
Proof.
  intros.
  apply preserves_continuously.
  - unfold extensional.
    intros.
    match goal with
    | H : now _ _ |- _ => unfold now in H
    end.
    destruct s1, s2.
    match goal with
    | H : exteq _ _ |- _ => apply exteq_inversion in H
    end.
    break_and.
    find_rewrite.
    assumption.
  - assumption.
Qed.

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

Lemma serialize_reachable : forall ex : infseq ChordSemantics.occurrence,
    reachable_st (ChordSemantics.occ_gst (infseq.hd ex)) ->
    reachable_st_serialized (occ_gst (infseq.hd (map serialize_occurrence ex))).
Proof.
  intros.
  destruct ex.
  simpl in *.
  induction H.
  - constructor.
    rewrite serialize_revert_global_state.
    assumption.
  - apply (reachableStepS (serialize_global_state gst)).
    + assumption.
    + apply step_dynamic_step_dynamic_serialized.
      assumption.
Qed.


Lemma serialize_lb_execution : forall ex,
    ChordSemantics.lb_execution ex -> lb_execution (map serialize_occurrence ex).
Proof.
  cofix.
  intros.
  do 2 (destruct ex; rewrite map_Cons).
  constructor; inv H.
  - apply labeled_step_serialized_labeled_step.
    assumption.
  - rewrite <- map_Cons.
    apply serialize_lb_execution.
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

Lemma Forall_map_serialize : forall msgs,
    Forall valid_msg (List.map serialize_msg msgs).
Proof.
  intros.
  induction msgs0.
  - constructor.
  - constructor.
    + unfold valid_msg.
      eauto.
    + assumption.
Qed.

Lemma reachable_st_valid : forall gst,
  reachable_st_serialized gst ->
  Forall valid_msg (msgs gst).
Proof.
  intros.
  induction H.
  - inversion H. repeat break_and.
    match goal with
    | H : ConstrainedChord.msgs _ = nil |- _ => unfold revert_global_state in H;
                                                simpl in H;
                                                apply map_eq_nil in H;
                                                rewrite H
    end.
    auto.
  - match goal with
    | H : step_dynamic _ _ |- _ => inversion H0; subst_max
    end.
    + unfold update_for_start, start_handler.
      repeat break_let. simpl.
      find_inversion.
      rewrite map_send_serialize.
      apply Forall_app.
      * assumption.
      * apply Forall_map_serialize.
    + unfold fail_node.
      assumption.
    + unfold apply_handler_result.
      unfold timeout_handler, serialize_res  in *.
      repeat break_let. find_inversion. simpl.
      rewrite map_send_serialize.
      apply Forall_app.
      *  assumption.
      * apply Forall_map_serialize.
    + unfold apply_handler_result.
      admit.
    + unfold update_msgs_and_trace. simpl.
      unfold client_payload, serialized_client_payload in *.
      constructor.
      * unfold valid_msg, send.
        break_exists. break_and.
        exists (h, (to, x)).
        simpl.
        admit.
      * assumption.
    + unfold update_msgs_and_trace.
      match goal with
      | H : msgs gst = _ |- _ => rewrite H in *
      end.
      simpl.
      apply Forall_app.
      * match goal with
        | H : Forall valid_msg _ |- _ => apply Forall_app_inv_r in H;
                                         inversion H
        end.
        assumption.
      * apply (Forall_app_inv_l _ (m :: ys)).
        assumption.
Admitted.

Lemma reachable_serialized_exteq : forall ex,
  reachable_st_serialized (occ_gst (hd ex)) ->
  lb_execution ex ->
  (exteq (map.map serialize_occurrence (map.map revert_occurrence ex)) ex).
Proof.
  cofix.
  intros.
  destruct ex.
  do 2 rewrite map_Cons at 1.
  match goal with
  | H : lb_execution _ |- _ => inversion H
  end.
  subst_max.
Admitted.

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

Theorem chord_serialized_stabilization :
  forall ex : infseq.infseq occurrence,
    reachable_st_serialized (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    strong_local_fairness ex ->
    always (~_ (now (lift_occurrence_prop circular_wait))) ex ->
    continuously (now (fun o => ideal (occ_gst o))) ex.
Proof.
  intros.
Admitted.