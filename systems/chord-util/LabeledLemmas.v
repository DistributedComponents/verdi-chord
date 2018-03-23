Require Import List.
Import ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Set Bullet Behavior "Strict Subproofs".

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.

Require Import Verdi.DynamicNet.

Require Import Chord.InfSeqTactics.

Require Import Chord.Chord.

Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.

Require Import Chord.LiveNodesStayLive.
Require Import Chord.NodesHaveState.
Require Import Chord.QueryInvariant.
Require Import Chord.TimeoutMeansActive.
Require Import Chord.ValidPointersInvariant.

Lemma l_enabled_RecvMsg_In_msgs :
  forall e src dst m d,
    In dst (nodes (occ_gst e)) ->
    ~ In dst (failed_nodes (occ_gst e)) ->
    In (src, (dst, m)) (msgs (occ_gst e)) ->
    sigma (occ_gst e) dst = Some d ->
    l_enabled (RecvMsg src dst m) e.
Proof using.
  move => e src dst m d H_in_n H_in_f H_in H_s.
  find_apply_lem_hyp in_split.
  break_exists.
  rewrite /l_enabled /enabled.
  case H_r: (recv_handler_l src dst d m) => [[[[st ms] newts] clearedts] lb].
  have H_lb: lb = RecvMsg src dst m.
  rewrite /recv_handler_l /= in H_r.
    by tuple_inversion.
    rewrite H_lb {H_lb} in H_r.
    pose gst' := apply_handler_result
                   dst
                   (st, ms, newts, clearedts)
                   [e_recv (src, (dst, m))]
                   (update_msgs (occ_gst e) (x ++ x0)).
    exists gst'.
      by eapply LDeliver_node; eauto.
Qed.

Ltac break_labeled_step :=
  match goal with
  | H : labeled_step_dynamic _ _ _ |- _ =>
    destruct H
  end; subst.

Ltac clean_up_labeled_step_cases :=
  unfold label_input, label_output in *;
  try congruence;
  try (find_apply_lem_hyp timeout_handler_l_definition; expand_def; congruence);
  try (exfalso; unfold recv_handler_l in *; now tuple_inversion).

Ltac inv_labeled_step :=
  match goal with
  | H : labeled_step_dynamic _ _ _ |- _ =>
    inv H; clean_up_labeled_step_cases
  end.

Ltac invc_labeled_step :=
  match goal with
  | H : labeled_step_dynamic _ _ _ |- _ =>
    invc H; clean_up_labeled_step_cases
  end.

Ltac inv_lb_execution :=
  match goal with
  | H : lb_execution _ |- _ =>
    inv H
  end.

Ltac invc_lb_execution :=
  match goal with
  | H : lb_execution _ |- _ =>
    invc H
  end.

Ltac inv_timeout_constraint :=
  match goal with
  | H : timeout_constraint _ _ _ |- _ =>
    inv H
  end.

Lemma labeled_step_preserves_state_existing :
  forall gst gst' l h d,
    sigma gst h = Some d ->
    labeled_step_dynamic gst l gst' ->
    exists d',
      sigma gst' h = Some d'.
Proof using.
  intros.
  break_labeled_step;
    solve [eexists; eauto |
           match goal with
           | H: In ?n (nodes _) |- exists _, sigma _ ?h = _ => destruct (addr_eq_dec n h)
           end;
           subst_max;
           eexists;
           eauto using sigma_ahr_updates, sigma_ahr_passthrough].
Qed.

Lemma define_msg_from_recv_step_equality :
  forall m d st ms nts cts src dst p,
    recv_handler_l (fst m) (fst (snd m)) d (snd (snd m)) = (st, ms, nts, cts, RecvMsg src dst p) ->
    (m = (src, (dst, p)) /\ fst m = src /\ fst (snd m) = dst /\ snd (snd m) = p).
Proof using.
  unfold recv_handler_l.
  intuition;
    now tuple_inversion.
Qed.

Ltac recover_msg_from_recv_step_equality :=
  find_copy_apply_lem_hyp define_msg_from_recv_step_equality;
  break_and.

Ltac recover_msg_from_recv_step_equality_clear :=
  find_apply_lem_hyp define_msg_from_recv_step_equality;
  break_and.

Lemma irrelevant_message_not_removed :
  forall m p dst src to from gst gst',
    labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
    In (from, (to, m)) (msgs gst) ->
    (from, (to, m)) <> (src, (dst, p)) ->
    In (from, (to, m)) (msgs gst').
Proof using.
  intros.
  inv_labeled_step.
  apply in_or_app.
  right.
  recover_msg_from_recv_step_equality.
  repeat find_reverse_rewrite.
  eauto with struct_util datatypes.
  cut (In (from, (to, m)) (xs ++ ys));
    eauto with struct_util.
Qed.

Ltac destruct_recv_handler_l :=
  match goal with
    |- context[recv_handler_l ?from ?to ?st ?p] =>
    unfold recv_handler_l;
    destruct (recv_handler from to st p) as [[[?st ?ms] ?cts] ?nts] eqn:?H
  end.

Lemma when_RecvMsg_enabled :
  forall from to p gst,
    In to (nodes gst) ->
    ~ In to (failed_nodes gst) ->
    (exists st, sigma gst to = Some st) ->
    In (from, (to, p)) (msgs gst) ->
    enabled (RecvMsg from to p) gst.
Proof using.
  intros.
  find_apply_lem_hyp in_split.
  break_exists.
  match goal with
  | H: sigma ?gst ?to = Some ?d |- enabled (RecvMsg ?from ?to ?p) ?gst =>
    assert (exists st ms nts cts, recv_handler_l from to d p = (st, ms, nts, cts, RecvMsg from to p))
  end.
  destruct_recv_handler_l.
  repeat eexists.
  break_exists.
  unfold enabled.
  eauto using LDeliver_node.
Qed.

Lemma recv_implies_state_exists :
  forall gst gst' gst'' from to src dst p m,
    labeled_step_dynamic gst (RecvMsg from to p) gst'  ->
    labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
    exists st,
      sigma gst' dst = Some st.
Proof using.
  intros.
  invc_labeled_step.
  invc_labeled_step.
  recover_msg_from_recv_step_equality_clear.
  recover_msg_from_recv_step_equality_clear.
  repeat find_rewrite.
  unfold update_msgs.
  destruct (addr_eq_dec to dst).
  - repeat find_rewrite.
    eauto using sigma_ahr_updates.
  - eauto using sigma_ahr_passthrough.
Qed.

Lemma recv_implies_msg_in_before :
  forall gst gst' src dst p,
    labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
    In (src, (dst, p)) (msgs gst).
Proof using.
  intros.
  invc_labeled_step.
  recover_msg_from_recv_step_equality_clear.
  repeat find_rewrite.
  auto using in_or_app, in_eq.
Qed.

Ltac construct_gst_RecvMsg :=
  match goal with
  | Hst: sigma ?gst ?d = Some ?st,
         Hmsgs: msgs ?gst = ?xs ++ (?s, (?d, ?p)) :: ?ys
    |- enabled (RecvMsg ?s ?d ?p) ?gst =>
    destruct (recv_handler_l s d st p) as [[[[?st' ?ms] ?nts] ?cts] ?l] eqn:?H;
    remember (apply_handler_result
                d
                (st', ms, nts, cts)
                (e_recv (s, (d, p)))
                (update_msgs gst (xs ++ ys))) as egst
  end.

Lemma recv_implies_node_in :
  forall gst gst' src dst p,
    labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
    In dst (nodes gst).
Proof using.
  intros.
  invc_labeled_step.
  destruct m as [? [? ?]].
  find_apply_lem_hyp define_msg_from_recv_step_equality.
  break_and.
  congruence.
Qed.

Lemma recv_implies_node_not_failed :
  forall gst gst' src dst p,
    labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
    ~ In dst (failed_nodes gst).
Proof using.
  intros.
  invc_labeled_step.
  recover_msg_from_recv_step_equality_clear.
  now repeat find_reverse_rewrite.
Qed.

Lemma failed_nodes_eq :
  forall gst gst' l,
    labeled_step_dynamic gst l gst' ->
    failed_nodes gst = failed_nodes gst'.
Proof using.
  intros.
  now invc_labeled_step.
Qed.

Lemma failed_nodes_never_added :
  forall gst gst' l h,
    labeled_step_dynamic gst l gst' ->
    ~ In h (failed_nodes gst) ->
    ~ In h (failed_nodes gst').
Proof using.
  intros.
  now invc_labeled_step.
Qed.
Hint Resolve failed_nodes_never_added : invar.

Lemma failed_nodes_never_removed :
  forall gst gst' l h,
    labeled_step_dynamic gst l gst' ->
    In h (failed_nodes gst) ->
    In h (failed_nodes gst').
Proof using.
  intros.
  now invc_labeled_step.
Qed.
Hint Resolve failed_nodes_never_removed : invar.

Lemma failed_nodes_not_new :
  forall gst gst' l h,
    labeled_step_dynamic gst l gst' ->
    In h (failed_nodes gst') ->
    In h (failed_nodes gst).
Proof using.
  intros.
  now invc_labeled_step.
Qed.
Hint Resolve failed_nodes_not_new : invar.

Lemma nodes_never_removed :
  forall gst gst' l h,
    labeled_step_dynamic gst l gst' ->
    In h (nodes gst) ->
    In h (nodes gst').
Proof using.
  intros.
  now invc_labeled_step.
Qed.
Hint Resolve nodes_never_removed : invar.

Lemma recv_implies_state_exists_after_timeout :
  forall gst gst' gst'' h t eff src dst m,
    labeled_step_dynamic gst (Timeout h t eff) gst'  ->
    labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
    exists st,
      sigma gst' dst = Some st.
Proof using.
  intros.
  invc_labeled_step.
  invc_labeled_step.
  match goal with
  | |- context[sigma (apply_handler_result ?h _ _ _) ?dst] =>
    destruct (addr_eq_dec h dst)
  end.
  - subst.
    eauto using sigma_ahr_updates.
  - recover_msg_from_recv_step_equality_clear.
    repeat find_rewrite.
    eauto using sigma_ahr_passthrough.
Qed.

Lemma recv_implies_message_exists_after_timeout :
  forall gst gst' gst'' dst src m h t eff,
    labeled_step_dynamic gst (Timeout h t eff) gst' ->
    labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
    In (src, (dst, m)) (msgs gst').
Proof using.
  intros.
  find_copy_eapply_lem_hyp recv_implies_msg_in_before.
  invc_labeled_step.
  invc_labeled_step.
  recover_msg_from_recv_step_equality_clear.
  apply in_or_app.
  right.
  assumption.
Qed.

(* TODO: put this in a good place *)
Lemma clients_not_in_failed :
  forall st h,
    reachable_st st ->
    client_addr h ->
    ~ In h (nodes st) /\
    ~ In h (failed_nodes st).
Proof.
  intros.
  induct_reachable_st.
  - intros.
    inv_prop initial_st; intuition eauto.
    repeat find_rewrite; tauto.
  - intros. inv_prop step_dynamic; simpl; auto.
    + intuition; try congruence; firstorder.
    + intuition; try congruence.
      * firstorder.
      * subst. firstorder.
      * firstorder.
Qed.


Lemma labeled_step_dynamic_timeout_enabled :
  forall gst gst' gst'' dst src m h t eff,
    labeled_step_dynamic gst (Timeout h t eff) gst' ->
    labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
    enabled (RecvMsg src dst m) gst'.
Proof using.
  intros.
  apply when_RecvMsg_enabled.
  - eauto using recv_implies_node_in, nodes_never_removed.
  - eauto using recv_implies_node_not_failed, failed_nodes_never_added.
  - eauto using recv_implies_state_exists_after_timeout.
  - eauto using recv_implies_message_exists_after_timeout.
Qed.

Lemma RecvMsg_stays_enabled_after_other_label :
  forall gst src dst m l' gst',
    reachable_st gst ->
    enabled (RecvMsg src dst m) gst ->
    l' <> RecvMsg src dst m ->
    labeled_step_dynamic gst l' gst' ->
    enabled (RecvMsg src dst m) gst'.
Proof.
  intros.
  match goal with
  | H : enabled _ _ |- _ =>
    unfold enabled in H; break_exists_name gst'';
      inversion H; try handler_def; simpl in *;
        unfold label_input, label_output in *; try congruence
  end.
  find_inversion.
  inv_prop labeled_step_dynamic; simpl in *.
  - apply when_RecvMsg_enabled; simpl; auto.
    + update_destruct; subst; rewrite_update; eauto.
    + repeat find_rewrite.
      destruct m0 as [x [y z]]. simpl.  in_crush.
  - handler_def.
    apply when_RecvMsg_enabled; simpl; auto.
    + update_destruct; subst; rewrite_update; eauto.
    + repeat find_rewrite.
      destruct m0 as [x [y z]]. simpl. in_crush.
      right. in_crush.
      match goal with
      | H : ?xs ++ ?m :: ?ys = ?xs' ++ ?m' :: ?ys' |- _ =>
        let x := fresh H in
        assert (In m (xs ++ m :: ys)) as x by in_crush;
          rewrite H in x;
          in_crush
      end.
  - apply when_RecvMsg_enabled; simpl; eauto.
    repeat find_rewrite. destruct m0 as [x [y z]]. simpl. in_crush.
  -  apply when_RecvMsg_enabled; simpl; eauto.
     repeat find_rewrite. destruct m0 as [x [y z]]. simpl. in_crush.
      match goal with
      | H : ?xs ++ ?m :: ?ys = ?xs' ++ ?m' :: ?ys' |- _ =>
        let x := fresh H in
        assert (In m (xs ++ m :: ys)) as x by in_crush;
          rewrite H in x;
          in_crush
      end. find_eapply_lem_hyp clients_not_in_failed; eauto.
      intuition.
(*
Other kinds of step don't remove (src, (dst, m)) from (msgs gst).

USED: in phase three.
DIFFICULTY: 1
*)
Qed.

Lemma RecvMsg_enabled_until_occurred :
  forall s,
    reachable_st (occ_gst (hd s)) ->
    lb_execution s ->
    forall src dst m,
      l_enabled (RecvMsg src dst m) (hd s) ->
      ~ client_addr dst ->
      weak_until (now (l_enabled (RecvMsg src dst m)))
                 (now (occurred (RecvMsg src dst m)))
                 s.
Proof using.
  cofix c.
  intros.
  destruct s as [o [o' s]].
  inv_prop lb_execution.
  destruct (label_eq_dec (RecvMsg src dst m) (occ_label o));
    try (apply W0; assumption).
  apply W_tl.
  simpl.
  eauto.
  apply c; eauto.
  - econstructor 2; eauto using labeled_step_is_unlabeled_step.
  - find_eapply_lem_hyp RecvMsg_stays_enabled_after_other_label; eauto.
Qed.

Lemma until_weak_until_eventually :
  forall T J P (s : infseq T),
    weak_until J P s ->
    eventually P s ->
    until J P s.
Proof.
  intros.
  induction 0.
  - constructor; eauto.
  - inv_prop weak_until;
      solve [constructor; eauto].
Qed.

Lemma RecvMsg_strong_until_occurred :
  forall s,
    lb_execution s ->
    reachable_st (occ_gst (hd s)) ->
    weak_local_fairness s ->
    forall src dst m d,
      In dst (nodes (occ_gst (hd s))) ->
      ~ In dst (failed_nodes (occ_gst (hd s))) ->
      ~ client_addr dst ->
      In (src, (dst, m)) (msgs (occ_gst (hd s))) ->
      sigma (occ_gst (hd s)) dst = Some d ->
      until (now (l_enabled (RecvMsg src dst m)))
            (now (occurred (RecvMsg src dst m)))
            s.
Proof using.
  intros.
  pose proof (RecvMsg_enabled_until_occurred _ ltac:(eauto) ltac:(eauto) src dst m).
  find_copy_apply_lem_hyp weak_until_until_or_always;
    eauto using l_enabled_RecvMsg_In_msgs.
  break_or_hyp.
  - eauto.
  - destruct s.
    find_copy_apply_lem_hyp always_now; simpl in *.
    eapply until_weak_until_eventually; eauto.
    eapply always_now'; eauto.
    unfold weak_local_fairness in *.
    find_eapply_lem_hyp always_continuously.
    now find_apply_hyp_hyp.
Qed.

Lemma RecvMsg_eventually_occurred :
  forall s,
    lb_execution s ->
    reachable_st (occ_gst (hd s)) ->
    weak_local_fairness s ->
    forall src dst m d,
      In dst (nodes (occ_gst (hd s))) ->
      ~ In dst (failed_nodes (occ_gst (hd s))) ->
      ~ client_addr dst ->
      In (src, (dst, m)) (msgs (occ_gst (hd s))) ->
      sigma (occ_gst (hd s)) dst = Some d ->
      eventually (now (occurred (RecvMsg src dst m))) s.
Proof using.
  intros.
  pose proof (RecvMsg_enabled_until_occurred _ ltac:(eauto) ltac:(eauto) src dst m).
  find_copy_apply_lem_hyp weak_until_until_or_always;
    eauto using l_enabled_RecvMsg_In_msgs.
  break_or_hyp.
  - eapply until_eventually; eauto.
  - destruct s.
    apply always_now.
    unfold weak_local_fairness in *.
    find_eapply_lem_hyp always_continuously.
    now find_apply_hyp_hyp.
Qed.

Lemma timeout_step_satisfies_constraint :
  forall gst h t gst' eff,
    labeled_step_dynamic gst (Timeout h t eff) gst' ->
    timeout_constraint gst h t.
Proof using.
  intros.
  now invc_labeled_step.
Qed.

Lemma if_Timeout_enabled :
  forall h t eff gst,
    enabled (Timeout h t eff) gst ->
    timeout_constraint gst h t /\
    In h (nodes gst) /\
    ~ In h (failed_nodes gst) /\
    In t (timeouts gst h) /\
    exists st, sigma gst h = Some st.
Proof.
  unfold enabled.
  intros; break_exists; break_and.
  inv_labeled_step.
  find_apply_lem_hyp timeout_handler_l_definition; expand_def.
  find_injection.
  firstorder eauto.
Qed.

Lemma when_Timeout_enabled :
  forall h t st gst,
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    In t (timeouts gst h) ->
    timeout_constraint gst h t ->
    exists eff,
      enabled (Timeout h t eff) gst.
Proof using.
  move => h t st gst H_in H_live H_st H_t H_constraint.
  unfold enabled.
  case H_r: (timeout_handler_l h st t) => [[[[st' ms] nts] cts] l].
  pose gst' := apply_handler_result
                 h
                 (st', ms, nts, t :: cts)
                 [e_timeout h t]
                 gst.
  find_copy_apply_lem_hyp timeout_handler_l_definition;
    break_exists_exists; expand_def.
  exists gst'.
  econstructor; eauto.
Qed.

Lemma timeout_implies_node_exists :
  forall gst h t eff gst',
    labeled_step_dynamic gst (Timeout h t eff) gst' ->
    In h (nodes gst).
Proof using.
  intros.
  invc_labeled_step.
Qed.

Lemma timeout_implies_node_not_failed :
  forall gst h t eff gst',
    labeled_step_dynamic gst (Timeout h t eff) gst' ->
    ~ In h (failed_nodes gst).
Proof using.
  intros.
  invc_labeled_step.
Qed.

Lemma timeout_implies_state_exists :
  forall gst h t eff gst',
    labeled_step_dynamic gst (Timeout h t eff) gst' ->
    exists st,
      sigma gst h = Some st.
Proof using.
  intros.
  invc_labeled_step.
  find_apply_lem_hyp timeout_handler_l_definition; expand_def.
  find_apply_lem_hyp timeout_handler_eff_definition; expand_def;
    solve_by_inversion' eauto.
Qed.

Lemma timeout_implies_state_exists_after :
  forall gst h t eff gst',
    labeled_step_dynamic gst (Timeout h t eff) gst' ->
    exists st,
      sigma gst' h = Some st.
Proof using.
  intros.
  invc_labeled_step.
  find_apply_lem_hyp timeout_handler_l_definition; expand_def.
  find_injection.
  rewrite sigma_ahr_updates.
  eexists; eauto.
Qed.

Lemma states_not_removed_by_recv_step :
  forall gst gst' h st src dst p,
    labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
    sigma gst h = Some st ->
    exists d,
      sigma gst' h = Some d.
Proof using.
  move => gst gst' h st src dst p H_step H_st.
  invc_labeled_step.
  recover_msg_from_recv_step_equality_clear.
  simpl.
  repeat find_rewrite.
  case (addr_eq_dec h dst).
  - move => H_eq.
    subst_max.
    repeat find_rewrite.
    find_injection.
    eexists.
    exact: update_eq.
  - move => H_neq.
    find_apply_lem_hyp not_eq_sym.
    exists st.
    rewrite <- H_st.
    exact: update_diff.
Qed.

Lemma handle_query_req_busy_never_clears :
  forall src st p st' ms nts cts,
    handle_query_req_busy src st p = (st', ms, nts, cts) ->
    cts = nil.
Proof using.
  unfold handle_query_req_busy.
  intros.
  repeat break_match;
    by tuple_inversion.
Qed.

Lemma timeouts_in_never_has_Tick :
  forall st,
    ~ In Tick (timeouts_in st).
Proof using.
  unfold timeouts_in.
  intros.
  repeat break_match.
  - auto with datatypes.
    unfold not; intro.
    find_apply_lem_hyp in_inv.
      by break_or_hyp.
  - easy.
Qed.

Lemma handle_query_res_never_clears_Tick :
  forall src dst st p q st' ms nts cts,
    handle_query_res src dst st q p = (st', ms, nts, cts) ->
    ~ In Tick cts.
Proof using.
  intros.
  find_eapply_lem_hyp handle_query_res_definition;
    repeat (break_or_hyp || break_and || break_exists); subst_max; try by apply in_nil.
  - apply timeouts_in_never_has_Tick.
  - destruct (handle_rectify _ _ _) as [[[?st ?ms] ?nts] ?cts] eqn:H_hr.
    find_apply_lem_hyp end_query_definition.
    find_apply_lem_hyp handle_rectify_definition.
    break_and; subst_max.
    autorewrite with list.
    apply timeouts_in_never_has_Tick.
  - find_apply_lem_hyp end_query_definition; break_and; subst_max.
    autorewrite with list.
    apply timeouts_in_never_has_Tick.
  - (* need handle_stabilize_definition *)
    unfold handle_stabilize in *; repeat break_match.
    + find_apply_lem_hyp start_query_definition;
        break_or_hyp; break_exists; break_and; subst_max;
          auto using timeouts_in_never_has_Tick.
    + find_apply_lem_hyp end_query_definition;
        break_and; subst_max;
          autorewrite with list;
          auto using timeouts_in_never_has_Tick.
    + find_apply_lem_hyp end_query_definition;
        break_and; subst_max;
          autorewrite with list;
          auto using timeouts_in_never_has_Tick.
  - find_apply_lem_hyp end_query_definition;
      break_and; subst_max;
        autorewrite with list;
        auto using timeouts_in_never_has_Tick.
  - auto using timeouts_in_never_has_Tick.
  - auto using timeouts_in_never_has_Tick.
  - find_apply_lem_hyp end_query_definition;
      break_and; subst_max;
        autorewrite with list;
        auto using timeouts_in_never_has_Tick.
  - find_apply_lem_hyp start_query_definition;
      break_or_hyp; break_exists; break_and; subst_max;
        auto using timeouts_in_never_has_Tick.
  - unfold add_tick in *.
    simpl in *.
    tuple_inversion.
    autorewrite with list.
    auto using timeouts_in_never_has_Tick.
Qed.

Lemma schedule_rectify_with_never_clears :
  forall h st st' ms nts cts,
    schedule_rectify_with h st = (st', ms, nts, cts) ->
    cts = [].
Proof.
  unfold schedule_rectify_with.
  intros.
  repeat break_match; tuple_inversion; tauto.
Qed.

Lemma handle_msg_never_clears_Tick :
  forall src dst st p st' ms nts cts,
    handle_msg src dst st p = (st', ms, nts, cts) ->
    ~ In Tick cts.
Proof using.
  intros.
  find_apply_lem_hyp handle_msg_definition;
    expand_def;
    try find_apply_lem_hyp handle_query_req_busy_never_clears;
    try find_apply_lem_hyp schedule_rectify_with_never_clears;
    subst_max;
    eauto using in_nil, handle_query_res_never_clears_Tick.
Qed.

Lemma do_rectify_never_clears_Tick :
  forall h st st' ms nts cts eff,
    do_rectify h st = (st', ms, nts, cts, eff) ->
    ~ In Tick cts.
Proof using.
  intros.
  find_apply_lem_hyp do_rectify_definition; expand_def; try apply in_nil.
  find_apply_lem_hyp start_query_definition; expand_def;
    auto using in_nil, timeouts_in_never_has_Tick.
Qed.

Lemma do_delayed_queries_never_clears_Tick :
  forall h st st' ms nts cts,
    do_delayed_queries h st = (st', ms, nts, cts) ->
    ~ In Tick cts.
Proof.
  intros.
  find_apply_lem_hyp do_delayed_queries_definition; expand_def.
  - apply in_nil.
  - eapply not_in_cons; split.
    + congruence.
    + apply in_nil.
Qed.

Lemma recv_handler_never_clears_Tick :
  forall src dst st p ms st' nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    ~ In Tick cts.
Proof using.
  intros.
  destruct (handle_msg src dst st p) as [[[st_hm ?ms] ?nts] ?cts] eqn:?H.

  find_copy_apply_lem_hyp handle_msg_never_clears_Tick.
  destruct (do_delayed_queries dst st_hm) as [[[st_dq ?ms] ?nts] ?cts] eqn:?H.
  find_copy_apply_lem_hyp do_delayed_queries_never_clears_Tick.
  destruct (do_rectify dst st_dq) as [[[[?st ?ms] ?nts] ?cts] ?eff] eqn:?H.
  find_copy_apply_lem_hyp do_rectify_never_clears_Tick.

  find_eapply_lem_hyp recv_handler_definition; eauto; expand_def.

  unfold not; intros.
  repeat (find_apply_lem_hyp in_app_or; break_or_hyp);
    tauto.
Qed.

Lemma recv_handler_never_clears_RectifyTick :
  forall src dst st p ms st' nts cts,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    ~ In RectifyTick cts.
Proof using.
  intros.
  find_apply_lem_hyp recv_handler_possible_cts.
  inv_prop possible_cts; in_crush; try congruence.
  find_apply_lem_hyp In_timeouts_in; expand_def; congruence.
Qed.

Definition timeout_handler_eff_Tick_adds_Tick :
  forall h st st' ms nts cts eff,
    timeout_handler_eff h st Tick = (st', ms, nts, cts, eff) ->
    In Tick nts.
Proof using.
  intros.
  find_apply_lem_hyp timeout_handler_eff_definition; expand_def;
    try congruence.
  find_apply_lem_hyp tick_handler_definition; expand_def;
    try auto with datatypes.
  destruct (start_query _ _ _) as [[[?st ?ms] ?nts] ?cts].
  find_apply_lem_hyp add_tick_definition; expand_def.
  auto with datatypes.
Qed.

Lemma timeout_handler_eff_never_removes_Tick :
  forall h st t st' ms nts cts eff,
    timeout_handler_eff h st t = (st', ms, nts, cts, eff) ->
    ~ In Tick cts.
Proof.
  intros.
  find_apply_lem_hyp timeout_handler_eff_definition; expand_def.
  - find_apply_lem_hyp tick_handler_definition; expand_def;
      try auto with datatypes.
    destruct (start_query _ _ _) as [[[?st ?ms] ?nts] ?cts] eqn:H_sq.
    find_apply_lem_hyp add_tick_definition; expand_def.
    find_apply_lem_hyp start_query_definition; expand_def;
      auto using timeouts_in_never_has_Tick with datatypes.
  - find_apply_lem_hyp keepalive_handler_definition; expand_def.
    auto with datatypes.
  - eapply do_rectify_never_clears_Tick; eauto.
  - find_apply_lem_hyp request_timeout_handler_definition; expand_def;
      try auto with datatypes.
    find_apply_lem_hyp handle_query_timeout_definition; expand_def;
      try find_apply_lem_hyp end_query_definition;
      try find_apply_lem_hyp start_query_definition;
      expand_def;
      autorewrite with list;
      auto using timeouts_in_never_has_Tick.
Qed.

Lemma timeouts_in_Request :
  forall st dst q m a,
    cur_request st = Some (dst, q, m) ->
    a = addr_of dst ->
    In (Request a m) (timeouts_in st).
Proof using.
  unfold timeouts_in.
  intros.
  repeat find_rewrite.
  exact: in_eq.
Qed.

Ltac inv_query_request :=
  match goal with
  | H : query_request _ _ |- _ => inv H
  end.

Ltac inv_request_response_pair :=
  match goal with
  | H: request_response_pair _ _ |- _ =>
    inv H
  end.

Definition request_response_pair_dec :
  forall p q,
    {request_response_pair p q} + {~ request_response_pair p q}.
Proof using.
  destruct p;
    destruct q;
    try by eauto using pair_GetSuccList, pair_GetBestPredecessor, pair_GetPredAndSuccs, pair_Ping;
    right; intro H; inv H.
Defined.

(* TODO(ryan) move this somewhere else *)
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
            [find_apply_lem_hyp in_map_iff; expand_def; unfold send in *; find_injection; in_crush
            |in_crush; eauto with datatypes]
          ].
  - inv_prop initial_st; break_and.
    repeat find_rewrite.
    in_crush.
  - in_crush; eauto.
    unfold send in *.
    find_injection; tauto.
  - simpl in *.
    find_apply_lem_hyp in_app_or.
    break_or_hyp; eauto with datatypes.
Qed.
Hint Resolve sent_non_client_message_means_in_nodes.

Lemma constrained_Request_not_cleared_by_recv_handler :
  forall gst h dst req p src st st' ms nts cts,
    reachable_st gst ->
    timeout_constraint gst h (Request dst req) ->
    In h (nodes gst) ->
    sigma gst h = Some st ->
    In (Request dst req) (timeouts gst h) ->
    In (src, (h, p)) (msgs gst) ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    In (Request dst req) nts \/ ~ In (Request dst req) cts.
Proof using.
  intros.
  find_copy_apply_lem_hyp cur_request_timeouts_related_invariant_elim; auto.
  inv_prop cur_request_timeouts_ok.
  - intuition eauto.
  - inv_prop timeout_constraint.
    destruct (client_payload_dec p).
    {
      inv_prop client_payload; repeat handler_def;
      simpl; autorewrite with list; try intuition congruence.
    }
    assert (exists st__src, sigma gst src = Some st__src) by eauto.
    break_exists_name st__src.
    assert (query_message_ok h src (cur_request st) (delayed_queries st__src)
                             (channel gst h src) (channel gst src h))
      by eauto using query_message_ok_invariant.
    assert (Request (addr_of dstp) req0 = Request dst req)
      by eauto using at_most_one_request_timeout_uniqueness.
    find_injection.
    destruct (request_response_pair_dec req p).
    + eapply recv_msg_not_right_response_never_removes_request_timeout; eauto.
      assert (response_payload p)
        by (inv_prop request_response_pair; constructor).
      assert (src = (addr_of dstp)).
      {
        repeat find_rewrite.
        inv_prop query_message_ok;
          solve [exfalso; eapply_prop no_responses; eauto|reflexivity].
      }
      intro; invcs_prop query_response; invcs_prop query_request;
        intuition eauto using request_response_pair.
    + repeat find_rewrite.
      assert (no_responses (channel gst src h)).
      {
        inv_prop query_message_ok; auto.
        find_apply_hyp_hyp.
        exfalso; intuition.
      }
      assert (~response_payload p) by eauto.
      find_copy_apply_lem_hyp timeouts_in_Some.
      destruct p; try (exfalso; find_eapply_prop response_payload; now constructor);
        right; repeat (handler_def; simpl; autorewrite with list;
                       try solve [eauto with datatypes | intuition congruence]).
Qed.

Lemma reassembled_msg_still_eq :
  forall (m : msg),
    (fst m, (fst (snd m), snd (snd m))) = m.
Proof using.
  move => m.
  destruct m as [a [b c]].
  easy.
Qed.

Lemma recv_handler_keeps_timeouts_satisfying_constraint :
  forall gst src dst p gst' t h,
    reachable_st gst ->
    labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
    In t (timeouts gst h) ->
    timeout_constraint gst h t ->
    t <> KeepaliveTick ->
    In t (timeouts gst' h).
Proof using.
  intros.
  inv_labeled_step.
  simpl.
  destruct (addr_eq_dec (fst (snd m)) h).
  - subst.
    rewrite update_same.
    destruct t.
    * apply in_or_app.
      right.
      find_apply_lem_hyp recv_handler_labeling.
      find_apply_lem_hyp recv_handler_never_clears_Tick.
      now apply in_remove_all_preserve.
    * apply in_or_app.
      right.
      find_apply_lem_hyp recv_handler_labeling.
      find_apply_lem_hyp recv_handler_never_clears_RectifyTick.
      now apply in_remove_all_preserve.
    * apply in_or_app.
      right.
      congruence.
    * find_apply_lem_hyp recv_handler_labeling.
      find_eapply_lem_hyp constrained_Request_not_cleared_by_recv_handler;
        repeat find_rewrite;
        try rewrite -> reassembled_msg_still_eq;
        eauto using in_or_app, in_eq.
      apply in_or_app.
      inv_labeled_step.
      intuition auto using in_remove_all_preserve.
  - by rewrite update_diff.
Qed.

Lemma enabled_Tick_invariant :
  forall gst l gst' eff h,
    labeled_step_dynamic gst l gst' ->
    enabled (Timeout h Tick eff) gst ->
    exists eff',
      enabled (Timeout h Tick eff') gst'.
Proof.
  intros.
  find_copy_apply_lem_hyp if_Timeout_enabled; expand_def.
  invc_labeled_step.
  - find_apply_lem_hyp timeout_handler_l_definition; expand_def.
    find_copy_apply_lem_hyp timeout_handler_eff_never_removes_Tick.
    destruct (addr_eq_dec (ltac:(eauto)) h);
      destruct (timeout_eq_dec (ltac:(eauto)) Tick); subst_max.
    + find_copy_apply_lem_hyp timeout_handler_eff_Tick_adds_Tick.
      eapply when_Timeout_enabled; eauto.
      * erewrite apply_handler_result_updates_sigma; eauto.
      * simpl; rewrite_update.
        auto with datatypes.
      * constructor.
    + eapply when_Timeout_enabled; eauto.
      * erewrite apply_handler_result_updates_sigma; eauto.
      * simpl; rewrite_update.
        intuition auto using in_or_app, in_remove_all_preserve, remove_preserve.
      * constructor.
    + eapply when_Timeout_enabled; eauto.
      * simpl; rewrite_update; find_rewrite; auto.
      * simpl; rewrite_update; auto.
      * constructor.
    + eapply when_Timeout_enabled; eauto.
      * simpl; rewrite_update; find_rewrite; auto.
      * simpl; rewrite_update; auto.
      * constructor.
  - unfold recv_handler_l in *.
    tuple_inversion.
    find_rewrite.
    find_copy_apply_lem_hyp recv_handler_never_clears_Tick.
    destruct (addr_eq_dec (fst (snd (ltac:(eauto)))) h); subst.
    + eapply when_Timeout_enabled; eauto.
      * simpl; rewrite_update; auto.
      * simpl; rewrite_update.
        intuition auto using in_or_app, in_remove_all_preserve, remove_preserve.
      * constructor.
    + eapply when_Timeout_enabled; eauto.
      * simpl; rewrite_update; find_rewrite; auto.
      * simpl; rewrite_update.
        intuition auto using in_or_app, in_remove_all_preserve, remove_preserve.
      * constructor.
  - eapply when_Timeout_enabled; solve [eauto | constructor].
  - eapply when_Timeout_enabled; solve [eauto | constructor].
Qed.

Lemma eventual_exists_invariant_always_true :
  forall X ex (P : X -> global_state -> Prop),
    lb_execution ex ->
    eventually (now (fun o => exists x0, P x0 (occ_gst o))) ex ->
    (forall gst l gst' x0',
        labeled_step_dynamic gst l gst' ->
        P x0' gst ->
        exists x, P x gst') ->
    continuously (now (fun o => exists x, P x (occ_gst o))) ex.
Proof.
  intros.
  match goal with
  | [ H : eventually _ ex |- _ ] =>
    induction H
  end.
  - constructor.
    generalize dependent s.
    cofix CIH.
    intros.
    constructor; [assumption|].
    destruct s as [o [o' s]].
    specialize (CIH (Cons o' s)).
    inv_lb_execution.
    simpl in *.
    break_exists.
    assert (exists x', P x' (occ_gst o')) by eauto; break_exists.
    eapply CIH; eauto.
  - constructor 2.
    apply IHeventually.
    eapply lb_execution_invar; eauto.
Qed.

Definition enabled_Tick_with_effect (h : addr) (eff : timeout_effect) (gst : global_state) : Prop :=
  enabled (Timeout h Tick eff) gst.
Hint Unfold enabled_Tick_with_effect.

Lemma l_enabled_Timeout_In_timeouts :
  forall h t e st,
    In h (nodes (occ_gst e)) ->
    ~ In h (failed_nodes (occ_gst e)) ->
    In t (timeouts (occ_gst e) h) ->
    sigma (occ_gst e) h = Some st ->
    timeout_constraint (occ_gst e) h t ->
    exists eff,
      l_enabled (Timeout h t eff) e.
Proof using.
  move => h t e st H_node H_live H_t H_st.
  unfold l_enabled, enabled.
  set (gst := occ_gst e) in *.
  case H_r: (timeout_handler_l h st t) => [[[[st' ms] newts] clearedts] lb].
  find_copy_apply_lem_hyp timeout_handler_l_definition; expand_def.
  pose gst' := apply_handler_result
                 h
                 (st', ms, newts, t :: clearedts)
                 [e_timeout h t]
                 gst.
  intros.
  exists x.
  exists gst'.
  eapply LTimeout; eauto.
Qed.

Lemma step_preserves_timeout_constraint :
  forall st l st' h t,
    reachable_st st ->
    labeled_step_dynamic st l st' ->
    timeout_constraint st h t ->
    timeout_constraint st' h t.
Proof.
  intros.
  invc_labeled_step;
    match goal with
    | H : timeout_constraint _ _ ?t |- timeout_constraint _ _ ?t =>
      invcs H
    end; try solve [constructor];
      repeat find_rewrite; constructor; simpl in *; auto;
        intros; intro.
  - in_crush; eauto.
    unfold send in *. solve_by_inversion.
  - in_crush; eauto.
    + unfold send in *. solve_by_inversion.
    + find_apply_hyp_hyp. in_crush.
    + find_apply_hyp_hyp. in_crush.
  - intuition eauto.
    unfold send in *. find_inversion.
    find_apply_lem_hyp clients_not_in_failed; auto.
  - in_crush; find_apply_hyp_hyp; in_crush.
Qed.

Lemma Timeout_enabled_when_open_request_to_dead_node :
  forall occ h st dst req,
    live_node (occ_gst occ) h ->
    sigma (occ_gst occ) h = Some st ->
    open_request_to (occ_gst occ) h dst req ->
    In dst (failed_nodes (occ_gst occ)) ->
    (forall res, request_response_pair req res -> ~ In (dst, (h, res)) (msgs (occ_gst occ))) ->
    l_enabled (Timeout h (Request dst req) DetectFailure) occ.
Proof.
  intros.
  break_live_node.

  destruct (timeout_handler_l h st (Request dst req))
    as [[[[st' ms] nts] cts] l] eqn:H_thl.
  copy_apply timeout_handler_l_definition H_thl; expand_def.
  inv_prop open_request_to; expand_def.
  find_copy_apply_lem_hyp timeout_handler_eff_definition; expand_def; try congruence.
  find_copy_apply_lem_hyp request_timeout_handler_definition; expand_def; try congruence.
  repeat find_rewrite.
  repeat find_injection.
  eexists; repeat find_rewrite; eapply LTimeout; eauto.
  eapply Request_needs_dst_dead_and_no_msgs; eauto.
Qed.

Lemma if_branches_same :
  forall A (p : bool) (x : A),
    (if p then x else x) = x.
Proof.
  intros.
  break_if; auto.
Qed.

Lemma channel_empty_not_in :
  forall st snd recv p,
    channel st snd recv = [] ->
    ~ In (snd, (recv, p)) (msgs st).
Proof.
  intros. intro.
  find_rewrite_lem channel_contents.
  repeat find_rewrite. solve_by_inversion.
Qed.

Lemma schedule_rectify_with_cur_request :
  forall st ptr st' ms nts cts,
    schedule_rectify_with st ptr = (st', ms, nts, cts) ->
    cur_request st' = cur_request st.
Proof.
  intros.
  unfold schedule_rectify_with in *.
  repeat break_match; simpl in *; find_inversion; auto.
Qed.

Lemma open_request_to_dead_node_preserved_or_times_out :
  forall gst l gst' h dst req,
    reachable_st gst ->
    labeled_step_dynamic gst l gst' ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    In dst (failed_nodes gst) ->
    channel gst dst h = [] ->
    open_request_to gst h dst req ->
    open_request_to gst' h dst req \/
    Timeout h (Request dst req) DetectFailure = l.
Proof.
  intros.
  inv_labeled_step.
  - find_apply_lem_hyp timeout_handler_l_definition.
    break_exists; intuition; subst.
    destruct t.
    + left. simpl in *.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and.
      destruct (addr_eq_dec h h0).
      * subst. repeat find_rewrite. find_inversion.
        unfold tick_handler in *.
        repeat find_rewrite. find_inversion.
        simpl in *. rewrite_update.
        intuition; [|repeat eexists; intuition; now eauto].
        in_crush. right. eapply remove_preserve; eauto; congruence.
      * rewrite_update. intuition.
        repeat eexists; intuition; now eauto.
    + left. simpl in *.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and.
      destruct (addr_eq_dec h h0).
      * subst. repeat find_rewrite. find_inversion.
        unfold do_rectify in *.
        repeat find_rewrite.
        find_rewrite_lem if_branches_same.
        find_inversion.
        simpl in *. rewrite_update.
        intuition; [|repeat eexists; intuition; now eauto].
        eapply remove_preserve; eauto; congruence.
      * rewrite_update. intuition.
        repeat eexists; intuition; now eauto.
    + left. simpl in *.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and.
      destruct (addr_eq_dec h h0).
      * subst. repeat find_rewrite. find_inversion.
        unfold keepalive_handler in *.
        repeat find_rewrite.
        find_inversion.
        simpl in *. rewrite_update.
        intuition; [|repeat eexists; intuition; now eauto].
        in_crush. right. eapply remove_preserve; eauto; congruence.
      * rewrite_update. intuition.
        repeat eexists; intuition; now eauto.
    + simpl in *.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and.
      destruct (addr_eq_dec h h0).
      * subst. repeat find_rewrite. find_inversion.
        unfold request_timeout_handler in *.
        repeat find_rewrite. break_if.
        -- find_inversion. right. f_equal.
           eauto using at_most_one_request_timeout_uniqueness,
           at_most_one_request_timeout_invariant.
        -- left. find_inversion.
           simpl in *. rewrite_update.
           intuition; [|repeat eexists; intuition; now eauto].
           eapply remove_preserve; eauto; congruence.
      * left. rewrite_update. intuition.
        repeat eexists; intuition; now eauto.
  - left. find_apply_lem_hyp recv_handler_labeling.
    destruct m as [snd [recv pay]]. simpl in *.
    destruct pay.
    + unfold recv_handler in *. simpl in *.
      repeat break_let. subst. find_inversion.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and. subst.
      update_destruct.
      * subst. rewrite_update. repeat find_rewrite. find_inversion.
        repeat find_rewrite. break_if.
        -- subst. exfalso.
           eapply channel_empty_not_in; eauto.
           repeat find_rewrite. in_crush.
        -- find_inversion.
           unfold do_delayed_queries in *.
           repeat find_rewrite.
           find_inversion. simpl in *.
           intuition. repeat eexists; eauto.
      * rewrite_update. intuition. repeat eexists; eauto.
    + unfold recv_handler in *. simpl in *.
      repeat break_let. subst. find_inversion.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and. subst.
      update_destruct.
      * subst. rewrite_update. repeat find_rewrite. find_inversion.
        repeat find_rewrite.
        find_apply_lem_hyp handle_query_req_busy_definition.
        unfold delay_query, do_delayed_queries in *. break_and. subst.
        repeat find_rewrite. simpl in *.
        find_inversion. simpl. split; [in_crush|].
        repeat eexists; eauto.
      * rewrite_update; intuition; repeat eexists; eauto.
    + unfold recv_handler in *. simpl in *.
      repeat break_let. subst. find_inversion.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and. subst.
      update_destruct.
      * subst. rewrite_update. repeat find_rewrite. find_inversion.
        repeat find_rewrite. break_if.
        -- subst. exfalso.
           eapply channel_empty_not_in; eauto.
           repeat find_rewrite. in_crush.
        -- find_inversion.
           unfold do_delayed_queries in *.
           repeat find_rewrite.
           find_inversion. simpl in *.
           intuition. repeat eexists; eauto.
      * rewrite_update. intuition. repeat eexists; eauto.
    + unfold recv_handler in *. simpl in *.
      repeat break_let. subst. find_inversion.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and. subst.
      update_destruct.
      * subst. rewrite_update. repeat find_rewrite. find_inversion.
        repeat find_rewrite.
        find_apply_lem_hyp handle_query_req_busy_definition.
        unfold delay_query, do_delayed_queries in *. break_and. subst.
        repeat find_rewrite. simpl in *.
        find_inversion. simpl. split; [in_crush|].
        repeat eexists; eauto.
      * rewrite_update; intuition; repeat eexists; eauto.
    + unfold recv_handler in *. simpl in *.
      repeat break_let. subst. find_inversion.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and. subst.
      update_destruct.
      * subst. rewrite_update. repeat find_rewrite. find_inversion.
        repeat find_rewrite. break_if.
        -- subst. exfalso.
           eapply channel_empty_not_in; eauto.
           repeat find_rewrite. in_crush.
        -- find_inversion.
           unfold do_delayed_queries in *.
           repeat find_rewrite.
           find_inversion. simpl in *.
           intuition. repeat eexists; eauto.
      * rewrite_update. intuition. repeat eexists; eauto.
    + unfold recv_handler in *. simpl in *.
      repeat break_let. subst. find_inversion.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and. subst.
      update_destruct.
      * subst. rewrite_update. repeat find_rewrite. find_inversion.
        repeat find_rewrite.
        find_apply_lem_hyp handle_query_req_busy_definition.
        unfold delay_query, do_delayed_queries in *. break_and. subst.
        repeat find_rewrite. simpl in *.
        find_inversion. simpl. split; [in_crush|].
        repeat eexists; eauto.
      * rewrite_update; intuition; repeat eexists; eauto.
    + unfold recv_handler in *. simpl in *.
      repeat break_let. subst. find_inversion.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and. subst.
      update_destruct.
      * subst. rewrite_update. repeat find_rewrite. find_inversion.
        repeat find_rewrite. break_if.
        -- subst. exfalso.
           eapply channel_empty_not_in; eauto.
           repeat find_rewrite. in_crush.
        -- find_inversion.
           unfold do_delayed_queries in *.
           repeat find_rewrite.
           find_inversion. simpl in *.
           intuition. repeat eexists; eauto.
      * rewrite_update. intuition. repeat eexists; eauto.
    + unfold recv_handler in *. simpl in *.
      repeat break_let. subst. find_inversion.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and. subst.
      update_destruct.
      * subst. rewrite_update. repeat find_rewrite. find_inversion.
        repeat find_rewrite.
        find_copy_apply_lem_hyp schedule_rectify_with_cur_request.
        find_apply_lem_hyp schedule_rectify_with_never_clears.
        subst.
        unfold delay_query, do_delayed_queries in *. break_and. subst.
        repeat find_rewrite. simpl in *.
        find_inversion. simpl. split; [in_crush|].
        repeat eexists; eauto.
      * rewrite_update. intuition. repeat eexists; eauto.
    + unfold recv_handler in *. simpl in *.
      repeat break_let. subst. find_inversion.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and. subst.
      update_destruct.
      * subst. rewrite_update. repeat find_rewrite. find_inversion.
        repeat find_rewrite.
        unfold delay_query, do_delayed_queries in *. break_and. subst.
        repeat find_rewrite. simpl in *.
        find_inversion. simpl. split; [in_crush|].
        repeat eexists; eauto.
      * rewrite_update; intuition; repeat eexists; eauto.
    + unfold recv_handler in *. simpl in *.
      repeat break_let. subst. find_inversion.
      unfold open_request_to in *; simpl in *.
      break_and; break_exists; break_and. subst.
      update_destruct.
      * subst. rewrite_update. repeat find_rewrite. find_inversion.
        repeat find_rewrite. break_if.
        -- subst. exfalso.
           eapply channel_empty_not_in; eauto.
           repeat find_rewrite. in_crush.
        -- find_inversion.
           unfold do_delayed_queries in *.
           repeat find_rewrite.
           find_inversion. simpl in *.
           intuition. repeat eexists; eauto.
      * rewrite_update. intuition. repeat eexists; eauto.
  - auto.
  - auto.
Qed.

Definition active_nodes (gst : global_state) :=
  RemoveAll.remove_all addr_eq_dec (failed_nodes gst) (nodes gst).

Lemma labeled_step_dynamic_preserves_active_nodes :
  forall gst l gst',
    labeled_step_dynamic gst l gst' ->
    active_nodes gst = active_nodes gst'.
Proof.
  intros; unfold active_nodes.
  erewrite labeled_step_dynamic_preserves_failed_nodes; eauto.
  erewrite labeled_step_dynamic_preserves_nodes; eauto.
Qed.

Lemma active_nodes_always_identical :
  forall l ex,
    lb_execution ex ->
    active_nodes (occ_gst (hd ex)) = l ->
    always (fun ex' => l = active_nodes (occ_gst (hd ex'))) ex.
Proof.
  cofix c. intros.
  constructor; destruct ex.
  - easy.
  - apply c; eauto using lb_execution_invar.
    inv_prop lb_execution.
    find_apply_lem_hyp labeled_step_dynamic_preserves_active_nodes.
    cbn; congruence.
Qed.

Lemma in_active_in_nodes :
  forall h gst,
    In h (active_nodes gst) ->
    In h (nodes gst).
Proof.
  unfold active_nodes.
  eauto using RemoveAll.in_remove_all_was_in.
Qed.

Lemma in_active_not_failed :
  forall h gst,
    In h (active_nodes gst) ->
    ~ In h (failed_nodes gst).
Proof.
  unfold active_nodes.
  eauto using RemoveAll.in_remove_all_not_in.
Qed.

Lemma in_nodes_not_failed_in_active :
  forall h gst,
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    In h (active_nodes gst).
Proof.
  eauto using RemoveAll.in_remove_all_preserve.
Qed.

Lemma active_nodes_invar :
  forall h gst l gst',
    In h (active_nodes gst) ->
    labeled_step_dynamic gst l gst' ->
    In h (active_nodes gst').
Proof.
  intros.
  apply in_nodes_not_failed_in_active;
    eauto using nodes_never_removed, in_active_in_nodes, failed_nodes_never_added, in_active_not_failed.
Qed.

Lemma lb_execution_cons_cons :
  forall o o' ex,
    lb_execution (Cons o (Cons o' ex)) ->
    labeled_step_dynamic (occ_gst o) (occ_label o) (occ_gst o').
Proof.
  intros.
  now inv_lb_execution.
Qed.

Lemma lb_execution_step_one_cons :
  forall o ex,
    lb_execution (Cons o ex) ->
    labeled_step_dynamic (occ_gst o) (occ_label o) (occ_gst (hd ex)).
Proof.
  intros.
  destruct ex; simpl.
  eapply lb_execution_cons_cons; eauto.
Qed.

Hint Resolve always_invar : invar.
Hint Resolve lb_execution_invar : invar.
Hint Resolve strong_local_fairness_invar : invar.
Hint Resolve weak_local_fairness_invar : invar.
Hint Resolve live_node_invariant : invar.
Hint Resolve labeled_step_is_unlabeled_step : invar.
Hint Resolve reachableStep : invar.
Hint Resolve lb_execution_step_one_cons : invar.
Hint Resolve lb_execution_cons_cons : invar.
Ltac invar_eauto :=
  eauto with invar.

Lemma channel_stays_empty' :
  forall gst gst' src dst,
    (forall p, In (src, (dst, p)) (msgs gst') -> In (src, (dst, p)) (msgs gst)) ->
    channel gst src dst = [] ->
    channel gst' src dst = [].
Proof.
  intros.
  destruct (channel gst' src dst) eqn:?; auto.
  exfalso.
  assert (In p (channel gst' src dst)) by (find_rewrite; intuition).
  find_apply_lem_hyp in_channel_in_msgs. find_apply_hyp_hyp.
  find_apply_lem_hyp in_msgs_in_channel. repeat find_rewrite. solve_by_inversion.
Qed.

Lemma channel_stays_empty :
  forall ex src dst,
    reachable_st (occ_gst (hd ex)) ->
    lb_execution ex ->
    In src (failed_nodes (occ_gst (hd ex))) ->
    channel (occ_gst (hd ex)) src dst = [] ->
    channel (occ_gst (hd (tl ex))) src dst = [].
Proof.
  intros. destruct ex. simpl in *.
  inv_prop lb_execution.
  inv_prop labeled_step_dynamic; simpl in *; repeat find_rewrite.
  - destruct (addr_eq_dec h src); subst; try congruence.
    eapply channel_stays_empty'; [|eauto]; simpl in *.
    intros. in_crush. destruct x. find_rewrite_lem send_definition.
    congruence.
  - destruct (addr_eq_dec (fst (snd m)) src); subst; try congruence.
    eapply channel_stays_empty'; [|eauto]; simpl in *.
    intros. repeat find_rewrite. in_crush.
    destruct x. find_rewrite_lem send_definition.
    congruence.
  - find_eapply_lem_hyp clients_not_in_failed; eauto.
    intuition. destruct (addr_eq_dec h src); subst; intuition.
    eapply channel_stays_empty'; [|eauto]; simpl in *.
    intros. intuition.
    find_rewrite_lem send_definition.
    congruence.
  - eapply channel_stays_empty'; [|eauto]; simpl in *.
    intros. find_rewrite. in_crush.
(*
USED: In phase one (transitively)
DIFFICULTY: 1
*)
Qed.

Lemma open_request_until_timeout :
  forall h dst req ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->

    channel (occ_gst (hd ex)) dst h = [] ->
    In h (active_nodes (occ_gst (hd ex))) ->
    In dst (failed_nodes (occ_gst (hd ex))) ->
    open_request_to (occ_gst (hd ex)) h dst req ->

    weak_until (now (fun occ => open_request_to (occ_gst occ) h dst req))
               (now (occurred (Timeout h (Request dst req) DetectFailure)))
               ex.
Proof.
  intros h dst req.
  cofix c.
  destruct ex.
  intros.
  inv_prop lb_execution.
  find_copy_eapply_lem_hyp open_request_to_dead_node_preserved_or_times_out;
    (* eauto will grab the coinduction hypothesis if we don't do something like this *)
    match goal with
    | |- weak_until _ _ _ => idtac
    | _ => eauto using in_active_in_nodes, in_active_not_failed
    end.
  break_or_hyp.
  - apply W_tl; [assumption|].
    apply c;
      invar_eauto;
      eauto using active_nodes_invar, failed_nodes_never_removed, channel_stays_empty.
  - now apply W0.
Qed.

Lemma dead_node_channel_empties_out :
  forall ex dead h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    In dead (failed_nodes (occ_gst (hd ex))) ->
    weak_local_fairness ex ->
    continuously (now (fun occ => channel (occ_gst occ) dead h = [])) ex.
Proof.
(*
USED: In phase one (transitively)
DIFFICULTY: 3
*)
Admitted.

Lemma live_node_in_active :
  forall h gst,
    live_node gst h ->
    In h (active_nodes gst).
Proof.
  intros.
  inv_prop live_node; expand_def.
  eapply in_nodes_not_failed_in_active; auto.
Qed.

Lemma request_eventually_fires :
  forall h dst req ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->

    live_node (occ_gst (hd ex)) h ->
    In dst (failed_nodes (occ_gst (hd ex))) ->
    open_request_to (occ_gst (hd ex)) h dst req ->
    channel (occ_gst (hd ex)) dst h = [] ->

    eventually (now (occurred (Timeout h (Request dst req) DetectFailure))) ex.
Proof.
  intros.
  find_apply_lem_hyp open_request_until_timeout; auto using live_node_in_active.
  find_apply_lem_hyp weak_until_until_or_always.
  break_or_hyp; [eauto using until_eventually|].
  find_copy_apply_lem_hyp (dead_node_channel_empties_out ex dst h); auto.
  find_apply_lem_hyp always_continuously.
  destruct ex. apply always_now.
  match goal with
  | H : weak_local_fairness _ |- _ => apply H
  end.
  assert (continuously
            (now (fun occ => open_request_to (occ_gst occ) h dst req) /\_
             now (fun occ => channel (occ_gst occ) dst h = []) /\_
             (fun ex => lb_execution ex /\
                     now (fun occ => live_node (occ_gst occ) h /\
                                  In dst (failed_nodes (occ_gst occ))) ex))
            (Cons o ex)).
  {
    apply continuously_and_tl; auto.
    apply continuously_and_tl; auto.
    apply E0.
    apply always_inv; [|firstorder].
    intros.
    split; break_and; eauto using lb_execution_invar.
    destruct s.
    inv_prop lb_execution; simpl in *; break_and.
    split.
    - eapply live_node_invariant; eauto.
    - eapply failed_nodes_never_removed; eauto.
  }
  eapply continuously_monotonic; [|eauto].
  intros.
  destruct s.
  do 2 invcs_prop and_tl.
  repeat break_and.
  inv_prop live_node; expand_def.
  eapply Timeout_enabled_when_open_request_to_dead_node; eauto.
  intros.
  rewrite channel_contents.
  find_rewrite.
  tauto.
Qed.

Lemma reachable_st_lb_execution_cons :
  forall o o' ex,
    lb_execution (Cons o (Cons o' ex)) ->
    reachable_st (occ_gst o) ->
    reachable_st (occ_gst o').
Proof using.
  intros.
  inv_lb_execution.
  eauto using reachableStep, labeled_step_is_unlabeled_step.
Qed.

Lemma reachable_st_always :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    always ((fun ex' => reachable_st (occ_gst (hd ex'))) /\_ lb_execution) ex.
Proof.
  intros.
  eapply always_inv.
  - intros.
    destruct s.
    inv_prop and_tl.
    split;
      eauto using lb_execution_invar, reachable_st_lb_execution_cons.
  - firstorder.
Qed.

Lemma sent_message_means_in_nodes_or_client :
  forall gst src dst p,
    reachable_st gst ->
    In (src, (dst, p)) (msgs gst) ->
    In src (nodes gst) \/ client_payload p /\ client_addr src.
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
            [find_apply_lem_hyp in_map_iff; expand_def; unfold send in *; find_injection; in_crush
            |in_crush; eauto with datatypes]
          ].
  - inv_prop initial_st; break_and.
    repeat find_rewrite.
    in_crush.
  - in_crush; eauto.
    + unfold send in *.
      find_injection; tauto.
    + find_apply_hyp_hyp; tauto.
  - unfold send in *.
    simpl in *.
    break_or_hyp.
    + find_injection; tauto.
    + find_apply_hyp_hyp; tauto.
  - simpl in *.
    assert (In (src, (dst, p)) (xs ++ m :: ys)) by in_crush.
    find_apply_hyp_hyp; tauto.
Qed.

(*TODO move to wherever response_payload is defined *)
Definition response_payload_dec :
  forall p,
    {response_payload p} + {~ response_payload p}.
Proof.
  destruct p;
    solve [left; constructor
          |right; intro; inv_prop response_payload].
Defined.
Lemma req_res_pair_response_payload :
  forall req res,
    request_response_pair req res ->
    response_payload res.
Proof.
  intros.
  inv_prop request_response_pair; constructor.
Qed.
Hint Resolve req_res_pair_response_payload.

Lemma open_request_with_response_on_wire_closed_or_preserved :
  forall gst l gst' src dst req res,
    reachable_st gst ->
    In src (nodes gst) ->
    labeled_step_dynamic gst l gst' ->
    open_request_to gst src dst req ->
    request_response_pair req res ->
    In res (channel gst dst src) ->
    RecvMsg dst src res = l \/
    open_request_to gst' src dst req /\
    In res (channel gst' dst src).
Proof.
(*
If there's a response to a request on the wire, we'll either recieve the
response or the situation will stay the same.

This still needs some set-up to be proved easily since it relies on the
assumption that there's only ever one request.

DIFFICULTY: Ryan.
USED: In phase two.
 *)
  intros.
  assert (exists st__src, sigma gst src = Some st__src)
    by eauto.
  break_exists_name st__src.
  assert (exists st__src, sigma gst' src = Some st__src)
    by eauto with invar.
  break_exists_name st__src'.
  assert (~ client_payload res0)
    by (intro; inv_prop client_payload; inv_prop request_response_pair).
  assert (In dst (nodes gst))
    by eauto.
  assert (exists st__dst, sigma gst dst = Some st__dst)
    by eauto.
  break_exists_name st__dst.
  assert (exists st__dst, sigma gst' dst = Some st__dst)
    by eauto with invar.
  break_exists_name st__dst'.
  assert (query_message_ok src dst (cur_request st__src) (delayed_queries st__dst)
                           (channel gst src dst) (channel gst dst src)).
    by (eapply query_message_ok_invariant; eauto).
  assert (query_message_ok src dst (cur_request st__src') (delayed_queries st__dst')
                           (channel gst' src dst) (channel gst' dst src))
    by (eapply query_message_ok_invariant; eauto with invar).
  inv_prop open_request_to; expand_def.
  assert (cur_request_timeouts_ok' (cur_request st__src) (timeouts gst src))
    by eauto.
  assert (cur_request_timeouts_ok' (cur_request st__src') (timeouts gst' src)).
  {
    eapply cur_request_timeouts_ok'_complete.
    eapply cur_request_timeouts_related_invariant; eauto with invar.
  }

  inv_prop labeled_step_dynamic.
  - handler_def.
    handler_def.
    + right; simpl in *.
      update_destruct; subst; rewrite_update; simpl; auto.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto;
             repeat (handler_def || handler_simpl);
             eauto using remove_preserve.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
    + right; simpl in *.
      update_destruct; subst; rewrite_update; simpl; auto.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto;
             repeat (handler_def || handler_simpl);
             eauto using remove_preserve.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
    + right; simpl in *.
      update_destruct; subst; rewrite_update; simpl; auto.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto;
             repeat (handler_def || handler_simpl);
             eauto using remove_preserve.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
    + right; simpl in *.
      update_destruct; subst; rewrite_update; simpl; auto.
      * match goal with
           | H : In (Request ?x1 ?y1) _, H' : In (Request ?x2 ?y2) _ |- _ =>
             assert (Request x1 y1 = Request x2 y2) by
                 eauto using at_most_one_request_timeout_uniqueness,
                 at_most_one_request_timeout_invariant
        end. find_inversion.
        exfalso.
        inv_prop timeout_constraint.
        find_apply_lem_hyp in_channel_in_msgs.
        intuition. eauto.
      * split.
        -- eapply open_request_to_intro; simpl; try rewrite_update; eauto.
        -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
             in_crush.
  - handler_def.
    destruct m as [m__src [m__dst p]].
    simpl (fst _) in *; simpl (snd _) in *.
    assert (In (m__src, (m__dst, p)) (msgs gst))
      by (repeat find_rewrite; in_crush).
    assert (m__src <> (addr_of x1) /\ client_addr m__src /\ client_payload p \/ exists stm, sigma gst m__src = Some stm).
    {
      find_eapply_lem_hyp sent_message_means_in_nodes_or_client; eauto.
      break_or_hyp.
      right; eauto.
      left.
      break_and.
      split; auto.
      intro; subst.
      find_eapply_lem_hyp clients_not_in_failed; eauto.
      break_and; eauto.
    }
    break_or_hyp; break_and.
    {
      right; split.
      - eapply open_request_to_intro; eauto.
        + repeat find_rewrite; find_injection.
          simpl; update_destruct; rewrite_update; eauto.
          subst.
          repeat find_rewrite; find_injection.
          find_eapply_lem_hyp (recv_msg_not_right_response_never_removes_request_timeout m__src src); eauto.
          break_or_hyp; try now in_crush.
          apply in_or_app; right; eauto using in_remove_all_preserve.
          intro; inv_prop client_payload; inv_prop query_response.
        + repeat find_rewrite; find_injection.
          simpl in *.
          destruct (addr_eq_dec m__dst src).
          * repeat rewrite_update.
            find_injection.
            repeat find_rewrite; find_injection.
            find_eapply_lem_hyp recv_msg_not_right_response_preserves_cur_request; eauto.
            congruence.
            intro; inv_prop query_response; inv_prop client_payload.
          * repeat rewrite_update.
            congruence.
      - repeat find_apply_lem_hyp in_channel_in_msgs.
        apply in_msgs_in_channel.
        simpl.
        repeat find_rewrite; in_crush;
          find_injection; tauto.
    }
    break_exists_name stm.
    assert (query_message_ok src m__src (cur_request st__src) (delayed_queries stm)
                             (channel gst src m__src) (channel gst m__src src))
      by (eapply query_message_ok_invariant; eauto).
    destruct (addr_eq_dec m__dst src); repeat find_rewrite.
    + subst.
      find_injection.
      inv H11; repeat find_rewrite; find_injection;
        try congruence;
        try (exfalso; eapply_prop no_responses; eauto).
      repeat find_rewrite; find_injection.
      assert (res1 = res0); subst.
      {
        repeat find_apply_lem_hyp in_split; break_exists.
        assert (no_responses (x0 ++ x2)) by eauto.
        assert (~ In res0 x0).
          by (intro; eapply_prop no_responses; [in_crush|]; eauto).
        assert (~ In res0 x2).
          by (intro; eapply_prop no_responses; [in_crush|]; eauto).
        assert (In res0 (x11 ++ res0 :: x12)) by in_crush.
        repeat find_rewrite.
        in_crush.
      }
      destruct (response_payload_dec p).
      * inv_prop query_message_ok;
          try solve [exfalso; eapply_prop no_responses; eauto;
                     eapply in_msgs_in_channel; find_rewrite; in_crush].
        repeat find_rewrite; find_injection.
        assert (res0 = p).
        {
          assert (In p (channel gst (addr_of x1) src))
            by (eapply in_msgs_in_channel; find_rewrite; in_crush).
          repeat find_apply_lem_hyp in_split; break_exists.
          repeat find_rewrite.
          assert (no_responses (x5 ++ x6)) by eauto.
          assert (~ In p x5)
            by (intro; eapply_prop no_responses; [in_crush|]; eauto).
          assert (~ In p x6)
            by (intro; eapply_prop no_responses; [in_crush|]; eauto).
          assert (In p (x0 ++ p :: x2)) by in_crush.
          assert (In p (x5 ++ res0 :: x6)) by congruence.
          in_crush.
        }
        subst; left; auto.
      * assert (p <> res0) by (intro; subst; eauto).
        right; split.
        -- assert (~ query_response x p).
           {
             intro; find_eapply_prop response_payload.
             inv_prop query_response; constructor.
           }
           find_copy_eapply_lem_hyp recv_msg_not_right_response_never_removes_request_timeout; eauto.
           eapply open_request_to_intro; try erewrite sigma_ahr_updates; simpl; eauto.
           rewrite_update.
           break_or_hyp; try now in_crush.
           apply in_or_app; right; eauto using in_remove_all_preserve.
           find_copy_eapply_lem_hyp recv_msg_not_right_response_preserves_cur_request; eauto.
           congruence.
        -- apply in_msgs_in_channel; repeat find_apply_lem_hyp in_channel_in_msgs.
           apply in_or_app; right.
           repeat find_rewrite.
           simpl; in_crush; congruence.
    + right; split.
      * find_injection.
        repeat find_rewrite.
        eapply open_request_to_intro; try erewrite sigma_ahr_passthrough; simpl; eauto.
        rewrite_update.
        repeat invcs_prop cur_request_timeouts_ok'; auto.
      * apply in_msgs_in_channel; simpl.
        apply in_or_app; right.
        repeat find_apply_lem_hyp in_channel_in_msgs.
        repeat find_rewrite.
        in_crush; find_injection; tauto.
  - right. split; eauto.
    -- find_apply_lem_hyp in_channel_in_msgs; apply in_msgs_in_channel; simpl;
         in_crush.
  - right. split; eauto.
    -- find_apply_lem_hyp in_channel_in_msgs. repeat find_rewrite.
       apply in_msgs_in_channel; simpl;
         in_crush.
       find_eapply_lem_hyp clients_not_in_failed; eauto. intuition.
Qed.
