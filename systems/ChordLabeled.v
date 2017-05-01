Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Verdi.DynamicNet.
Require Chord.Chord.
Import Chord.Chord.Chord.
Import Chord.ChordIDSpace.
Require Import Chord.ChordLocalProps.
Require Import Chord.ChordProof.
Require Import Chord.ChordDefinitionLemmas.
Require Import List.
Import ListNotations.
(*Require Import Wf_nat.*)
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.

Set Bullet Behavior "Strict Subproofs".

Require Chord.ChordSemantics.
Import Chord.ChordSemantics.ChordSemantics.
Import Chord.ChordSemantics.ConstrainedChord.

(* assuming sigma gst h = Some st *)
Definition failed_successors (gst : global_state) (st : data) : list pointer :=
  filter (fun p : pointer => In_dec addr_eq_dec (addr_of p) (failed_nodes gst)) (succ_list st).

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
  try now (unfold recv_handler_l, timeout_handler_l in *; tuple_inversion).

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

Ltac inv_timeout_constraint :=
  match goal with
  | H : timeout_constraint _ _ _ |- _ =>
    inv H
  end.

Lemma sigma_ahr_updates :
  forall gst n st ms nts cts e,
    sigma (apply_handler_result n (st, ms, nts, cts) e gst) n = Some st.
Proof using.
  unfold apply_handler_result.
  simpl.
  intros.
  exact: update_eq.
Qed.

Lemma sigma_ahr_passthrough :
  forall gst n st ms nts cts e h d,
    n <> h ->
    sigma gst h = Some d ->
    sigma (apply_handler_result n (st, ms, nts, cts) e gst) h = Some d.
Proof using.
  unfold apply_handler_result.
  simpl.
  intros.
  find_reverse_rewrite.
  exact: update_diff.
Qed.

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

Lemma other_elements_remain_after_removal :
  forall A (l xs ys : list A) (a b : A),
    l = xs ++ b :: ys ->
    In a l ->
    a <> b ->
    In a (xs ++ ys).
Proof using.
  intros.
  subst_max.
  do_in_app.
  break_or_hyp.
  - auto with datatypes.
  - find_apply_lem_hyp in_inv.
    break_or_hyp; auto using in_or_app || congruence.
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
  - apply in_or_app.
    right.
    recover_msg_from_recv_step_equality.
    eapply other_elements_remain_after_removal; eauto.
    now repeat find_rewrite.
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

Lemma recv_implies_msg_in_after :
  forall gst gst' gst'' dst to src from m p,
    labeled_step_dynamic gst (RecvMsg from to p) gst' ->
    labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
    (src, (dst, m)) <> (from, (to, p)) ->
    In (src, (dst, m)) (msgs gst').
Proof using.
  intros.
  eapply irrelevant_message_not_removed.
  - eauto.
  - admit.
  - admit.
(*
    - invc_labeled_step.
      invc_labeled_step.
      recover_msg_from_recv_step_equality_clear.
      recover_msg_from_recv_step_equality_clear.
      match goal with
      | H: msgs ?gst = _ ++ ?packet :: _,
        H': ?packet = ?tuple
        |- In ?tuple (msgs ?gst) =>
        rewrite H; rewrite H'
      end.
      auto using in_or_app, in_eq.
    - congruence. *)
Admitted.

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
Admitted.

Lemma recv_implies_node_not_failed :
  forall gst gst' src dst p,
    labeled_step_dynamic gst (RecvMsg src dst p) gst' ->
    ~ In dst (failed_nodes gst).
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

Lemma failed_nodes_never_removed :
  forall gst gst' l h,
    labeled_step_dynamic gst l gst' ->
    In h (failed_nodes gst) ->
    In h (failed_nodes gst').
Proof using.
  intros.
  now invc_labeled_step.
Qed.

Lemma failed_nodes_not_new :
  forall gst gst' l h,
    labeled_step_dynamic gst l gst' ->
    In h (failed_nodes gst') ->
    In h (failed_nodes gst).
Proof using.
  intros.
  now invc_labeled_step.
Qed.


Lemma nodes_never_removed :
  forall gst gst' l h,
    labeled_step_dynamic gst l gst' ->
    In h (nodes gst) ->
    In h (nodes gst').
Proof using.
  intros.
  now invc_labeled_step.
Qed.

Lemma labeled_step_dynamic_neq_payload_enabled :
  forall gst gst' gst'' to from m p,
    labeled_step_dynamic gst (RecvMsg from to p) gst' ->
    labeled_step_dynamic gst (RecvMsg from to m) gst'' ->
    m <> p ->
    enabled (RecvMsg from to m) gst'.
Proof using.
  intros.
  apply when_RecvMsg_enabled.
  - eauto using recv_implies_node_in, nodes_never_removed.
  - eauto using recv_implies_node_not_failed, failed_nodes_never_added.
  - eauto using recv_implies_state_exists.
  - eapply irrelevant_message_not_removed.
    * eauto.
    * eauto using recv_implies_msg_in_before.
    * congruence.
Qed.

Lemma labeled_step_dynamic_neq_src_enabled :
  forall gst gst' gst'' to src from m p,
    labeled_step_dynamic gst (RecvMsg from to p) gst' ->
    labeled_step_dynamic gst (RecvMsg src to m) gst'' ->
    src <> from ->
    enabled (RecvMsg src to m) gst'.
Proof using.
  intros.
  apply when_RecvMsg_enabled.
  - eauto using recv_implies_node_in, nodes_never_removed.
  - eauto using recv_implies_node_not_failed, failed_nodes_never_added.
  - eauto using recv_implies_state_exists.
  - eapply irrelevant_message_not_removed.
    * eauto.
    * eauto using recv_implies_msg_in_before.
    * congruence.
Qed.

Lemma labeled_step_dynamic_neq_dst_enabled :
  forall gst gst' gst'' dst to src from m p,
    labeled_step_dynamic gst (RecvMsg from to p) gst' ->
    labeled_step_dynamic gst (RecvMsg src dst m) gst'' ->
    dst <> to ->
    enabled (RecvMsg src dst m) gst'.
Proof using.
  intros.
  apply when_RecvMsg_enabled.
  - eauto using recv_implies_node_in, nodes_never_removed.
  - eauto using recv_implies_node_not_failed, failed_nodes_never_added.
  - eauto using recv_implies_state_exists.
  - eapply irrelevant_message_not_removed.
    * eauto.
    * eauto using recv_implies_msg_in_before.
    * congruence.
Qed.

Lemma recv_implies_state_exists_after_timeout :
  forall gst gst' gst'' h t src dst m,
    labeled_step_dynamic gst (Timeout h t) gst'  ->
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
  forall gst gst' gst'' dst src m h t,
    labeled_step_dynamic gst (Timeout h t) gst' ->
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

Lemma labeled_step_dynamic_timeout_enabled :
  forall gst gst' gst'' dst src m h t,
    labeled_step_dynamic gst (Timeout h t) gst' ->
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

Lemma RecvMsg_enabled_until_occurred :
  forall s, lb_execution s ->
            forall src dst m, l_enabled (RecvMsg src dst m) (hd s) ->
                              weak_until (now (l_enabled (RecvMsg src dst m)))
                                         (now (occurred (RecvMsg src dst m)))
                                         s.
Proof using.
  cofix c.
  case => /=.
  case => /= gst.
  case => [from to p|h t|from to p |from to p].
  - case.
    case => /= gst' lb' s H_exec src dst m H_en.
    inversion H_exec; subst_max.
    simpl in *.
    case (addr_eq_dec dst to) => H_dec_dst.
    case (addr_eq_dec src from) => H_dec_src.
    case (payload_eq_dec m p) => H_dec_m.
    subst_max.
    admit. (* was: exact: W0 *)
    subst_max.
    apply: W_tl; first by [].
    apply: c => //=.
    unfold l_enabled in *.
    simpl in *.
    unfold enabled in H_en.
    break_exists.
    move: H1 H H_dec_m.
    admit.
    (* exact: labeled_step_dynamic_neq_payload_enabled. *)
    subst_max.
    apply: W_tl; first by [].
    apply: c => //=.
    unfold l_enabled in *.
    simpl in *.
    unfold enabled in H_en.
    break_exists.
    move: H1 H H_dec_src.
    admit.
    (* exact: labeled_step_dynamic_neq_src_enabled. *)
    apply: W_tl; first by [].
    apply: c => //=.
    unfold l_enabled in *.
    simpl in *.
    unfold enabled in H_en.
    break_exists.
    move: H1 H H_dec_dst.
    admit.
    (* exact: labeled_step_dynamic_neq_dst_enabled. *)
  - admit.
  - admit.
    (*
    case.
    case => /= gst' lb' s H_exec src dst m H_en.
    inversion H_exec; subst_max.
    simpl in *.
    rewrite /l_enabled /= in H_en.
    apply: W_tl; first by [].
    apply: c => //=.
    unfold l_enabled in *.
    simpl in *.
    unfold enabled in H_en.
    break_exists.
    move: H1 H.
    exact: labeled_step_dynamic_eq_enabled.
     *)
  - admit.
Admitted.

Lemma RecvMsg_eventually_occurred :
  forall s, lb_execution s ->
            weak_local_fairness s ->
            forall src dst m d,
              In dst (nodes (occ_gst (hd s))) ->
              ~ In dst (failed_nodes (occ_gst (hd s))) ->
              In (src, (dst, m)) (msgs (occ_gst (hd s))) ->
              sigma (occ_gst (hd s)) dst = Some d ->
              eventually (now (occurred (RecvMsg src dst m))) s.
Proof using.
  move => s H_exec H_fair src dst m d H_in_n H_in_f H_in_m H_s.
  have H_un := RecvMsg_enabled_until_occurred _ H_exec src dst m.
  apply weak_until_until_or_always in H_un; last by apply: l_enabled_RecvMsg_In_msgs; eauto.
  case: H_un; first exact: until_eventually.
  move => H_al.
  apply always_continuously in H_al.
  apply H_fair in H_al.
  destruct s as [x s].
    by apply always_now in H_al.
Qed.

Lemma timeout_step_satisfies_constraint :
  forall gst h t gst',
    labeled_step_dynamic gst (Timeout h t) gst' ->
    timeout_constraint gst h t.
Proof using.
  move => gst h t gst' H_step.
  now invc_labeled_step.
Qed.

Lemma if_Timeout_enabled :
  forall h t gst,
    enabled (Timeout h t) gst ->
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
  intuition eauto.
Qed.

Lemma when_Timeout_enabled :
  forall h t st gst,
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    In t (timeouts gst h) ->
    timeout_constraint gst h t ->
    enabled (Timeout h t) gst.
Proof using.
  move => h t st gst H_in H_live H_st H_t H_constraint.
  unfold enabled.
  case H_r: (timeout_handler_l h st t) => [[[[st' ms] nts] cts] l].
  pose gst' := apply_handler_result
                 h
                 (st', ms, nts, t :: cts)
                 [e_timeout h t]
                 gst.
  have H_l: l = Timeout h t.
  rewrite /timeout_handler_l /= in H_r.
    by tuple_inversion.
    subst_max.
    exists gst'.
    now eapply LTimeout; eauto.
Qed.

Lemma timeout_implies_node_exists :
  forall gst h t gst',
    labeled_step_dynamic gst (Timeout h t) gst' ->
    In h (nodes gst).
Proof using.
  intros.
  invc_labeled_step.
Qed.

Lemma timeout_implies_node_not_failed :
  forall gst h t gst',
    labeled_step_dynamic gst (Timeout h t) gst' ->
    ~ In h (failed_nodes gst).
Proof using.
  intros.
  invc_labeled_step.
Qed.

Lemma timeout_implies_state_exists :
  forall gst h t gst',
    labeled_step_dynamic gst (Timeout h t) gst' ->
    exists st,
      sigma gst h = Some st.
Proof using.
  intros.
  invc_labeled_step.
  unfold timeout_handler_l in *.
  tuple_inversion.
    by eauto.
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

Lemma timeout_step_implies_timeout_exists :
  forall gst gst' h t,
    labeled_step_dynamic gst (Timeout h t) gst' ->
    In t (timeouts gst h).
Proof using.
  intros.
  invc_labeled_step.
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
    repeat (break_or_hyp || break_and || break_exists); subst; try by apply in_nil.
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
    unfold handle_stabilize in *; break_if.
    + find_apply_lem_hyp start_query_definition;
        break_or_hyp; break_exists; break_and; subst_max;
          auto using timeouts_in_never_has_Tick.
    + find_apply_lem_hyp end_query_definition;
        break_and; subst_max;
          autorewrite with list;
          auto using timeouts_in_never_has_Tick.
  - find_apply_lem_hyp end_query_definition;
      break_and; subst_max;
        autorewrite with list;
        auto using timeouts_in_never_has_Tick.
  - find_apply_lem_hyp end_query_definition;
      break_and; subst_max;
        autorewrite with list;
        auto using timeouts_in_never_has_Tick.
  - apply not_in_cons; split; [congruence | by apply in_nil].
  - apply not_in_cons; split; [congruence | by apply in_nil].
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

Lemma handle_msg_never_clears_Tick :
  forall src dst st p st' ms nts cts,
    handle_msg src dst st p = (st', ms, nts, cts) ->
    ~ In Tick cts.
Proof using.
  intros.
  find_apply_lem_hyp handle_msg_definition;
    expand_def;
    try find_apply_lem_hyp handle_query_req_busy_never_clears;
    subst_max;
    eauto using in_nil, handle_query_res_never_clears_Tick.
Qed.

Lemma do_rectify_never_clears_Tick :
  forall h st st' ms nts cts,
    do_rectify h st = (st', ms, nts, cts) ->
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
  destruct (do_rectify dst st_dq) as [[[?st ?ms] ?nts] ?cts] eqn:?H.
  find_copy_apply_lem_hyp do_rectify_never_clears_Tick.

  find_eapply_lem_hyp recv_handler_definition; eauto; expand_def.

  unfold not; intros.
  repeat (find_apply_lem_hyp in_app_or; break_or_hyp);
    tauto.
Qed.

Definition timeout_handler_Tick_adds_Tick :
  forall h st st' ms nts cts,
    timeout_handler h st Tick = (st', ms, nts, cts) ->
    In Tick nts.
Proof.
  intros.
  find_apply_lem_hyp timeout_handler_definition; expand_def;
    try congruence.
  find_apply_lem_hyp tick_handler_definition; expand_def;
    try auto with datatypes.
  destruct (start_query _ _ _) as [[[?st ?ms] ?nts] ?cts].
  find_apply_lem_hyp add_tick_definition; expand_def.
  auto with datatypes.
Qed.

Lemma timeout_handler_never_removes_Tick :
  forall h st t st' ms nts cts,
    timeout_handler h st t = (st', ms, nts, cts) ->
    ~ In Tick cts.
Proof.
  intros.
  find_apply_lem_hyp timeout_handler_definition; expand_def.
  - find_apply_lem_hyp tick_handler_definition; expand_def;
      try auto with datatypes.
    destruct (start_query _ _ _) as [[[?st ?ms] ?nts] ?cts] eqn:H_sq.
    find_apply_lem_hyp add_tick_definition; expand_def.
    find_apply_lem_hyp start_query_definition; expand_def;
      auto using timeouts_in_never_has_Tick with datatypes.
  - find_apply_lem_hyp keepalive_handler_definition; expand_def.
    auto with datatypes.
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

Lemma pointers_exist :
  forall a,
  exists p,
    addr_of p = a.
Proof using.
  move => a.
    by exists (make_pointer a).
Qed.

Ltac inv_request_response_pair :=
  match goal with
  | H: request_response_pair _ _ |- _ =>
    inv H
  end.

Lemma handle_query_res_doesnt_remove_constrained_requests :
  forall h dst gst req st p q st' ms nts cts,
    timeouts_match_query gst ->
    (* handle_query_res is only called on responses, so this should hold *)
    request_response_pair req p ->
    In h (nodes gst) ->
    sigma gst h = Some st ->
    In (Request dst req) (timeouts gst h) ->
    timeout_constraint gst h (Request dst req) ->
    In (dst, (h, p)) (msgs gst) ->
    handle_query_res dst h st q p = (st', ms, nts, cts) ->
    In (Request dst req) nts \/ ~ In (Request dst req) cts.
Proof using.
  unfold handle_query_res.
  intros.
  assert (exists q, cur_request st = Some (make_pointer dst, q, req) /\
               query_request q req)
    by eauto.
  break_exists.
  break_and.
  inv_request_response_pair;
    break_match;
    inv_timeout_constraint;
    inv_query_request;
    firstorder with datatypes.
Qed.

Definition request_response_pair_dec :
  forall p q,
    {request_response_pair p q} + {~ request_response_pair p q}.
Proof using.
  destruct p;
    destruct q;
    try by eauto using pair_GetSuccList, pair_GetBestPredecessor, pair_GetPredAndSuccs, pair_Ping;
    right; intro H; inv H.
Defined.

Lemma unsafe_not_req_payload_is_response :
  forall p,
    is_safe p = false ->
    is_request p = false ->
    response_payload p.
Proof using.
  intros.
  destruct p;
    try (simpl in *; discriminate);
    auto using res_GotBestPredecessor, res_GotSuccList, res_GotPredAndSuccs, res_Pong, res_Busy.
Qed.

Lemma responses_come_from_dst_of_timeout :
  forall gst dst req h src p,
    inductive_invariant gst ->
    In (Request dst req) (timeouts gst h) ->
    In (src, (h, p)) (msgs gst) ->
    response_payload p ->
    src = dst.
Admitted.

Lemma responses_are_paired_to_requests :
  forall gst req dst h p,
    inductive_invariant gst ->
    In (Request dst req) (timeouts gst h) ->
    In (dst, (h, p)) (msgs gst) ->
    response_payload p ->
    request_response_pair req p.
Admitted.

Lemma invariant_implies_timeouts_match_query :
  forall gst,
    inductive_invariant gst ->
    timeouts_match_query gst.
Admitted.

Lemma constrained_Request_not_cleared_by_recv_handler :
  forall gst h dst req p src st st' ms nts cts,
    inductive_invariant gst ->
    timeout_constraint gst h (Request dst req) ->
    In h (nodes gst) ->
    sigma gst h = Some st ->
    In (Request dst req) (timeouts gst h) ->
    In (src, (h, p)) (msgs gst) ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    In (Request dst req) nts \/ ~ In (Request dst req) cts.
Proof using.
  unfold recv_handler.
  intros.
  repeat break_match.
Admitted.

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
    inductive_invariant gst ->
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
      congruence.
    * find_apply_lem_hyp recv_handler_labeling.
      find_eapply_lem_hyp constrained_Request_not_cleared_by_recv_handler;
        repeat find_rewrite;
        try rewrite -> reassembled_msg_still_eq;
        eauto using in_or_app, in_eq.
      apply in_or_app.
      intuition auto using in_remove_all_preserve.
  - by rewrite update_diff.
Qed.

Lemma request_constraint_prevents_recv_adding_msgs :
  forall gst from to m gst' h dst p gst'' q,
    labeled_step_dynamic gst (RecvMsg from to m) gst' ->
    labeled_step_dynamic gst (Timeout h (Request dst p)) gst'' ->
    request_response_pair p q ->
    ~ In (dst, (h, q)) (msgs gst) ->
    ~ In (dst, (h, q)) (msgs gst').
Proof using.
  move => gst from to m gst' h dst p gst'' q.
Admitted.

Lemma labeled_step_dynamic_recv_timeout_enabled :
  forall gst gst' gst'' a b m h t,
    inductive_invariant gst ->
    t <> KeepaliveTick ->
    labeled_step_dynamic gst (RecvMsg a b m) gst' ->
    labeled_step_dynamic gst (Timeout h t) gst'' ->
    enabled (Timeout h t) gst'.
Proof using.
  move => gst gst' gst'' a b m h t H_inv H_notkeepalive H_recv H_timeout.
  find_copy_apply_lem_hyp timeout_step_satisfies_constraint.
  find_copy_apply_lem_hyp timeout_implies_state_exists.
  break_exists_name st.
  copy_eapply states_not_removed_by_recv_step H_recv; eauto.
  break_exists_name st'.
  eapply when_Timeout_enabled.
  - find_apply_lem_hyp timeout_implies_node_exists.
    move: H_recv H_timeout.
    exact: nodes_never_removed.
  - find_apply_lem_hyp timeout_implies_node_not_failed.
    move: H_recv H_timeout.
    exact: failed_nodes_never_added.
  - by eauto.
  - invc_labeled_step.
    inv_labeled_step.
    eapply recv_handler_keeps_timeouts_satisfying_constraint; eauto.
    (* TODO make this a lemma/tactic like recover_msg_from_... *)
    unfold timeout_handler_l in *.
    now tuple_inversion.
  - inv_timeout_constraint.
    * apply Tick_unconstrained.
    * apply KeepaliveTick_unconstrained.
    * apply Request_needs_dst_dead_and_no_msgs.
    + eapply failed_nodes_never_removed; eauto.
    + move => q H_pair.
      now eapply request_constraint_prevents_recv_adding_msgs; eauto.
Qed.

Lemma labeled_step_dynamic_timeout_neq_h_timeout_enabled :
  forall gst gst' gst'' h h' t t',
    labeled_step_dynamic gst (Timeout h t) gst' ->
    labeled_step_dynamic gst (Timeout h' t') gst'' ->
    h <> h' ->
    enabled (Timeout h' t') gst'.
Admitted.

Lemma labeled_step_dynamic_timeout_neq_timeout_enabled :
  forall gst gst' gst'' h h' t t',
    labeled_step_dynamic gst (Timeout h t) gst' ->
    labeled_step_dynamic gst (Timeout h' t') gst'' ->
    t <> t' ->
    enabled (Timeout h' t') gst'.
Admitted.

Definition satisfies_invariant (s : infseq occurrence) :=
  match s with
  | Cons o s => inductive_invariant (occ_gst o)
  end.

Lemma satisfies_invariant_inv :
  forall s,
    satisfies_invariant s ->
    inductive_invariant (occ_gst (hd s)).
Proof using.
  intros.
  now destruct s.
Qed.

Lemma always_satisfies_inv_means_hd_satisfies_inv :
  forall o s,
    always satisfies_invariant (Cons o s) ->
    inductive_invariant (occ_gst o).
Proof using.
  intros.
  find_eapply_lem_hyp always_now.
  now find_eapply_lem_hyp satisfies_invariant_inv.
Qed.


Lemma enabled_Tick_invariant :
  forall gst l gst' h,
    labeled_step_dynamic gst l gst' ->
    enabled (Timeout h Tick) gst ->
    enabled (Timeout h Tick) gst'.
Proof.
  intros.
  find_copy_apply_lem_hyp if_Timeout_enabled; expand_def.
  invc_labeled_step.
  - find_apply_lem_hyp timeout_handler_l_definition; expand_def.
    find_copy_apply_lem_hyp timeout_handler_never_removes_Tick.
    destruct (addr_eq_dec (ltac:(eauto)) h);
      destruct (timeout_eq_dec (ltac:(eauto)) Tick); subst_max.
    + find_copy_apply_lem_hyp timeout_handler_Tick_adds_Tick.
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

Lemma Timeout_enabled_until_occurred :
  forall s h t,
    t <> KeepaliveTick ->
    reachable_st (hd s).(occ_gst) ->
    lb_execution s ->
    l_enabled (Timeout h t) (hd s) ->
    weak_until (now (l_enabled (Timeout h t)))
               (now (occurred (Timeout h t)))
               s.
Proof using.
  cofix c.
  case => /=.
  case => /= gst.
  case => [from to p|h t||].
  - case.
    case => /= gst' lb' s h t H_notkt H_inv H_exec H_en.
    inversion H_exec as [o o' s' H_step_recv H_exec' H_oeq]; subst_max.
    simpl in *.
    case (addr_eq_dec h to) => H_dec_h.
    * admit.
      (*
      subst_max.
      apply: W_tl => //.
      apply c; auto using always_tl.
      unfold l_enabled in *.
      unfold enabled in H_en.
      break_exists_name gst''.
      move: H_step_recv H_en.
      find_copy_apply_lem_hyp always_satisfies_inv_means_hd_satisfies_inv.
      exact: labeled_step_dynamic_recv_timeout_enabled.
       *)
    * admit.
      (*
      apply: W_tl => //.
      apply c; auto using always_tl.
      unfold l_enabled in *.
      unfold enabled in H_en.
      break_exists_name gst''.
      move: H_step_recv H_en.
      find_copy_apply_lem_hyp always_satisfies_inv_means_hd_satisfies_inv.
      exact: labeled_step_dynamic_recv_timeout_enabled.
       *)
  - admit.
    (*
    case.
    case => /= gst' l s h' t' H_notkt H_inv H_exec H_en.
    inversion H_exec as [o o' s' H_step_timeout H_exec' H_oeq]; subst_max.
    simpl in *.
    case (addr_eq_dec h h') => H_dec_h.
    * subst_max.
      case (timeout_eq_dec t t') => H_dec_t.
    + subst_max.
      exact: W0.
    + apply W_tl; first by [].
      apply c; auto using always_tl.
      unfold l_enabled in *.
      unfold enabled in H_en.
      break_exists_name gst''.
      simpl in *.
      move: H_step_timeout H_en H_dec_t.
      exact: labeled_step_dynamic_timeout_neq_timeout_enabled.
      * apply W_tl; first by [].
        apply c; auto using always_tl.
        unfold l_enabled in *.
        unfold enabled in H_en.
        break_exists_name gst''.
        move: H_step_timeout H_en H_dec_h.
        exact: labeled_step_dynamic_timeout_neq_h_timeout_enabled.
     *)
  - admit.
Admitted.

Lemma l_enabled_Timeout_In_timeouts :
  forall h t e st,
    In h (nodes (occ_gst e)) ->
    ~ In h (failed_nodes (occ_gst e)) ->
    In t (timeouts (occ_gst e) h) ->
    sigma (occ_gst e) h = Some st ->
    timeout_constraint (occ_gst e) h t ->
    l_enabled (Timeout h t) e.
Proof using.
  move => h t e st H_node H_live H_t H_st.
  unfold l_enabled, enabled.
  set (gst := occ_gst e) in *.
  case H_r: (timeout_handler_l h st t) => [[[[st' ms] newts] clearedts] lb].
  rewrite /timeout_handler_l /= in H_r.
  have H_lb: lb = Timeout h t by tuple_inversion.
  rewrite H_lb {H_lb} in H_r.
  pose gst' := apply_handler_result
                 h
                 (st', ms, newts, t :: clearedts)
                 [e_timeout h t]
                 gst.
  exists gst'.
    by eapply LTimeout; eauto.
Qed.

Lemma unconstrained_timeout_eventually_occurred :
  forall s,
    lb_execution s ->
    weak_local_fairness s ->
    reachable_st (hd s).(occ_gst) ->
    forall h st t,
      t <> KeepaliveTick ->
      In t (timeouts (occ_gst (hd s)) h) ->
      In h (nodes (occ_gst (hd s))) ->
      ~ In h (failed_nodes (occ_gst (hd s))) ->
      sigma (occ_gst (hd s)) h = Some st ->
      timeout_constraint (occ_gst (hd s)) h t ->
      eventually (now (occurred (Timeout h t))) s.
Proof using.
  move => s H_exec H_fair H_inv h st t H_nkt H_in_n H_in_f H_in_m H_s H_constraint.
  have H_un := Timeout_enabled_until_occurred _ h t H_nkt H_inv H_exec.
  apply weak_until_until_or_always in H_un;
    last by eapply l_enabled_Timeout_In_timeouts; eauto.
  case: H_un; first exact: until_eventually.
  move => H_al.
  apply always_continuously in H_al.
  apply H_fair in H_al.
  destruct s as [x s].
    by apply always_now in H_al.
Qed.

Definition res_clears_timeout (r : res) (t : timeout) : Prop :=
  match r with
  | (_, _, _, cts) => In t cts
  end.

Inductive clears_timeout (h : addr) (t : timeout) (o : occurrence) : Prop :=
| ct_Timeout : forall st t',
    sigma (occ_gst o) h = Some st ->
    occ_label o = Timeout h t' ->
    res_clears_timeout (timeout_handler h st t') t ->
    clears_timeout h t o
| ct_RecvMsg : forall st src p,
    sigma (occ_gst o) h = Some st ->
    occ_label o = RecvMsg src h p ->
    res_clears_timeout (recv_handler src h st p) t ->
    clears_timeout h t o.

Lemma request_stays_in :
  forall o o' s src dst p,
    lb_execution (Cons o (Cons o' s)) ->
    ~ timeout_constraint (occ_gst o) src (Request dst p) ->
    In (Request dst p) (timeouts (occ_gst o) src) ->
    In (Request dst p) (timeouts (occ_gst o') src) \/
    clears_timeout src (Request dst p) o.
Admitted.

Lemma not_timeout_constraint_inv :
  forall gst src dst p,
    ~ timeout_constraint gst src (Request dst p) ->
    ~ In dst (failed_nodes gst) \/
    exists m,
      request_response_pair p m /\ In (dst, (src, m)) (msgs gst).
Proof using.
  move => gst src dst p H_ntc.
  destruct (In_dec addr_eq_dec dst (failed_nodes gst)).
  - right.
    (* might be able to avoid using this? *)
    apply Classical_Pred_Type.not_all_not_ex.
    move => H_notall.
    apply H_ntc.
    apply Request_needs_dst_dead_and_no_msgs; [ easy |].
    move => m H_pair H_in.
    eapply H_notall; eauto.
  - left.
    easy.
Qed.

Lemma msgs_remain_after_timeout :
  forall gst h t gst' src dst p,
    labeled_step_dynamic gst (Timeout h t) gst' ->
    In (src, (dst, p)) (msgs gst) ->
    In (src, (dst, p)) (msgs gst').
Admitted.

Definition Request_payload_has_response (gst : global_state) : Prop :=
  forall src dst p,
    In (Request dst p) (timeouts gst src) ->
    exists m,
      request_response_pair p m.

Definition responses_are_unique (gst : global_state) : Prop :=
  forall src dst p m m',
    In (src, (dst, m)) (msgs gst) ->
    request_response_pair p m ->
    In (src, (dst, m')) (msgs gst) ->
    request_response_pair p m' ->
    m = m'.

Lemma timeout_constraint_lifted_by_clearing :
  forall o o' src dst p,
    responses_are_unique (occ_gst o) ->
    Request_payload_has_response (occ_gst o) ->
    In (Request dst p) (timeouts (occ_gst o) src) ->
    labeled_step_dynamic (occ_gst o) (occ_label o) (occ_gst o') ->
    ~ timeout_constraint (occ_gst o) src (Request dst p) ->
    ~ timeout_constraint (occ_gst o') src (Request dst p) \/
    clears_timeout src (Request dst p) o.
Proof using.
  move => o o' src dst p H_uniqr H_res H_req H_step H_nt.
  inv_labeled_step.
  - left.
    destruct (addr_eq_dec h src);
      destruct (timeout_eq_dec t (Request dst p));
      subst_max.
    + by exfalso.
    + move => H_t.
      inv H_t.
      find_eapply_lem_hyp not_timeout_constraint_inv.
      break_or_hyp.
      * by find_eapply_lem_hyp failed_nodes_not_new; eauto.
      * break_exists.
        break_and.
        unfold timeout_handler_l, not in *; tuple_inversion.
        repeat find_reverse_rewrite.
        find_copy_eapply_lem_hyp msgs_remain_after_timeout; eauto.
    + move => H_t.
      inv H_t.
      find_eapply_lem_hyp not_timeout_constraint_inv.
      break_or_hyp.
      * by find_eapply_lem_hyp failed_nodes_not_new; eauto.
      * break_exists.
        break_and.
        intros.
        unfold timeout_handler_l in *; tuple_inversion.
        repeat find_reverse_rewrite.
        find_eapply_lem_hyp msgs_remain_after_timeout; eauto.
        find_apply_hyp_hyp.
        congruence.
    + move => H_t.
      inv H_t.
      find_eapply_lem_hyp not_timeout_constraint_inv.
      break_or_hyp.
      * by find_eapply_lem_hyp failed_nodes_not_new; eauto.
      * break_exists.
        break_and.
        intros.
        unfold timeout_handler_l in *; tuple_inversion.
        repeat find_reverse_rewrite.
        find_eapply_lem_hyp msgs_remain_after_timeout; eauto.
        find_apply_hyp_hyp.
        congruence.
  - copy_apply H_res H_req.
    break_exists_name m'.
    (* should really be: request_response_pair p m is decidable *)
    pose proof (msg_eq_dec (dst, (src, m')) m) as H_eqdec.
    destruct H_eqdec.
    * right.
      subst_max.
      simpl in *.
      unfold recv_handler_l in *; tuple_inversion.
      admit.
    * left.
      move => H_t.
      inv H_t.
      find_eapply_lem_hyp not_timeout_constraint_inv.
      break_or_hyp.
    + by find_eapply_lem_hyp failed_nodes_not_new; eauto.
    + admit.
Admitted.

Lemma queries_are_closed_by_recvmsg_occ :
  forall o src dst m p,
    inductive_invariant (occ_gst o) ->
    request_response_pair m p ->
    In (Request dst m) (timeouts (occ_gst o) src) ->
    occ_label o = RecvMsg dst src p ->
    clears_timeout src (Request dst m) o.
Admitted.

Lemma inv_responses_are_unique :
  forall gst,
    inductive_invariant gst ->
    responses_are_unique gst.
Admitted.

Lemma inv_Request_payload_has_response :
  forall gst,
    inductive_invariant gst ->
    Request_payload_has_response gst.
Admitted.

Lemma now_recvmsg_now_clears_timeout :
  forall s p m dst src,
    lb_execution s ->
    always satisfies_invariant s ->
    request_response_pair p m ->
    In (Request dst p) (timeouts (occ_gst (hd s)) src) ->
    ~ timeout_constraint (occ_gst (hd s)) src (Request dst p) ->
    (now (occurred (RecvMsg dst src m))) s ->
    (now (clears_timeout src (Request dst p))) s.
Admitted.

Lemma queries_now_closed :
  forall s p m dst src,
    lb_execution s ->
    always satisfies_invariant s ->
    request_response_pair p m ->
    In (Request dst p) (timeouts (occ_gst (hd s)) src) ->
    ~ timeout_constraint (occ_gst (hd s)) src (Request dst p) ->
    eventually (now (occurred (RecvMsg dst src m))) s ->
    eventually (now (clears_timeout src (Request dst p))) s.
Proof using.
  move => s p m dst src H_exec H_inv H_pair H_t H_const H_recv.
  induction H_recv as [ | o s'].
  - apply E0.
    unfold now in *.
    break_match.
    eapply queries_are_closed_by_recvmsg_occ; eauto.
      by find_eapply_lem_hyp always_satisfies_inv_means_hd_satisfies_inv.
  - destruct s' as [o' s']. simpl in *.
    inv H_exec.
    copy_apply always_satisfies_inv_means_hd_satisfies_inv H_inv.
    find_eapply_lem_hyp timeout_constraint_lifted_by_clearing;
      eauto using inv_Request_payload_has_response, inv_responses_are_unique.
    break_or_hyp; [| by apply E0].
    copy_eapply request_stays_in H_exec; eauto.
    break_or_hyp; [| by apply E0].
    apply E_next.
    apply always_invar in H_inv.
    now apply IHH_recv.
Qed.

Definition Request_has_message (gst : global_state) : Prop :=
  forall src dst p m,
    In (Request dst p) (timeouts gst src) ->
    request_response_pair p m ->
    (~ In dst (failed_nodes gst) /\
     In (src, (dst, p)) (msgs gst)) \/
    In (dst, (src, m)) (msgs gst).

Definition Request_messages_unique (gst : global_state) : Prop :=
  forall src dst p m m',
    In (Request dst p) (timeouts gst src) ->
    request_response_pair p m ->
    In (dst, (src, m)) (msgs gst) ->
    In (dst, (src, m')) (msgs gst) ->
    m = m'.

Lemma requests_eventually_get_responses :
  forall s,
    lb_execution s ->
    weak_local_fairness s ->
    always satisfies_invariant s ->
    forall src dst p,
      In src (nodes (occ_gst (hd s))) ->
      ~ In src (failed_nodes (occ_gst (hd s))) ->
      In dst (nodes (occ_gst (hd s))) ->
      In (Request dst p) (timeouts (occ_gst (hd s)) src) ->
      ~ timeout_constraint (occ_gst (hd s)) src (Request dst p) ->
      exists m,
        request_response_pair p m /\
        eventually (now (occurred (RecvMsg dst src m))) s.
Admitted.

Lemma requests_eventually_complete :
  forall s,
    lb_execution s ->
    weak_local_fairness s ->
    always satisfies_invariant s ->
    forall src dst p m,
      In src (nodes (occ_gst (hd s))) ->
      ~ In src (failed_nodes (occ_gst (hd s))) ->
      In dst (nodes (occ_gst (hd s))) ->
      request_response_pair p m ->
      ~ timeout_constraint (occ_gst (hd s)) src (Request dst p) ->
      In (Request dst p) (timeouts (occ_gst (hd s)) src) ->
      eventually (now (clears_timeout src (Request dst p))) s.
Proof using.
  intros.
  find_copy_eapply_lem_hyp requests_eventually_get_responses; eauto.
  break_exists_name m'.
  now eapply queries_now_closed with (m:=m').
Qed.

Lemma constrained_timeout_eventually_cleared :
  forall s,
    lb_execution s ->
    weak_local_fairness s ->
    always satisfies_invariant s ->
    (* these should all follow from satisfies_invariant. *)
    timeouts_match_msg (occ_gst (hd s)) ->
    Request_goes_to_real_node (occ_gst (hd s)) ->
    Request_payload_has_response (occ_gst (hd s)) ->
    Request_has_message (occ_gst (hd s)) ->
    forall h st t,
      In t (timeouts (occ_gst (hd s)) h) ->
      In h (nodes (occ_gst (hd s))) ->
      ~ In h (failed_nodes (occ_gst (hd s))) ->
      sigma (occ_gst (hd s)) h = Some st ->
      ~ timeout_constraint (occ_gst (hd s)) h t ->
      eventually (now (clears_timeout h t)) s.
Proof using.
  move => s H_exec H_fair H_inv H_tmsg H_reqnode H_res H_uniqm h st t H_t H_node H_live H_st H_constraint.
  destruct t.
  - (* Tick case is.. impossible *)
    exfalso.
    apply: H_constraint.
    exact: Tick_unconstrained.
  - exfalso.
    apply: H_constraint.
    exact: KeepaliveTick_unconstrained.
  - find_copy_eapply_lem_hyp not_timeout_constraint_inv.
    break_or_hyp.
    * copy_apply H_reqnode H_t.
      copy_apply H_res H_t.
      break_exists.
      eapply requests_eventually_complete; eauto.
    * break_exists.
      break_and.
      eapply requests_eventually_complete; eauto.
Qed.

Lemma always_in_nodes :
  forall s, lb_execution s ->
       forall h, In h (nodes (occ_gst (hd s))) ->
            always (now (fun o => In h (nodes (occ_gst o)))) s.
Proof using.
  cofix c.
  case => /= o; case => o' s H_exec h H_in_f.
  inversion H_exec; subst.
  apply: Always; first by [].
  rewrite /=.
  apply: c; first by [].
  rewrite /=.
    by apply: nodes_never_removed; eauto.
Qed.

Lemma always_not_failed :
  forall s, lb_execution s ->
       forall h, ~ In h (failed_nodes (occ_gst (hd s))) ->
            always (now (fun o => ~ In h (failed_nodes (occ_gst o)))) s.
Proof using.
  cofix c.
  case => /= o; case => o' s H_exec h H_in_f.
  inversion H_exec; subst.
  apply: Always; first by [].
  rewrite /=.
  apply: c; first by [].
  rewrite /=.
    by apply: failed_nodes_never_added; eauto.
Qed.
