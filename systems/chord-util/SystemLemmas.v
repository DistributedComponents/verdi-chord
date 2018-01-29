Require Import Arith.
Require Import Omega.
Require FunctionalExtensionality.
Require Import List.
Import List.ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Set Bullet Behavior "Strict Subproofs".

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import InfSeqExt.infseq.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.

Definition live_node_bool (gst : global_state) (h : addr) : bool :=
  if sigma gst h is Some st then
    joined st && in_dec addr_eq_dec h (nodes gst) && ~~ in_dec addr_eq_dec h (failed_nodes gst)
  else false.

Ltac break_live_node_name var :=
  match goal with
  | H : live_node _ _ |- _ =>
    unfold live_node in H; repeat break_and; break_exists_name var; repeat break_and
  end.

Ltac break_live_node_exists_exists :=
  match goal with
  | H : live_node _ _ |- _ =>
    unfold live_node in H; repeat break_and; break_exists_exists; repeat break_and
  end.

Ltac break_dead_node :=
  match goal with
  | H : dead_node _ _ |- _ =>
    unfold dead_node in H; repeat break_and; break_exists; repeat break_and
  end.

Ltac break_dead_node_name var :=
  match goal with
  | H : dead_node _ _ |- _ =>
    unfold dead_node in H; repeat break_and; break_exists_name var; repeat break_and
  end.

Ltac break_dead_node_exists_exists :=
  match goal with
  | H : dead_node _ _ |- _ =>
    unfold dead_node in H; repeat break_and; break_exists_exists; repeat break_and
  end.

Ltac break_live_node :=
  match goal with
  | H : live_node _ _ |- _ =>
    unfold live_node in H; repeat break_and; break_exists; repeat break_and
  end.

Theorem live_node_characterization :
  forall gst h st,
    sigma gst h = Some st ->
    joined st = true ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    live_node gst h.
Proof using.
  unfold live_node.
  intuition.
  match goal with
  | x : data |- exists _ : data, _ => exists x
  end.
  intuition.
Qed.

Definition live_node_dec :
  forall gst h,
    {live_node gst h} + {~ live_node gst h}.
Proof.
  intros.
  destruct (In_dec addr_eq_dec h (nodes gst));
    destruct (In_dec addr_eq_dec h (failed_nodes gst));
    destruct (sigma gst h) as [st|] eqn:?;
    try destruct (joined st) eqn:?;
        try solve [left; eapply live_node_characterization; eassumption
                  |right; intro; inv_prop live_node; expand_def; congruence].
Defined.

Definition live_addrs (gst : global_state) : list addr :=
  filter (live_node_bool gst) (nodes gst).

Definition live_ptrs (gst : global_state) : list pointer :=
  map make_pointer (live_addrs gst).

Definition live_ptrs_with_states (gst : global_state) : list (pointer * data) :=
  FilterMap.filterMap (fun p =>
                         match sigma gst (addr_of p) with
                         | Some st => Some (p, st)
                         | None => None
                         end)
                      (live_ptrs gst).

Theorem live_node_equiv_live_node_bool :
  forall gst h,
    live_node gst h <-> live_node_bool gst h = true.
Proof using.
  unfold live_node_bool.
  intuition.
  - repeat break_match; break_live_node; last by congruence.
    find_rewrite.
    find_injection.
    apply/andP; split; first by apply/andP; split => //; case in_dec.
    by case in_dec.
  - repeat break_match; last by congruence.
    move/andP: H => [H H_f]; move/andP: H => [H H_n].
    apply: live_node_characterization; eauto.
    * by move: H_n; case in_dec.
    * by move: H_f; case in_dec.
Qed.

Lemma live_addr_In_live_addrs :
  forall gst h,
    live_node gst h ->
    In h (live_addrs gst).
Proof.
  unfold live_addrs.
  intros.
  apply filter_In; split.
  - unfold live_node in *; break_and; auto.
  - apply live_node_equiv_live_node_bool; auto.
Qed.

Lemma In_live_addrs_live :
  forall gst h,
    In h (live_addrs gst) ->
    live_node gst h.
Proof.
  unfold live_addrs.
  intros.
  find_apply_lem_hyp filter_In; break_and.
  apply live_node_equiv_live_node_bool; auto.
Qed.

Lemma In_live_ptrs_live :
  forall gst h,
    In h (live_ptrs gst) ->
    live_node gst (addr_of h).
Proof.
  unfold live_ptrs.
  intros.
  apply In_live_addrs_live.
  now find_apply_lem_hyp in_map_iff; expand_def.
Qed.

Lemma when_apply_handler_result_preserves_live_node :
  forall h h0 st st' gst gst' e ms cts nts,
    live_node gst h ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    joined st' = true ->
    gst' = apply_handler_result h0 (st', ms, cts, nts) e gst ->
    live_node gst' h.
Proof using.
  intuition.
  eapply live_node_characterization.
  - eauto.
  - break_live_node.
    repeat find_rewrite.
    find_inversion; eauto.
  - find_apply_lem_hyp apply_handler_result_preserves_nodes.
    find_inversion.
    break_live_node; auto.
  - find_apply_lem_hyp apply_handler_result_preserves_failed_nodes.
    find_inversion.
    break_live_node; auto.
Qed.

Theorem live_node_preserved_by_recv_step :
  forall gst h src st msg gst' e st' ms nts cts,
    live_node gst h ->
    Some st = sigma gst h ->
    recv_handler src h st msg = (st', ms, nts, cts) ->
    gst' = apply_handler_result h (st', ms, nts, cts) e gst ->
    live_node gst' h.
Proof using.
  intuition.
  eapply when_apply_handler_result_preserves_live_node; eauto.
  - eauto using apply_handler_result_updates_sigma.
  - eapply joined_preserved_by_recv_handler.
    * eauto.
    * break_live_node.
      find_rewrite.
      find_injection.
      auto.
Qed.

Theorem live_node_preserved_by_timeout_step :
  forall gst h st st' t ms nts cts e gst',
    live_node gst h ->
    sigma gst h = Some st ->
    timeout_handler h st t = (st', ms, nts, cts) ->
    gst' = apply_handler_result h (st', ms, nts, t :: cts) e gst ->
    live_node gst' h.
Proof using.
  intuition.
  eapply when_apply_handler_result_preserves_live_node; eauto.
  - eauto using apply_handler_result_updates_sigma.
  - break_live_node.
    unfold timeout_handler, fst in *; break_let.
    repeat find_rewrite.
    find_apply_lem_hyp joined_preserved_by_timeout_handler_eff.
    repeat find_rewrite.
    find_injection.
    eauto.
Qed.

Definition best_succ_of (gst : global_state) (h : addr) : option addr :=
  match (sigma gst) h with
  | Some st => head (filter (live_node_bool gst) (map addr_of (succ_list st)))
  | None => None
  end.

Lemma live_node_specificity :
  forall gst gst',
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst = sigma gst' ->
    live_node gst = live_node gst'.
Proof using.
  intuition.
  unfold live_node.
  repeat find_rewrite.
  auto.
Qed.

Lemma live_node_joined :
  forall gst h,
    live_node gst h ->
    exists st,
      sigma gst h = Some st /\
      joined st = true.
Proof using.
  intuition.
    by break_live_node_exists_exists.
Qed.

Lemma live_node_in_nodes :
  forall gst h,
    live_node gst h ->
    In h (nodes gst).
Proof using.
  intuition.
    by break_live_node.
Qed.
Hint Resolve live_node_in_nodes.

Lemma live_node_not_in_failed_nodes :
  forall gst h,
    live_node gst h ->
    ~ In h (failed_nodes gst).
Proof using.
  intuition.
    by break_live_node.
Qed.
Hint Resolve live_node_not_in_failed_nodes.

Lemma live_node_equivalence :
  forall gst gst' h st st',
    live_node gst h ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    joined st = joined st' ->
    live_node gst' h.
Proof using.
  intuition.
  break_live_node.
  eapply live_node_characterization.
  * eauto.
  * repeat find_rewrite.
    find_injection.
    eauto.
  * repeat find_rewrite; auto.
  * repeat find_rewrite; auto.
Qed.

Lemma live_node_means_state_exists :
  forall gst h,
    live_node gst h ->
    exists st, sigma gst h = Some st.
Proof using.
  intuition.
  find_apply_lem_hyp live_node_joined.
  break_exists_exists.
    by break_and.
Qed.
Hint Resolve live_node_means_state_exists.

Lemma coarse_live_node_characterization :
  forall gst gst' h,
    live_node gst h ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst = sigma gst' ->
    live_node gst' h.
Proof using.
  intuition.
  find_copy_apply_lem_hyp live_node_means_state_exists.
  break_exists.
  eapply live_node_equivalence.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
Qed.

Lemma adding_nodes_does_not_affect_live_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n (Some st) ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    live_node gst h ->
    live_node gst' h.
Proof using.
  intuition.
  break_live_node_name d.
  repeat split.
  * repeat find_rewrite.
    now apply in_cons.
  * by find_rewrite.
  * exists d.
    split => //.
    repeat find_reverse_rewrite.
    find_rewrite.
    find_rewrite.
    apply update_diff.
    congruence.
Qed.

(* reverse of the above, with additional hypothesis that h <> n. *)
Lemma adding_nodes_did_not_affect_live_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n st ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    live_node gst' h ->
    h <> n ->
    live_node gst h.
Proof using.
  intuition.
  unfold live_node.
  break_live_node_name d.
  repeat split.
  * repeat find_rewrite.
    find_apply_lem_hyp in_inv.
    break_or_hyp; congruence.
  * repeat find_rewrite.
    auto.
  * exists d.
    split => //.
    repeat find_reverse_rewrite.
    find_rewrite.
    find_rewrite.
    find_rewrite.
    find_rewrite.
    symmetry.
    apply update_diff; auto.
Qed.

Lemma adding_nodes_does_not_affect_dead_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n st ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    dead_node gst h ->
    dead_node gst' h.
Proof using.
  intuition.
  break_dead_node_name d.
  repeat split.
  - find_rewrite.
    eauto using in_cons.
  - find_rewrite; auto.
  - exists d.
    repeat find_reverse_rewrite.
    find_rewrite.
    find_rewrite.
    eapply update_diff.
    congruence.
Qed.


(* use lemma from Update.v instead *)
Lemma update_determined_by_f :
  forall A (f : addr -> A) x d d' y,
    y <> x ->
    update addr_eq_dec f x d y = d' ->
    f y = d'.
Proof using.
  intuition.
  symmetry.
  repeat find_reverse_rewrite.
  apply update_diff.
  now apply not_eq_sym.
Qed.

Lemma adding_nodes_did_not_affect_dead_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    In h (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n st ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    dead_node gst' h ->
    dead_node gst h.
Proof using.
  intuition.
  break_dead_node_name d.
  unfold dead_node.
  repeat split.
  - find_rewrite.
    eauto using in_cons.
  - now repeat find_rewrite.
  - eexists.
    eapply update_determined_by_f.
    * instantiate (1 := n).
      eauto using In_notIn_implies_neq.
    * repeat find_rewrite; eauto.
Qed.

Lemma coarse_dead_node_characterization :
  forall gst gst' h,
    dead_node gst h ->
    sigma gst' = sigma gst ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    dead_node gst' h.
Proof using.
  intuition.
  break_dead_node_name d.
  repeat split; try (find_rewrite; auto).
  now exists d.
Qed.

Lemma coarse_best_succ_characterization :
  forall gst gst' h s,
    best_succ gst h s ->
    sigma gst' = sigma gst ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    best_succ gst' h s.
Proof using.
  unfold best_succ in *.
  intuition.
  break_exists_exists.
  break_and.
  repeat break_and_goal.
  - eapply live_node_equivalence; eauto.
    now repeat find_rewrite.
  - now repeat find_rewrite.
  - easy.
  - move => o H_in.
    find_apply_hyp_hyp.
    eapply coarse_dead_node_characterization; eauto.
  - eapply coarse_live_node_characterization; eauto.
Qed.

Lemma adding_nodes_does_not_affect_best_succ :
  forall gst gst' h s n st,
    best_succ gst h s ->
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n (Some st) ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    best_succ gst' h s.
Proof using.
  unfold best_succ.
  intuition.
  break_exists_exists.
  break_and.
  repeat break_and_goal;
    eauto using adding_nodes_does_not_affect_live_node.
  - repeat break_live_node.
    repeat find_rewrite.
    match goal with
    | H: sigma gst h = Some _ |- _ = Some _ => rewrite <- H
    end.
    eapply update_diff.
    congruence.
  - intuition.
    find_copy_apply_hyp_hyp.
    break_dead_node.
    eauto using adding_nodes_does_not_affect_dead_node.
Qed.

Lemma global_state_eq_ext :
  forall gst gst',
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    timeouts gst = timeouts gst' ->
    sigma gst = sigma gst' ->
    msgs gst = msgs gst' ->
    trace gst = trace gst' ->
    gst = gst'.
Proof using.
  intros.
  destruct gst, gst'.
  simpl in *.
  subst_max.
  tauto.
Qed.

Definition channel (gst : global_state) (src dst : addr) : list payload :=
  filterMap
    (fun m =>
       if (addr_eq_dec (fst m) src) && (addr_eq_dec (fst (snd m)) dst)
       then Some (snd (snd m))
       else None)
    (msgs gst).

Lemma in_msgs_in_channel :
  forall gst src dst p,
    In (src, (dst, p)) (msgs gst) ->
    In p (channel gst src dst).
Proof.
  unfold channel.
  intros.
  eapply filterMap_In; eauto.
  by case addr_eq_dec, addr_eq_dec.
Qed.
Hint Resolve in_msgs_in_channel.

Lemma in_channel_in_msgs :
  forall gst src dst p,
    In p (channel gst src dst) ->
    In (src, (dst, p)) (msgs gst).
Proof.
  unfold channel.
  intros.
  find_eapply_lem_hyp In_filterMap; eauto.
  break_exists.
  break_and.
  assert (x = (src, (dst, p))).
  { break_if; try discriminate.
    find_apply_lem_hyp Bool.andb_true_iff; break_and.
    repeat find_apply_lem_hyp addr_eqb_true.
    find_injection.
    move: H1 H2.
    case addr_eq_dec, addr_eq_dec => H_a H_a' //=.
    by destruct x, p; subst. }
  now find_reverse_rewrite.
Qed.
Hint Resolve in_channel_in_msgs.

Lemma channel_contents :
  forall gst src dst p,
    In (src, (dst, p)) (msgs gst) <-> In p (channel gst src dst).
Proof using.
  intuition.
Qed.

Lemma sigma_apply_handler_result_same :
  forall h res es gst,
    sigma (apply_handler_result h res es gst) h =
    Some (fst (fst (fst res))).
Proof.
  intros. unfold apply_handler_result.
  repeat break_match. subst. simpl.
  now rewrite_update.
Qed.

Lemma sigma_apply_handler_result_diff :
  forall h h' res es gst,
    h <> h' ->
    sigma (apply_handler_result h res es gst) h' =
    sigma gst h'.
Proof.
  intros. unfold apply_handler_result.
  repeat break_match. subst. simpl.
  now rewrite_update.
Qed.

Lemma sigma_initial_st_start_handler :
  forall gst h st,
    initial_st gst ->
    sigma gst h = Some st ->
    st = fst (fst (start_handler h (nodes gst))).
Proof.
  intros.
  inv_prop initial_st.
  break_and.
  destruct (start_handler _ _) as [[d ?] ?] eqn:?.
  simpl.
  destruct (In_dec addr_eq_dec h (nodes gst)).
  - apply_prop_hyp sigma start_handler;
      intuition congruence.
  - find_higher_order_rewrite; congruence.
Qed.

Lemma timeouts_apply_handler_result_diff :
  forall h h' res es gst,
    h <> h' ->
    timeouts (apply_handler_result h res es gst) h' =
    timeouts gst h'.
Proof.
  intros. unfold apply_handler_result.
  repeat break_match. subst. simpl.
  now rewrite_update.
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

Definition has_succs (gst : global_state) (h : addr) (succs : list pointer) :=
  exists st,
    sigma gst h = Some st /\
    succ_list st = succs.

Lemma has_succs_intro :
  forall gst h succs st,
    sigma gst h = Some st ->
    succ_list st = succs ->
    has_succs gst h succs.
Proof.
  eexists; eauto.
Qed.

Lemma initial_nodes_large :
  forall gst,
    initial_st gst ->
    3 <= length (nodes gst).
Proof.
  unfold initial_st.
  intros.
  break_and.
  assert (2 <= Chord.SUCC_LIST_LEN)
    by apply Chord.succ_list_len_lower_bound.
  omega.
Qed.


Lemma Tick_in_initial_st :
  forall gst h,
    initial_st gst ->
    In h (nodes gst) ->
    timeouts gst h = [Tick].
Proof.
  intros.
  find_copy_eapply_lem_hyp initial_nodes_large.
  unfold initial_st in *.
  break_and.
  destruct (start_handler h (nodes gst)) as [[? ?] nts] eqn:?.
  assert ([Tick] = nts).
  {
    pose proof (sort_by_between_permutes h (map make_pointer (nodes gst)) _ eq_refl).
    find_copy_apply_lem_hyp Permutation.Permutation_length.
    find_rewrite_lem map_length.
    destruct (sort_by_between h (map make_pointer (nodes gst))) as [| ? [|? ?]] eqn:? in *;
      change ChordIDParams.name with addr in *;
      simpl in *; try omega.
    unfold start_handler in *.
    change ChordIDParams.name with addr in *;
      repeat find_rewrite.
    now find_inversion.
  }
  find_rewrite.
  eapply_prop_hyp start_handler start_handler; auto.
  tauto.
Qed.

Lemma in_nodes_sigma_some :
  forall gst h,
    initial_st gst ->
    In h (nodes gst) ->
    exists st,
      sigma gst h = Some st.
Proof.
  intros. unfold initial_st in *. intuition.
  match goal with
  | H : context [start_handler] |- _ =>
    remember H as Hsh; clear HeqHsh; clear H
  end.
  specialize (Hsh h). concludes.
  destruct (start_handler h (nodes gst)) as [[st ms] nts].
  specialize (Hsh st ms nts). intuition.
  eauto.
Qed.

Lemma exists_node_in_initial_st :
  forall gst,
    initial_st gst ->
    exists h,
      In h (nodes gst) /\ ~ In h (failed_nodes gst).
Proof.
  intros. unfold initial_st in *. intuition.
  destruct (nodes gst); simpl in *; [omega|].
  repeat find_rewrite.
  eexists; intuition; eauto.
Qed.

Lemma start_handler_init_state_preset :
  forall h knowns,
    length knowns > 1 ->
    start_handler h knowns =
    (init_state_preset h
                       (find_pred h (sort_by_between h (map make_pointer knowns)))
                       (find_succs h (sort_by_between h (map make_pointer knowns))),
     nil,
     Tick :: nil).
Proof.
  intros.
  unfold start_handler.
  repeat break_match;
    match goal with H : _ = _ |- _ => symmetry in H end;
    find_copy_apply_lem_hyp sort_by_between_permutes;
    [| | reflexivity];
    find_apply_lem_hyp Permutation.Permutation_length;
    rewrite map_length in H0; simpl in *; repeat find_reverse_rewrite;
      exfalso; eapply gt_irrefl; eauto.
Qed.

Lemma live_node_in_initial_st :
  forall gst,
    initial_st gst ->
    exists h,
      live_node gst h.
Proof.
  intros.
  find_copy_apply_lem_hyp exists_node_in_initial_st.
  break_exists_name h; exists h. intuition.
  find_copy_eapply_lem_hyp in_nodes_sigma_some; eauto.
  break_exists_name st. unfold live_node. intuition.
  exists st. intuition.
  find_apply_lem_hyp sigma_initial_st_start_handler; auto. subst.
  pose proof succ_list_len_lower_bound.
  rewrite start_handler_init_state_preset;
    [|unfold initial_st in *; intuition].
  reflexivity.
Qed.

Lemma sorted_knowns_same_length :
  forall h ks,
    length (sort_by_between h (map make_pointer ks)) = length ks.
Proof.
  intros.
  pose proof (sort_by_between_permutes h (map make_pointer ks) ltac:(eauto) ltac:(eauto)).
  find_apply_lem_hyp Permutation.Permutation_length.
  find_reverse_rewrite.
  apply map_length.
Qed.
Hint Rewrite sorted_knowns_same_length.


Lemma initial_start_handler_st_joined :
  forall h ks st ms nts,
    start_handler h ks = (st, ms, nts) ->
    length ks > 1 ->
    joined st = true.
Proof.
  intros.
  unfold start_handler, empty_start_res, init_state_join, init_state_preset in *.
  repeat break_match; try find_injection.
  - rewrite <- (sorted_knowns_same_length h) in *.
    find_rewrite.
    simpl in *; omega.
  - rewrite <- (sorted_knowns_same_length h) in *.
    find_rewrite.
    simpl in *; omega.
  - reflexivity.
Qed.

Lemma initial_nodes_live :
  forall gst h,
    initial_st gst ->
    In h (nodes gst) ->
    live_node gst h.
Proof.
  intros.
  destruct (start_handler h (nodes gst)) as [[?st ?ms] ?nts] eqn:?.
  inv_prop initial_st; break_and.
  eapply live_node_characterization.
  - apply_prop_hyp sigma start_handler; break_and; eauto.
  - find_copy_apply_lem_hyp initial_nodes_large.
    eapply initial_start_handler_st_joined; eauto; omega.
  - auto.
  - repeat find_rewrite; in_crush.
Qed.
Hint Resolve initial_nodes_live.

Theorem initial_succ_list :
  forall h gst st,
    initial_st gst ->
    In h (nodes gst) ->
    sigma gst h = Some st ->
    succ_list st = find_succs h (sort_by_between h (map make_pointer (nodes gst))).
Proof.
  intros.
  inv_prop initial_st; break_and.
  find_copy_apply_lem_hyp initial_nodes_large.
  destruct (start_handler h (nodes gst)) as [[?st ?ms] ?nts] eqn:?.
  copy_eapply_prop_hyp start_handler start_handler; auto; break_and.
  rewrite start_handler_init_state_preset in Heqp; eauto with arith.
  repeat find_rewrite; repeat find_injection.
  simpl in *; eauto.
Qed.
Hint Rewrite initial_succ_list.

Lemma NoDup_map_make_pointer :
  forall l, NoDup l ->
  NoDup (map make_pointer l).
Proof.
elim => //=.
move => a l IH H_nd.
inversion H_nd; subst.
find_apply_lem_hyp IH.
apply NoDup_cons => //.
move {H2 H_nd IH}.
elim: l H1 => //=.
move => a' l IH H_in H_in'.
have H_neq: a' <> a by auto.
have H_nin: ~ In a l by auto.
break_or_hyp.
- unfold make_pointer in H.
  by find_injection.
- by apply IH.
Qed.

Lemma initial_successor_lists_full :
  forall h gst,
    initial_st gst ->
    length (find_succs h (sort_by_between h (map make_pointer (nodes gst)))) = SUCC_LIST_LEN.
Proof.
  intros.
  pose proof (sorted_knowns_same_length h (nodes gst)).
  inv_prop initial_st; break_and.
  rewrite -H0 in H1.
  move: H1 H0.
  set mm := map _ _.
  move => H_le H_eq.
  have H_pm := sort_by_between_permutes h mm (sort_by_between h mm) (eq_refl _).
  have H_nd := NoDup_map_make_pointer _ H2.
  rewrite -/mm in H_nd.
  apply NoDup_Permutation_NoDup in H_pm => //.
  move: H_pm H_le.
  set l := sort_by_between _ _.
  case: l => /=.
  - move => H_nd' H_le.
    by omega.
  - move => a l H_nd' H_le.
    have H_le': length l >= SUCC_LIST_LEN by omega.
    break_if.
    * inversion H_nd'.
      subst.
      move: H11 H_le' {H12 H_nd' H_le}.
      case: l => /=.
      + move => H_in H_le.
        by auto with arith.
      + move => a l H_in H_le.
        have H_neq: a <> make_pointer h by auto.
        break_if => //.
        rewrite /chop_succs.
        rewrite firstn_length /=.
        by rewrite min_l.
    * rewrite /chop_succs.
      rewrite firstn_length /=.
      rewrite min_l //.
      by auto with arith.
Qed.

Lemma best_succ_preserved :
  forall gst gst' h h0 s st st',
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    sigma gst' = update (addr_eq_dec) (sigma gst) h (Some st') ->
    (joined st = true -> joined st' = true) ->
    succ_list st = succ_list st' \/ h <> h0 ->
    nodes gst' = nodes gst ->
    failed_nodes gst = failed_nodes gst' ->
    best_succ gst h0 s ->
    best_succ gst' h0 s.
Proof.
  unfold best_succ.
  intros.
  destruct (addr_eq_dec h h0).
  {
    symmetry in e; subst.
    expand_def.
    repeat find_rewrite; rewrite_update.
    find_inversion.
    do 3 eexists.
    repeat break_and_goal.
    - repeat break_live_node.
      eapply live_node_characterization; try congruence.
      + repeat find_rewrite; rewrite_update; eauto.
      + find_eapply_prop joined; congruence.
    - reflexivity.
    - find_rewrite; eauto.
    - intros.
      assert (dead_node gst o) by auto.
      inv_prop dead_node; expand_def; unfold dead_node; repeat find_rewrite.
      rewrite_update; eauto.
    - inv_prop live_node; expand_def.
      destruct (addr_eq_dec h s); subst.
      + eapply live_node_characterization;
          repeat find_rewrite; rewrite_update; eauto.
        find_injection; auto.
      + eapply live_node_equivalence; eauto.
        repeat find_rewrite; rewrite_update; auto.
  }
  break_exists_exists.
  repeat break_and_goal; break_and;
    repeat find_rewrite; rewrite_update.
  - repeat break_live_node.
    eapply live_node_characterization; try congruence.
    + repeat find_rewrite; rewrite_update; eauto.
    + congruence.
  - auto.
  - auto.
  - intros.
    assert (dead_node gst o) by auto.
    inv_prop dead_node; expand_def; unfold dead_node; repeat find_rewrite;
      rewrite_update; eauto.
  - repeat break_live_node.
    destruct (addr_eq_dec s h);
      eapply live_node_characterization; try congruence;
        try solve [repeat find_rewrite; rewrite_update; eauto
                  |congruence
                  |find_eapply_prop joined; congruence].
Qed.
Hint Resolve best_succ_preserved.
