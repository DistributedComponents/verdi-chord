Require Import List.
Import ListNotations.
Require Import Omega.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.
Require Import Chord.LiveNodePreservation.
Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemPointers.
Require Import Chord.ValidPointersInvariant.
Require Import Chord.NodesNotJoinedHaveNoSuccessors.
Require Import Chord.QueryTargetsJoined.
Require Import Chord.QueryInvariant.
Require Import Chord.StabilizeOnlyWithFirstSucc.

Set Bullet Behavior "Strict Subproofs".

Lemma in_tl :
  forall A x (l : list A),
    In x (tl l) ->
    In x l.
Proof.
  induction l; simpl; tauto.
Qed.

Theorem live_node_invariant_init :
  chord_init_invariant (fun gst => live_node_in_succ_lists gst /\
                                live_node_in_msg_succ_lists gst).
Proof.
  autounfold; intros.
  inv_prop initial_st; break_and.
  repeat split.
  - unfold live_node_in_succ_lists.
    intros.
    find_copy_apply_lem_hyp initial_succ_list; auto.
    find_copy_eapply_lem_hyp (initial_successor_lists_full h).
    pose proof succ_list_len_lower_bound.
    destruct (succ_list st) as [|p l] eqn:?.
    + assert (length (@nil pointer) >= 2) by congruence.
      simpl in *; omega.
    + exists (addr_of p).
      unfold best_succ; exists st; exists nil; exists (map addr_of l).
      split; eauto.
      split; eauto.
      split; try split.
      * simpl.
         change (addr_of p :: map addr_of l) with (map addr_of (p :: l)).
         congruence.
      * intros; simpl in *; tauto.
      * eapply initial_nodes_live; eauto.
         assert (In p (chop_succs (List.tl (sort_by_between h (map make_pointer (nodes gst))))))
           by (cut (In p (p :: l)); [congruence | auto with datatypes]).
         find_apply_lem_hyp in_firstn.
         find_apply_lem_hyp in_tl.
         find_apply_lem_hyp in_sort_by_between.
         find_apply_lem_hyp in_map_iff; expand_def.
         easy.
  - autounfold; break_and; find_rewrite; in_crush.
Qed.
Hint Resolve live_node_invariant_init.

Lemma live_node_in_msg_succ_lists_app :
  forall gst xs ys,
    live_node_in_msg_succ_lists' gst xs ->
    live_node_in_msg_succ_lists' gst ys ->
    live_node_in_msg_succ_lists' gst (xs ++ ys).
Proof.
  autounfold; intros.
  match goal with
  | H: In _ _ \/ In _ _ |- _ =>
    destruct H;
      find_apply_lem_hyp in_app_or;
      intuition eauto
  end.
  Unshelve.
  all:exact None.
Qed.
Hint Resolve live_node_in_msg_succ_lists_app.

Lemma live_node_in_msg_succ_lists_app_l :
  forall gst xs ys,
    live_node_in_msg_succ_lists' gst (xs ++ ys) ->
    live_node_in_msg_succ_lists' gst xs.
Proof.
  autounfold; intros.
  match goal with
  | H: In _ _ \/ In _ _ |- _ =>
    destruct H; eauto using in_or_app
  end.
  Unshelve.
  all:exact None.
Qed.
Hint Resolve live_node_in_msg_succ_lists_app_l.

Lemma live_node_in_msg_succ_lists_app_r :
  forall gst xs ys,
    live_node_in_msg_succ_lists' gst (xs ++ ys) ->
    live_node_in_msg_succ_lists' gst ys.
Proof.
  autounfold; intros.
  match goal with
  | H: In _ _ \/ In _ _ |- _ =>
    destruct H; eauto using in_or_app
  end.
  Unshelve.
  all:exact None.
Qed.
Hint Resolve live_node_in_msg_succ_lists_app_r.

Lemma live_node_in_msg_succ_lists_app_cons :
  forall gst x xs,
    live_node_in_msg_succ_lists' gst (x :: xs) ->
    live_node_in_msg_succ_lists' gst xs.
Proof.
  autounfold; intros.
  simpl in *; intuition eauto.
  Unshelve.
  all:exact None.
Qed.
Hint Resolve live_node_in_msg_succ_lists_app_cons.

Lemma live_node_in_msg_succ_lists_app_cons_split :
  forall gst x xs,
    live_node_in_msg_succ_lists' gst [x] ->
    live_node_in_msg_succ_lists' gst xs ->
    live_node_in_msg_succ_lists' gst (x :: xs).
Proof.
  autounfold; intros.
  simpl in *; intuition eauto.
  Unshelve.
  all:exact None.
Qed.
Hint Resolve live_node_in_msg_succ_lists_app_cons_split.

Theorem live_node_invariant_start :
  chord_start_invariant (fun gst => live_node_in_succ_lists gst /\
                                 live_node_in_msg_succ_lists gst).
Proof.
  do 2 autounfold_one; intros.
  repeat split; break_and.
  - unfold live_node_in_succ_lists in *.
    intros; repeat split.
    repeat find_rewrite.
    update_destruct; subst; rewrite_update.
    + inv_prop live_node; expand_def.
      repeat find_rewrite; rewrite_update; repeat find_injection.
      find_eapply_lem_hyp joining_start_handler_st_joined.
      congruence.
    + break_and.
      eapply_lem_prop_hyp adding_nodes_did_not_affect_live_node live_node; eauto.
      find_apply_hyp_hyp.
      break_exists_exists.
      eapply adding_nodes_does_not_affect_best_succ; eauto.
  - autounfold_one.
    find_rewrite; apply live_node_in_msg_succ_lists_app; autounfold; intros.
    + exfalso.
      unfold start_handler in *; simpl in *; find_injection.
      unfold send in *; simpl in *.
      intuition congruence.
    + simpl in *; break_and.
      assert (Exists (live_node gst) (map addr_of (chop_succs (make_pointer src :: succs)))).
      {
        eapply_prop live_node_in_msg_succ_lists; eauto.
        break_or_hyp; try tauto.
        break_exists; break_and.
        repeat find_rewrite; update_destruct; rewrite_update;
          [find_apply_lem_hyp joining_start_handler_st_joined; congruence|eauto].
      }
      find_apply_lem_hyp Exists_exists; apply Exists_exists; break_exists_exists.
      break_and; eauto using live_before_start_stays_live.
Qed.
Hint Resolve live_node_invariant_start.

Theorem live_node_invariant_fail :
  chord_fail_invariant (fun gst => live_node_in_succ_lists gst /\
                                live_node_in_msg_succ_lists gst).
Proof.
  autounfold.
  intros.
  break_and.
  split; inv_prop failure_constraint; tauto.
Qed.
Hint Resolve live_node_invariant_fail.

Theorem zave_invariant_recv_live_node_in_succ_lists :
  chord_recv_handler_pre_post
    (fun gst => live_node_in_succ_lists gst /\
             live_node_in_msg_succ_lists gst)
    live_node_in_succ_lists.
Proof.
  autounfold_one; intros.
  cbn in *; break_and.
  unfold live_node_in_succ_lists; intros.
  repeat find_rewrite.
  update_destruct; rewrite_update.
  - symmetry in e; subst.
    find_injection.
    destruct (list_eq_dec pointer_eq_dec (succ_list st) (succ_list st0)).
    + assert (exists s, best_succ gst h s).
      {
        find_eapply_prop live_node_in_succ_lists; eauto.
        destruct (joined st) eqn:?;
          try solve [break_live_node; eapply live_node_characterization; eauto].
        break_live_node; repeat find_rewrite; rewrite_update; find_injection.
        exfalso; eapply recv_handler_setting_joined_makes_succ_list_nonempty; eauto.
        repeat find_reverse_rewrite.
        eapply nodes_not_joined_have_no_successors; eauto.
      }
      break_exists_exists.
      eapply best_succ_preserved; eauto.
      eauto using joined_preserved_by_recv_handler.
    + find_copy_apply_lem_hyp recv_handler_updating_succ_list; auto; expand_def.
      * handler_def.
        simpl in *; repeat find_rewrite.
        break_if; try congruence.
        assert (succ_list x8 = chop_succs ((make_pointer (addr_of x)) :: x2))
          by repeat (handler_def || find_injection || congruence || auto).
        find_apply_lem_hyp handle_query_res_definition; expand_def;
          try congruence;
          try inv_prop request_payload;
          try find_injection;
          try solve [handler_def].
        assert (Exists (live_node gst) (map addr_of (chop_succs ((make_pointer (addr_of x)) :: x13)))).
        {
          find_eapply_prop live_node_in_msg_succ_lists; eauto.
          repeat find_rewrite; constructor 2; in_crush.
          find_eapply_lem_hyp stabilize_target_joined; eauto.
        }
        find_apply_lem_hyp Exists_exists; break_exists.
        break_and.
        assert (live_node gst' x0).
        {
          break_live_node.
          destruct (addr_eq_dec x0 h).
          - eapply live_node_characterization; repeat find_rewrite; rewrite_update; eauto.
            find_apply_lem_hyp joined_preserved_by_do_delayed_queries.
            find_apply_lem_hyp joined_preserved_by_handle_stabilize.
            congruence.
          - eapply live_node_characterization; repeat find_rewrite; rewrite_update; eauto.
        }
        (* we know there's a live node in succ_list x8, so there's got to be
           a best_succ as well *)
        eapply live_node_in_succs_best_succ; eauto.
        -- solve [econstructor; eauto].
        -- repeat find_rewrite; rewrite_update; eauto.
        -- repeat find_rewrite; auto.
      * handler_def.
        simpl in *; repeat find_rewrite.
        break_if; try congruence.
        assert (succ_list x7 = chop_succs ((make_pointer (addr_of x)) :: x2)).
        {
          repeat (handler_def || find_injection || congruence || auto || simpl);
            unfold make_succs; try solve [simpl in *; congruence].
          - find_copy_eapply_lem_hyp stabilize2_param_matches; eauto; subst.
            find_eapply_lem_hyp cur_request_valid; eauto.
            rewrite <- wf_ptr_eq; eauto.
          - find_copy_eapply_lem_hyp join2_param_matches; eauto; subst.
            find_eapply_lem_hyp cur_request_valid; eauto.
            rewrite <- wf_ptr_eq; eauto.
        }
        assert (Exists (live_node gst)
                       (map addr_of (chop_succs (make_pointer (addr_of x) :: x2)))).
        {
          eapply_prop live_node_in_msg_succ_lists;
            try solve [repeat find_rewrite; right; in_crush].
          repeat (handler_def || handler_simpl).
          - find_copy_eapply_lem_hyp stabilize2_param_matches; eauto; subst.
            find_eapply_lem_hyp stabilize2_target_joined; eauto.
          - find_copy_eapply_lem_hyp join2_param_matches; eauto; subst.
            find_eapply_lem_hyp join2_target_joined; eauto.
        }
        find_apply_lem_hyp Exists_exists; break_exists_name l.
        break_and.
        assert (live_node gst' l).
        {
          break_live_node.
          destruct (addr_eq_dec l h).
          - eapply live_node_characterization; repeat find_rewrite; rewrite_update; eauto.
            find_apply_lem_hyp joined_preserved_by_do_delayed_queries.
            find_apply_lem_hyp joined_preserved_by_handle_query;
              congruence.
          - eapply live_node_characterization; repeat find_rewrite; rewrite_update; eauto.
        }
        eapply live_node_in_succs_best_succ; eauto.
        -- solve [econstructor; eauto].
        -- repeat find_rewrite; rewrite_update; eauto.
        -- repeat find_rewrite; eauto.
  - assert (live_node gst h0).
    break_live_node; repeat find_rewrite; rewrite_update; eauto using live_node_characterization.
    assert (exists s : addr, best_succ gst h0 s) by eauto.
    break_exists_exists.
    eapply best_succ_preserved; try find_eapply_prop update; eauto.
    eauto using joined_preserved_by_recv_handler.
Unshelve.
all:exact None.
Qed.
Hint Resolve zave_invariant_recv_live_node_in_succ_lists.

Theorem zave_invariant_recv_live_node_in_msg_succ_lists :
  chord_recv_handler_pre_post
    (fun gst => live_node_in_succ_lists gst /\
             live_node_in_msg_succ_lists gst)
    live_node_in_msg_succ_lists.
Proof.
  autounfold_one; intros.
  cbn in *; break_and.
  assert (reachable_st gst') by (econstructor; eauto).
  pose proof (joined_preserved_by_recv_handler _ _ _ _ _ _ _ _ ltac:(eauto)).
  handler_def.
  unfold live_node_in_msg_succ_lists in *.
  repeat find_rewrite.
  rewrite map_app.
  apply live_node_in_msg_succ_lists_app;
    [apply live_node_in_msg_succ_lists_app|].
  - autounfold; intros.
    repeat match goal with
           | H: In _ _ \/ In _ _ |- _ =>
             destruct H
           | H: In _ (map (send _) _) |- _ =>
             rewrite -> in_map_iff in H;
               destruct H as [? [? ?]]
           | H: send ?h _ = _ |- _ =>
             unfold send in H;
               injc H
           | H: In (_, GotPredAndSuccs _ _) _ |- _ =>
             eapply handle_delayed_queries_GotPredAndSuccs_response_accurate in H; eauto;
               destruct H; subst
           | H: In (_, GotSuccList _) _ |- _ =>
             eapply handle_delayed_queries_GotSuccList_response_accurate in H; eauto; subst
           | |- Exists (live_node ?gst')
                      (map addr_of (chop_succs (make_pointer ?h :: _))) =>
             apply Exists_exists; exists (addr_of (make_pointer h));
               split; eauto using in_map;
                 simpl in *; eapply live_node_characterization;
                   [repeat find_rewrite; rewrite_update; eauto
                   |break_or_hyp
                   |congruence
                   |congruence]
           | H: exists _, _ /\ joined _ = true |- _ =>
             destruct H as [? [? ?]];
               repeat find_rewrite; rewrite_update;
                 find_injection; auto
           | H : length (succ_list ?st) > 0 |- _ =>
             destruct (joined st) eqn:?; try congruence;
               find_eapply_lem_hyp (nodes_not_joined_have_no_successors gst');
               [repeat find_rewrite; simpl in *; omega
               |auto
               |repeat find_rewrite; now rewrite_update]
           end.
  - find_copy_apply_lem_hyp succ_list_preserved_by_do_delayed_queries.
    find_apply_lem_hyp joined_preserved_by_do_delayed_queries.
    repeat handler_def; simpl;
      try match goal with
          | |- live_node_in_msg_succ_lists' gst' [_] =>
            autounfold; intros;
              break_or_hyp; in_crush; unfold send in *; try congruence
          | |- live_node_in_msg_succ_lists' gst' [] =>
            autounfold; intros; simpl in *; tauto
          end.
    autounfold; intros.
    repeat match goal with
           | H: In _ _ \/ In _ _ |- _ =>
             destruct H
           | H: In _ (map (send _) _) |- _ =>
             rewrite -> in_map_iff in H;
               destruct H as [? [? ?]]
           | H: send ?h _ = _ |- _ =>
             unfold send in H; injc H
           | H: In (_, GotPredAndSuccs _ _) _ |- _ =>
             eapply handle_query_req_GotPredAndSuccs_response_accurate in H; eauto;
               destruct H; subst
           | H: In (_, GotSuccList _) _ |- _ =>
             eapply handle_query_req_GotSuccList_response_accurate in H; eauto; subst
           | |- Exists (live_node ?gst')
                      (map addr_of (chop_succs (make_pointer ?h :: _))) =>
             apply Exists_exists; exists (addr_of (make_pointer h));
               split; eauto using in_map;
                 simpl in *; eapply live_node_characterization;
                   [repeat find_rewrite; rewrite_update; eauto
                   |break_or_hyp
                   |congruence
                   |congruence]
           | H: exists _, _ /\ joined _ = true |- _ =>
             destruct H as [? [? ?]];
               repeat find_rewrite; rewrite_update;
                 find_injection; auto
           | H : length (succ_list ?st) > 0,
                 H': succ_list ?st = succ_list ?st'
             |- _ =>
             destruct (joined st) eqn:?; auto;
               destruct (joined st') eqn:?; auto;
               find_eapply_lem_hyp (nodes_not_joined_have_no_successors gst' ltac:(auto) src0 st');
               solve [replace (succ_list st) with (@nil pointer) in H21; [simpl in *; omega|congruence]
                     |repeat find_rewrite; now rewrite_update]
           end.
  - assert (live_node_in_msg_succ_lists' gst (xs ++ ys)) by eauto.
    autounfold in *; intros.
    repeat find_rewrite.
    update_destruct; rewrite_update; eauto; subst; break_or_hyp;
      try solve [apply Exists_exists; exists (addr_of (make_pointer src0));
                 break_exists; break_and;
                 find_injection;
                 split; auto using in_map;
                 eapply live_node_characterization; repeat find_rewrite; simpl; try congruence;
                 rewrite_update; auto];
    assert (Exists (live_node gst) (map addr_of (chop_succs (make_pointer src0 :: succs))))
      by eauto;
    find_apply_lem_hyp Exists_exists; apply Exists_exists; break_exists_exists;
    break_and; split; eauto;
      break_live_node;
      match goal with
      | H: sigma gst' = update _ _ ?h (Some ?st) |- _ =>
        destruct (addr_eq_dec h x7);
          [subst; eapply live_node_characterization;
           repeat find_rewrite; rewrite_update; find_injection; eauto
          |eapply live_node_characterization; repeat find_rewrite; rewrite_update; eauto]
      end.
Qed.
Hint Resolve zave_invariant_recv_live_node_in_msg_succ_lists.
Theorem live_node_invariant_tick_live_node_in_succ_lists :
  chord_tick_pre_post
    (fun gst => live_node_in_succ_lists gst /\
             live_node_in_msg_succ_lists gst)
    live_node_in_succ_lists.
Proof.
  autounfold_one; intros.
  simpl in *; break_and.
  unfold live_node_in_succ_lists; intros.
  find_copy_apply_lem_hyp joined_preserved_by_tick_handler.
  assert (succ_list st' = succ_list st)
    by now repeat handler_def.
  assert (exists s, best_succ gst h0 s).
  {
    repeat find_rewrite; update_destruct; rewrite_update; try find_injection;
      eapply_prop live_node_in_succ_lists; eauto;
        break_live_node; eapply live_node_characterization; eauto;
          repeat find_rewrite; rewrite_update; congruence.
  }
  break_exists_exists; eapply best_succ_preserved; eauto.
Qed.
Hint Resolve live_node_invariant_tick_live_node_in_succ_lists.


Theorem live_node_invariant_tick_live_node_in_msg_succ_lists :
  chord_tick_pre_post
    (fun gst => live_node_in_succ_lists gst /\
             live_node_in_msg_succ_lists gst)
    live_node_in_msg_succ_lists.
Proof.
  autounfold_one; intros.
  simpl in *; break_and.
  unfold live_node_in_msg_succ_lists; repeat find_rewrite.
  apply live_node_in_msg_succ_lists_app; autounfold; intros.
  - exfalso; repeat handler_def; unfold send in *; simpl in *;
      find_apply_lem_hyp option_map_Some; expand_def; congruence.
  - assert (Exists (live_node gst) (map addr_of (chop_succs (make_pointer src :: succs)))).
    {
      eapply_prop live_node_in_msg_succ_lists; eauto.
      repeat find_rewrite.
      break_or_hyp; auto.
      right.
      break_exists; break_and.
      update_destruct; rewrite_update; subst; try solve [eexists; eauto].
      exists st.
      split; auto; find_injection.
      erewrite -> joined_preserved_by_tick_handler; eauto.
    }
    apply Exists_exists; find_apply_lem_hyp Exists_exists; break_exists_exists.
    break_and; split; auto.
    eapply live_node_preserved_by_tick; eauto.
Qed.
Hint Resolve live_node_invariant_tick_live_node_in_msg_succ_lists.

Theorem live_node_invariant_keepalive :
  chord_keepalive_invariant
    (fun gst => live_node_in_succ_lists gst /\
             live_node_in_msg_succ_lists gst).
Proof.
  do 2 autounfold_one; simpl; intuition;
    unfold live_node_in_msg_succ_lists, live_node_in_succ_lists; intros.
  - handler_def.
    assert (exists s, best_succ gst h0 s).
    {
      repeat find_rewrite; update_destruct; rewrite_update; try find_injection;
        eapply_prop live_node_in_succ_lists; eauto;
          break_live_node; eapply live_node_characterization; eauto;
            repeat find_rewrite; rewrite_update; congruence.
    }
    break_exists_exists; eapply best_succ_preserved; eauto.
  - repeat find_rewrite.
    apply live_node_in_msg_succ_lists_app; autounfold; intros.
    + repeat handler_def;
        repeat match goal with
               | H: In _ (map _ _) |- _ =>
                 erewrite in_map_iff in H; expand_def
               | H: context[send_keepalives] |- _ =>
                 unfold send_keepalives in H
               | H: send _ _ = _ |- _ =>
                 unfold send in H
               | H: (_, (_, _)) = (_, (_, _)) |- _ =>
                 congruence
               end.
    + assert (Exists (live_node gst) (map addr_of (chop_succs (make_pointer src :: succs)))).
      {
        eapply_prop live_node_in_msg_succ_lists; eauto.
        repeat find_rewrite.
        break_or_hyp; auto.
        right.
        break_exists; break_and.
        update_destruct; rewrite_update; subst; try solve [eexists; eauto].
        exists st; find_injection; auto.
        handler_def; auto.
      }
      apply Exists_exists; find_apply_lem_hyp Exists_exists; break_exists_exists.
      break_and; split; eauto.
      eapply live_node_preserved_by_keepalive; eauto.
Qed.
Hint Resolve live_node_invariant_keepalive.


Theorem live_node_invariant_rectify :
  chord_rectify_invariant
    (fun gst => live_node_in_succ_lists gst /\
             live_node_in_msg_succ_lists gst).
Proof.
  do 2 autounfold_one; simpl; intros; break_and.
  find_copy_apply_lem_hyp joined_preserved_by_do_rectify.
  assert (succ_list st = succ_list st')
    by now repeat handler_def.
  split; unfold live_node_in_msg_succ_lists, live_node_in_succ_lists; intros.
  - assert (exists s, best_succ gst h0 s).
    {
      repeat find_rewrite; update_destruct; rewrite_update; try find_injection;
        eapply_prop live_node_in_succ_lists; eauto;
          break_live_node; eapply live_node_characterization; eauto;
            repeat find_rewrite; rewrite_update; congruence.
    }
    break_exists_exists; eapply best_succ_preserved; eauto.
  - repeat find_rewrite.
    apply live_node_in_msg_succ_lists_app; autounfold; intros.
    + repeat handler_def; simpl in *; intuition;
        repeat match goal with
               | H: option_map _ _ = Some _ |- _ =>
                 apply option_map_Some in H; destruct H as [? [? ?]]
               | H: In _ (map _ _) |- _ =>
                 erewrite in_map_iff in H; expand_def
               | H: context[send_keepalives] |- _ =>
                 unfold send_keepalives in H
               | H: send _ _ = _ |- _ =>
                 unfold send in H
               | H: (_, (_, _)) = (_, (_, _)) |- _ =>
                 congruence
               end.
    + assert (Exists (live_node gst) (map addr_of (chop_succs (make_pointer src :: succs)))).
      {
        eapply_prop live_node_in_msg_succ_lists; eauto.
        repeat find_rewrite.
        break_or_hyp; auto.
        right.
        break_exists; break_and.
        update_destruct; rewrite_update; subst; try solve [eexists; eauto].
        exists st; find_injection; auto.
        handler_def; auto.
      }
      apply Exists_exists; find_apply_lem_hyp Exists_exists; break_exists_exists.
      break_and; split; eauto.
      eapply live_node_preserved_by_rectify; eauto.
Qed.
Hint Resolve live_node_invariant_rectify.

Theorem live_node_invariant_request :
  chord_request_invariant
    (fun gst => live_node_in_succ_lists gst /\
             live_node_in_msg_succ_lists gst).
Proof.
  do 2 autounfold_one; simpl; intros; break_and.
  assert (joined st' = joined st) by (symmetry; eauto).
  find_copy_apply_lem_hyp joined_preserved_by_request_timeout_handler.
  split; unfold live_node_in_msg_succ_lists, live_node_in_succ_lists; intros.
  - assert (exists s, best_succ gst h0 s).
    {
      repeat find_rewrite; update_destruct; rewrite_update; try find_injection;
        eapply_prop live_node_in_succ_lists; eauto;
          break_live_node; eapply live_node_characterization; eauto;
            repeat find_rewrite; rewrite_update; congruence.
    }
    subst; inv_prop timeout_constraint.
    break_exists_name best.
    inv_prop best_succ; break_exists; break_and.
    destruct (addr_eq_dec best dst); subst.
    + break_live_node; tauto.
    + assert (In best (map addr_of (succ_list x)))
        by (repeat find_rewrite; in_crush).
      assert (In best (map addr_of (succ_list st0))).
      {
        repeat find_rewrite; update_destruct; rewrite_update;
          repeat (find_rewrite || find_injection).
        - find_copy_eapply_lem_hyp cur_request_timeouts_related_invariant; auto.
          repeat find_reverse_rewrite.
          repeat handler_def; simpl in *; try congruence.
          + repeat find_rewrite.
            inv_prop cur_request_timeouts_ok; try congruence; find_injection.
            inv_prop query_request.
            find_eapply_lem_hyp stabilize_only_with_first_succ; eauto.
            break_exists; break_and.
            repeat find_rewrite; simpl in *; repeat find_injection.
            assert (In best (addr_of x2 :: map addr_of x13)) by congruence.
            in_crush.
          + simpl in *.
            find_apply_lem_hyp option_map_None.
            find_apply_lem_hyp hd_error_None; subst.
            inv_prop cur_request_timeouts_ok; try congruence.
            repeat find_rewrite; repeat find_injection.
            inv_prop query_request.
            find_eapply_lem_hyp stabilize_only_with_first_succ; eauto.
            break_exists; break_and.
            repeat find_rewrite; simpl in *; repeat find_injection.
            assert (exists s, best_succ gst h0 s).
            eapply_prop live_node_in_succ_lists; eauto.
            break_exists; inv_prop best_succ; expand_def.
            repeat (find_rewrite || find_injection); simpl in *.
            match goal with
            | H: context[app] |- _ =>
              symmetry in H;
                apply app_cons_singleton_inv in H;
                destruct H as [? [? ?]];
                subst
            end.
            break_live_node.
            tauto.
        - auto.
      }
      assert (live_node gst' best)
        by (eapply live_node_preserved_by_request; eauto).
      eapply live_node_in_succs_best_succ;
        solve [eauto
              |econstructor; eauto].
  - repeat find_rewrite.
    apply live_node_in_msg_succ_lists_app; autounfold; intros.
    + repeat handler_def; simpl in *; intuition;
        repeat match goal with
               | H: option_map _ _ = Some _ |- _ =>
                 apply option_map_Some in H; destruct H as [? [? ?]]
               | H: In _ (concat _) |- _ =>
                 apply in_concat in H; expand_def
               | H: In _ (map _ _) |- _ =>
                 erewrite in_map_iff in H; expand_def
               | H: context[send_keepalives] |- _ =>
                 unfold send_keepalives in H
               | H: send _ _ = _ |- _ =>
                 unfold send in H
               | H: (_, _) = (_, _) |- _ =>
                 injc H
               end.
      all:admit.
    + assert (Exists (live_node gst) (map addr_of (chop_succs (make_pointer src :: succs)))).
      {
        eapply_prop live_node_in_msg_succ_lists; eauto.
        repeat find_rewrite.
        break_or_hyp; auto.
        right.
        break_exists; break_and.
        update_destruct; rewrite_update; subst; try solve [eexists; eauto].
        exists st; find_injection; eauto.
      }
      apply Exists_exists; find_apply_lem_hyp Exists_exists; break_exists_exists.
      break_and; split; eauto.
      eapply live_node_preserved_by_request; subst; eauto.
Admitted.
Hint Resolve live_node_invariant_request.

Theorem live_node_invariant_output :
  chord_output_invariant
    (fun gst => live_node_in_succ_lists gst /\
             live_node_in_msg_succ_lists gst).
Proof.
  unfold chord_output_invariant, chord_output_pre_post; intros; break_and.
  unfold send in *; subst.
  split.
  - unfold live_node_in_succ_lists; intros.
    simpl in *.
    assert (exists s, best_succ gst h s) by eauto.
    break_exists_exists; eauto using coarse_best_succ_characterization.
  - autounfold_one; simpl.
    eapply live_node_in_msg_succ_lists_app; autounfold; intros;
      assert (Exists (live_node gst) (map addr_of (chop_succs (make_pointer src :: succs))))
      by (eapply_prop live_node_in_msg_succ_lists; repeat find_rewrite;
          intuition eauto with datatypes);
      apply Exists_exists; find_apply_lem_hyp Exists_exists; break_exists_exists; tauto.
Qed.
Hint Resolve live_node_invariant_output.

Theorem live_node_invariant_input :
  chord_input_invariant
    (fun gst => live_node_in_succ_lists gst /\
             live_node_in_msg_succ_lists gst).
Proof.
  unfold chord_input_invariant, chord_input_pre_post; intros; break_and.
  unfold send in *; subst.
  split.
  - unfold live_node_in_succ_lists; intros.
    simpl in *.
    assert (exists s, best_succ gst h0 s) by eauto.
    break_exists_exists; eauto using coarse_best_succ_characterization.
  - autounfold_one; simpl.
    eapply live_node_in_msg_succ_lists_app_cons_split; autounfold; intros.
    + inv_prop client_payload; simpl in *; intuition congruence.
    + assert (Exists (live_node gst) (map addr_of (chop_succs (make_pointer src :: succs))))
        by eauto.
      apply Exists_exists; find_apply_lem_hyp Exists_exists; break_exists_exists; tauto.
Qed.
Hint Resolve live_node_invariant_input.

Theorem live_node_invariant_holds :
  forall gst,
    reachable_st gst ->
    live_node_in_succ_lists gst /\
    live_node_in_msg_succ_lists gst.
Proof.
  apply chord_net_invariant;
    solve [eauto
          |autounfold_one; eauto].
Qed.
Hint Resolve live_node_invariant_holds.
