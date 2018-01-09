Require Import List.
Import ListNotations.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Omega.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.
Require Import Chord.HashInjective.
Require Import Chord.NodesHaveState.
Require Import Chord.PairIn.
Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemPointers.
Require Import Chord.ValidPointersInvariant.
Require Import Chord.SuccessorNodesAlwaysValid.
Require Import Chord.NodesNotJoinedHaveNoSuccessors.
Require Import Chord.QueryTargetsJoined.
Require Import Chord.QueryInvariant.
Require Import Chord.LiveNodeInSuccLists.
Require Import Chord.LiveNodePreservation.
Require Import Chord.StabilizeOnlyWithFirstSucc.
Require Import Chord.WfPtrSuccListInvariant.

Set Bullet Behavior "Strict Subproofs".

Definition sufficient_principals (gst : global_state) : Prop :=
  exists ps,
    principals gst ps /\
    length ps > SUCC_LIST_LEN.
Hint Unfold sufficient_principals.

Definition have_principals (gst : global_state) (n : nat) : Prop :=
  exists ps,
    NoDup ps /\
    Forall (principal gst) ps /\
    length ps >= n.

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

Fixpoint not_skipped_bool (h : id) (succs : list id) (n : id) :=
  match succs with
  | [] => true
  | a :: succs' =>
    if between_bool h n a then
      false
    else
      not_skipped_bool a succs' n
  end.

Lemma not_skipped_initial :
  forall h x succs n,
    not_skipped h (x :: succs) n ->
    not_skipped x succs n.
Proof.
  intros.
  unfold not_skipped. intros.
  match goal with
  | H : not_skipped _ _ _ |- _ =>
    specialize (H a b (h :: xs) ys)
  end.
  simpl in *. repeat find_rewrite. intuition.
Qed.


Lemma not_skipped_initial' :
  forall h x succs n,
    not_skipped x succs n ->
    ~ between h n x ->
    not_skipped h (x :: succs) n.
Proof.
  intros.
  unfold not_skipped. intros.
  destruct xs.
  - simpl in *. find_inversion. auto.
  - simpl in *. find_inversion. unfold not_skipped in *. simpl in *. eauto.
Qed.

Lemma not_skipped_not_skipped_bool :
  forall succs h n,
    not_skipped h succs n ->
    not_skipped_bool h succs n = true.
Proof.
  induction succs;
    intros; simpl in *; auto.
  break_match; auto.
  - exfalso.
    match goal with
    | H : not_skipped _ _ _ |- _ =>
      specialize (H h a [] succs)
    end.
    simpl in *. intuition.
    eauto using between_bool_between.
  - eauto using not_skipped_initial.
Qed.

Lemma not_skipped_bool_not_skipped :
  forall succs h n,
    not_skipped_bool h succs n = true ->
    not_skipped h succs n.
Proof.
  induction succs;
    intros; simpl in *; auto.
  - unfold not_skipped. intros.
    destruct xs; simpl in *; try congruence.
    destruct xs; simpl in *; try congruence.
  - break_match; try congruence.
    find_apply_hyp_hyp. eapply not_skipped_initial'; eauto.
Qed.

Definition forallb_exists :
  forall A f (l : list A),
    forallb f l = false ->
    exists x,
      In x l /\ f x = false.
Proof.
  intros. induction l; simpl in *; try congruence.
  do_bool. intuition eauto.
  break_exists_exists. intuition.
Qed.

Definition principal_dec :
  forall gst h,
    {principal gst h} + {~ principal gst h}.
Proof.
  intros.
  destruct (live_node_dec gst h).
  - destruct (forallb (fun h' => match sigma gst h' with
                              | Some st => not_skipped_bool (hash h')
                                                           (map id_of (succ_list st)) (hash h)
                              | None => true
                              end) (live_addrs gst)) eqn:?.
    + left. unfold principal. intuition.
      find_eapply_lem_hyp forallb_forall; eauto using live_addr_In_live_addrs.
      repeat find_rewrite. eauto using not_skipped_bool_not_skipped.
    + right. intro. find_apply_lem_hyp forallb_exists.
      break_exists. intuition. find_apply_lem_hyp In_live_addrs_live.
      break_match; try congruence.
      unfold principal in *.
      intuition.
      eapply_prop_hyp live_node sigma; eauto.
      eauto using not_skipped_not_skipped_bool.
  - right. intuition. unfold principal in *. intuition.
Defined.

Definition compute_principals (gst : global_state) : list addr :=
  dedup
    addr_eq_dec
    (filter
       (fun h => ssrbool.is_left (principal_dec gst h))
       (nodes gst)).

Lemma compute_principals_correct :
  forall gst,
    principals gst (compute_principals gst).
Proof.
  unfold compute_principals, principals.
  repeat split; [now eapply NoDup_dedup|apply Forall_forall|]; intros.
  - find_eapply_lem_hyp in_dedup_was_in.
    find_eapply_lem_hyp filter_In; break_and.
    destruct (principal_dec gst x);
      simpl in *; congruence.
  - apply dedup_In.
    apply filter_In; split.
    + inv_prop principal.
      now inv_prop live_node.
    + destruct (principal_dec gst p);
        simpl in *; congruence.
Qed.

Lemma some_principals_ok :
  forall gst,
    have_principals gst (SUCC_LIST_LEN + 1) ->
    sufficient_principals gst.
Proof.
  intros.
  inv_prop have_principals; break_and.
  pose proof (compute_principals_correct gst).
  inv_prop principals; break_and.
  assert (incl x (compute_principals gst)).
  {
    unfold incl; intros.
    rewrite -> ?Forall_forall in *; eauto.
  }
  find_eapply_lem_hyp NoDup_incl_length; auto.
  eexists.
  split; eauto; omega.
Qed.

Definition zave_invariant (gst : global_state) : Prop :=
  sufficient_principals gst /\
  live_node_in_succ_lists gst /\
  live_node_in_msg_succ_lists gst.
Hint Unfold zave_invariant.

Lemma initial_succ_lists_all_principal :
  forall p l,
    In p l ->
    forall h a b,
      pair_in a b (hash h :: map id_of (find_succs h (sort_by_between h (map make_pointer l)))) ->
      ~ between a (hash p) b.
Proof.
  intros.
  rewrite initial_esl_is_sorted_nodes_chopped in H0.
  pose proof (sorted_list_chopped_elements_not_between (make_pointer p) (map make_pointer (h :: l))).
  forwards. apply in_map; auto with datatypes. concludes.
  find_apply_lem_hyp pair_in_map; expand_def.
  change (hash p) with (id_of (make_pointer p)).
  unfold not in *; eauto.
Qed.
Hint Resolve initial_succ_lists_all_principal.

Lemma initial_nodes_principal :
  forall gst h,
    initial_st gst ->
    In h (nodes gst) ->
    principal gst h.
Proof.
  intros.
  unfold principal; split.
  - auto.
  - unfold not_skipped; intros.
    find_apply_lem_hyp initial_succ_list; eauto.
    repeat find_rewrite; repeat find_injection.
    simpl in *; eauto.
Qed.
Hint Resolve initial_nodes_principal.

Lemma principals_intro :
  forall gst ps,
    NoDup ps ->
    (forall p, In p ps -> principal gst p) ->
    (forall p, principal gst p -> In p ps) ->
    principals gst ps.
Proof.
  unfold principals.
  intros.
  intuition (apply Forall_forall; auto).
Qed.

Lemma sufficient_principals_intro :
  forall gst ps,
    NoDup ps ->
    (forall p, In p ps -> principal gst p) ->
    (forall p, principal gst p -> In p ps) ->
    length ps > SUCC_LIST_LEN ->
    sufficient_principals gst.
Proof.
  unfold sufficient_principals.
  intros; exists ps.
  eauto using principals_intro.
Qed.

Lemma principals_involves_joined_node_state_only :
  forall gst gst' p,
    principal gst p ->
    (forall h st,
        live_node gst h /\ sigma gst h = Some st <->
        live_node gst' h /\ sigma gst' h = Some st) ->
    principal gst' p.
Proof.
  unfold principal.
  intros.
  expand_def.
  split.
  - firstorder.
  - intros.
    assert ((forall h, live_node gst h -> live_node gst' h) /\
            (forall h, live_node gst' h -> live_node gst h)).
    {
      split; intros;
        inv_prop live_node;
        expand_def;
        eapply H0;
        split; eauto.
    }
    break_and.
    eapply H1; eauto.
    eapply H0; split; eauto.
Qed.

Theorem zave_invariant_init :
  chord_init_invariant zave_invariant.
Proof.
  autounfold; intros.
  inv_prop initial_st.
  repeat split.
  - break_and.
    unfold sufficient_principals.
    exists (nodes gst); split; try omega.
    unfold principals; repeat split.
    + auto.
    + apply Forall_forall; eauto.
    + intros; inv_prop principal; auto.
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
         assert (In p (find_succs h (sort_by_between h (map make_pointer (nodes gst)))))
           by (cut (In p (p :: l)); [congruence | auto with datatypes]).
         find_apply_lem_hyp in_find_succs.
         find_apply_lem_hyp in_sort_by_between.
         find_apply_lem_hyp in_map_iff; expand_def.
         easy.
  - autounfold; break_and; find_rewrite; in_crush.
Qed.
Hint Resolve zave_invariant_init.

Lemma live_after_start_was_live :
  forall h gst gst' k st ms nts,
    ~ In h (nodes gst) ->
    In k (nodes gst) ->
    ~ In k (failed_nodes gst) ->
    start_handler h [k] = (st, ms, nts) ->
    nodes gst' = h :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' = update addr_eq_dec (timeouts gst) h nts ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st) ->
    msgs gst' = map (send h) ms ++ msgs gst ->
    trace gst' = trace gst ++ map e_send (map (send h) ms) ->
    forall l,
      live_node gst' l ->
      live_node gst l.
Proof.
  intros.
  inv_prop live_node; expand_def.
  assert (l <> h) by eauto using live_node_not_just_started.
  eapply live_node_characterization; eauto; repeat find_rewrite;
    solve [now rewrite_update | in_crush].
Qed.

Theorem zave_invariant_start :
  chord_start_invariant zave_invariant.
Proof.
  unfold chord_start_invariant, zave_invariant.
  repeat apply chord_start_pre_post_conj; eauto.
  do 2 autounfold_one; intros; break_and.
  unfold sufficient_principals in *; break_and.
  break_exists_exists.
  break_and; split; eauto.
  inv_prop principals; break_and.
  apply principals_intro; auto; intros.
  - inv_prop principals; expand_def.
    eapply principals_involves_joined_node_state_only; eauto.
    eapply Forall_forall; eauto.
    intros.
    intuition; inv_prop live_node; expand_def.
    + eapply live_node_characterization; eauto;
        repeat find_rewrite;
        try rewrite_update;
        in_crush || eauto.
    + repeat find_rewrite; rewrite_update; auto.
    + repeat find_rewrite; update_destruct;
        subst; rewrite_update;
          repeat find_injection.
      cut (joined x0 = false); [congruence|].
      eapply joining_start_handler_st_joined; eauto.
      eapply live_node_characterization; eauto; in_crush.
    + repeat find_rewrite; update_destruct;
        subst; rewrite_update;
          repeat find_injection.
      cut (joined x0 = false); [congruence|].
      eapply joining_start_handler_st_joined; eauto.
      rewrite_update; auto.
  - find_eapply_prop In.
    inv_prop principal.
    split; eauto using live_after_start_was_live.
    intros.
    inv_prop principal.
    assert (live_node gst p) by eauto using live_after_start_was_live.
    assert (live_node gst' h0) by eauto using live_before_start_stays_live.
    inv_prop (live_node gst' h0); expand_def.
    find_eapply_prop not_skipped; eauto.
    assert (h0 <> h) by eauto using live_node_not_just_started.
    repeat find_rewrite; rewrite_update; congruence.
Qed.
Hint Resolve zave_invariant_start.

Lemma principal_preserved :
  forall gst gst',
    nodes gst = nodes gst' ->
    (forall f,
        In f (failed_nodes gst) ->
        In f (failed_nodes gst')) ->
    sigma gst = sigma gst' ->
    forall h,
      principal gst h ->
      ~ In h (failed_nodes gst') ->
      principal gst' h.
Proof.
  intros.
  unfold principal in *; split; intros.
  - break_and.
    inv_prop live_node; expand_def.
    repeat find_rewrite.
    eapply live_node_characterization; eauto.
  - subst.
    inv_prop live_node; expand_def.
    find_rewrite; find_injection.
    find_eapply_prop not_skipped; repeat find_rewrite; eauto.
    eapply live_node_characterization; repeat find_rewrite; eauto.
Qed.

Lemma principal_not_failed :
  forall gst h,
    principal gst h ->
    In h (failed_nodes gst) ->
    False.
Proof.
  unfold principal.
  intros until 1.
  fold (~ In h (failed_nodes gst)).
  break_and.
  eauto.
Qed.
Hint Resolve principal_not_failed.

Lemma succ_lists_same_principal_preserved :
  forall gst gst' h p st st',
    principal gst p ->
    sigma gst h = Some st ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    succ_list st = succ_list st' ->
    joined st = joined st' ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    principal gst' p.
Proof.
  unfold principal.
  intuition eauto.
  - assert (live_node gst p) by eauto.
    break_live_node.
    destruct (addr_eq_dec p h);
      eapply live_node_characterization; repeat find_rewrite; rewrite_update; eauto.
    congruence.
  - subst.
    repeat find_rewrite; update_destruct; rewrite_update.
    + find_injection.
      find_reverse_rewrite.
      eapply H7; eauto.
      break_live_node;
        rewrite_update;
        eapply live_node_characterization; repeat find_rewrite; eauto.
      rewrite_update. congruence.
    + assert (live_node gst h0).
      {
        break_live_node; eapply live_node_characterization; repeat find_rewrite; eauto.
        rewrite_update; congruence.
      }
      eauto.
Qed.
Hint Resolve succ_lists_same_principal_preserved.

Theorem zave_invariant_fail :
  chord_fail_invariant zave_invariant.
Proof.
  autounfold.
  intros.
  eapply chord_fail_pre_post_conj; eauto.
  autounfold; intros; break_and.
  inv_prop failure_constraint.
  unfold principal_failure_constraint in *.
  unfold sufficient_principals in *.
  break_and.
  eapply some_principals_ok.
  destruct (principal_dec gst h).
  - concludes.
    break_exists_name ps; break_and.
    exists (remove addr_eq_dec h ps); repeat split.
    + inv_prop principals; auto using remove_NoDup.
    + inv_prop principals.
      pose proof (principal_preserved gst gst').
      econcludes.
      forwards.
      intros. repeat find_rewrite. in_crush.
      concludes.
      econcludes.
      break_and.
      rewrite -> ?Forall_forall in *; intros.
      repeat find_rewrite.
      eauto.
      find_eapply_prop principal; eauto using in_remove.
      simpl.
      destruct (addr_eq_dec h x);
        intro; break_or_hyp; try solve [eapply remove_In; eauto].
      assert (principal gst x) by eauto using in_remove.
      inv_prop principal; inv_prop live_node; tauto.
    + inv_prop principals; break_and.
      assert (length ps = SUCC_LIST_LEN + 1 -> False) by eauto.
      cut (length (remove addr_eq_dec h ps) > SUCC_LIST_LEN); [omega|].
      eapply gt_S_n.
      rewrite remove_length_in; eauto.
      omega.
  - unfold principals in * |- ; break_exists_exists; expand_def.
    rewrite -> ?Forall_forall in *.
    assert (~ In h x) by eauto.
    split; auto.
    unfold principals in *; break_and.
    intuition eauto; try omega.
    eapply principal_preserved; try symmetry; try eassumption; eauto.
    repeat find_rewrite.
    intros.
    in_crush.
    find_rewrite.
    in_crush.
    assert (principal gst x0) by eauto.
    inv_prop principal.
    inv_prop live_node.
    tauto.
Qed.
Hint Resolve zave_invariant_fail.

Theorem zave_invariant_recv_sufficient_principals :
  chord_recv_handler_pre_post
    zave_invariant
    sufficient_principals.
Proof.
Admitted.
Hint Resolve zave_invariant_recv_sufficient_principals.

Theorem zave_invariant_recv :
  chord_recv_handler_invariant zave_invariant.
Proof.
  autounfold; eauto.
Qed.
Hint Resolve zave_invariant_recv.

Theorem zave_invariant_tick :
  chord_tick_invariant zave_invariant.
Proof.
  unfold zave_invariant.
  repeat split; eauto.
  break_and.
  unfold sufficient_principals in *.
  eapply some_principals_ok.
  break_exists_exists.
  unfold principals in *; break_and.
  repeat split; eauto; try omega.
  rewrite -> Forall_forall in *.
  intros.
  eapply succ_lists_same_principal_preserved; eauto.
  - repeat handler_def; simpl; auto.
  - eauto using joined_preserved_by_tick_handler.
Qed.
Hint Resolve zave_invariant_tick.

Theorem zave_invariant_keepalive :
  chord_keepalive_invariant zave_invariant.
Proof.
  unfold zave_invariant.
  split; eauto.
  break_and.
  unfold sufficient_principals in *.
  eapply some_principals_ok.
  break_exists_exists.
  unfold principals in *; break_and.
  repeat split; eauto; try omega.
  rewrite -> Forall_forall in *.
  intros.
  eapply succ_lists_same_principal_preserved; eauto;
    repeat handler_def; simpl; auto.
Qed.
Hint Resolve zave_invariant_keepalive.

Theorem zave_invariant_rectify :
  chord_rectify_invariant zave_invariant.
Proof.
  unfold zave_invariant.
  split; eauto.
  break_and.
  unfold sufficient_principals in *.
  eapply some_principals_ok.
  break_exists_exists.
  unfold principals in *; break_and.
  repeat split; eauto; try omega.
  rewrite -> Forall_forall in *.
  intros.
  eapply succ_lists_same_principal_preserved; eauto;
    repeat handler_def; simpl; auto.
Qed.
Hint Resolve zave_invariant_rectify.

Lemma not_skipped_initial_not_between :
  forall a b p rest,
    not_skipped a (b :: rest) p ->
    ~ between a p b.
Proof.
  intros.
  unfold not_skipped in *.
  eauto.
  specialize (H a b [] rest). simpl in *. auto.
Qed.

Lemma remove_list_element_still_not_skipped :
  forall h s rest p,
    s <> p ->
    not_skipped h (s :: rest) p ->
    not_skipped h rest p.
Proof.
  (* This is for Doug *)
  destruct rest; intros; simpl in *.
  - unfold not_skipped. intros.
    destruct xs; simpl in *; try congruence.
    destruct xs; simpl in *; congruence.
  - find_copy_apply_lem_hyp not_skipped_initial_not_between.
    find_apply_lem_hyp not_skipped_initial.
    find_copy_apply_lem_hyp not_skipped_initial_not_between.
    find_eapply_lem_hyp not_skipped_initial.
    eapply not_skipped_initial'; eauto.
    destruct (id_eq_dec h s); [subst; exfalso; intuition; eauto using between_xyx|].
    destruct (id_eq_dec s i); [subst; exfalso; intuition; eauto using between_xyx|].
    find_apply_lem_hyp not_between_cases;
      intuition; subst; eauto; try solve [find_apply_lem_hyp not_between_xyy; eauto].
    find_apply_lem_hyp not_between_cases;
      intuition; subst; eauto; try solve [find_apply_lem_hyp not_between_xxy; eauto].
    repeat invcs_prop between;
      try solve [match goal with
      | H : lt ?a ?b, H' : lt ?b ?a |- _ =>
        specialize (lt_asymm _ _ H H'); eauto
                 end].
    + repeat find_apply_lem_hyp lt_asymm_neg.
      intuition; subst; auto;
        try solve [eapply lt_asymm; eauto].
      match goal with
      | H1 : lt ?a ?b, H2 : lt ?b ?c, H3 : lt ?c ?a |- _ =>
        specialize (lt_trans _ _ _ H1 H2) as Hcontra;
          specialize (lt_asymm _ _ H3 Hcontra); eauto
      end. 
    + repeat find_apply_lem_hyp lt_asymm_neg.
      intuition; subst; auto;
        try solve [eapply lt_asymm; eauto].
      match goal with
      | H1 : lt ?a ?b, H2 : lt ?b ?c, H3 : lt ?c ?a |- _ =>
        specialize (lt_trans _ _ _ H1 H2) as Hcontra;
          specialize (lt_asymm _ _ H3 Hcontra); eauto
      end.
Qed.
Hint Resolve remove_list_element_still_not_skipped.

Theorem zave_invariant_request :
  chord_request_invariant zave_invariant.
Proof.
  autounfold; intros.
  break_and; split; eauto.
  find_copy_eapply_lem_hyp cur_request_timeouts_related_invariant; auto.
  assert (succ_list st = succ_list st' \/
          req = GetPredAndSuccs /\
          exists s1 rest,
            succ_list st = s1 :: rest /\
            succ_list st' = rest).
  {
    repeat handler_def; simpl; intuition eauto;
      repeat find_rewrite;
      invcs_prop cur_request_timeouts_ok; try congruence;
        inv_prop query_request;
        try congruence;
        assert (Request (addr_of dstp) GetPredAndSuccs = Request (addr_of x) req) by eauto;
        find_injection;
        right; intuition eauto.
  }
  break_or_hyp.
  - unfold sufficient_principals in *.
    eapply some_principals_ok.
    break_exists_exists.
    unfold principals in *; break_and.
    repeat split; eauto; try omega.
    rewrite -> Forall_forall in *.
    intros.
    eapply succ_lists_same_principal_preserved; eauto;
      repeat handler_def; simpl; auto.
  - break_and.
    unfold sufficient_principals in *.
    eapply some_principals_ok.
    break_exists_exists.
    unfold principals in *; break_and.
    repeat split; eauto; try omega.
    rewrite -> Forall_forall in *.
    intros.
    assert (principal gst x0) by eauto.
    inv_prop principal.
    break_exists_name s1; break_exists_name rest; break_and.
    assert (live_node gst h).
    {
      eapply live_node_characterization; eauto.
      destruct (joined st) eqn:?; auto.
      find_apply_lem_hyp nodes_not_joined_have_no_successors; eauto.
      congruence.
    }
    split; intuition eauto.
    + eapply live_node_preserved_by_request; eauto.
    + assert (not_skipped (ChordIDSpace.hash h)
                          (map id_of (s1 :: succ_list st'))
                          (ChordIDSpace.hash x0))
        by (find_eapply_prop not_skipped; eauto || congruence).
      repeat find_rewrite; update_destruct; rewrite_update; subst.
      * find_injection; repeat find_rewrite.
        eapply remove_list_element_still_not_skipped; eauto.
        intro.
        repeat invcs_prop principal.
        repeat break_live_node.
        repeat find_rewrite; rewrite_update; repeat find_injection.
        inv_prop timeout_constraint.
        assert (dst = addr_of s1).
        {
          eapply_lem_prop_hyp (stabilize_only_with_first_succ gst) Request; eauto.
          break_exists; break_and.
          repeat find_rewrite; simpl in *; congruence.
        }
        cut (dst = x0); [intro; subst; eauto|].
        inv_prop cur_request_timeouts_ok; repeat find_rewrite.
        -- exfalso; intuition eauto.
        -- eapply_lem_prop_hyp (stabilize_only_with_first_succ gst) Request; eauto.
           break_exists; break_and.
           repeat find_rewrite.
           simpl in *; repeat find_injection.
           assert (wf_ptr x4)
             by (eapply wf_ptr_succ_list_invariant' with (h:=h0); eauto;
                 find_rewrite; in_crush).
           eapply hash_injective_invariant; eauto using in_failed_in_nodes.
           inv_prop wf_ptr.
           repeat find_rewrite; auto.
      * cut (not_skipped (ChordIDSpace.hash h0)
                          (map id_of (succ_list st0))
                          (ChordIDSpace.hash x0)); eauto.
        find_eapply_prop not_skipped; eauto.
        break_live_node; eapply live_node_characterization;
          repeat find_rewrite; rewrite_update; eauto || congruence.
Qed.
Hint Resolve zave_invariant_request.

Theorem zave_invariant_input :
  chord_input_invariant zave_invariant.
Proof.
  unfold zave_invariant.
  split; eauto.
  break_and.
  autounfold in *.
  break_exists_exists.
  break_and; split; auto.
  inv_prop principals; expand_def.
  eapply principals_intro; eauto.
  intros.
  eapply principals_involves_joined_node_state_only.
  eapply Forall_forall; eauto.
  split; intros; simpl; eauto.
Qed.
Hint Resolve zave_invariant_input.

Theorem zave_invariant_output :
  chord_output_invariant zave_invariant.
Proof.
  unfold zave_invariant.
  split; eauto.
  break_and.
  autounfold in *.
  break_exists_exists.
  break_and; split; auto.
  inv_prop principals; expand_def.
  eapply principals_intro; eauto.
  intros.
  eapply principals_involves_joined_node_state_only.
  eapply Forall_forall; eauto.
  split; intros; simpl; eauto.
Qed.
Hint Resolve zave_invariant_output.

Theorem zave_invariant_holds :
  forall gst,
    reachable_st gst ->
    zave_invariant gst.
Proof.
  apply chord_net_invariant; eauto.
Qed.
Hint Resolve zave_invariant_holds.

Lemma sufficient_principals_invariant :
  forall gst,
    reachable_st gst ->
    sufficient_principals gst.
Proof.
  intros.
  assert (zave_invariant gst) by auto.
  unfold zave_invariant in *.
  tauto.
Qed.
Hint Resolve sufficient_principals_invariant.

Lemma live_node_in_succ_lists_invariant :
  forall gst,
    reachable_st gst ->
    live_node_in_succ_lists gst.
Proof.
  intros.
  assert (zave_invariant gst) by auto.
  unfold zave_invariant in *.
  tauto.
Qed.
Hint Resolve live_node_in_succ_lists_invariant.

Lemma first_succ_and_second_distinct :
  forall gst h st s1 s2 rest,
    reachable_st gst ->
    live_node gst h ->
    sigma gst h = Some st ->
    succ_list st = s1 :: s2 :: rest ->
    addr_of s1 <> addr_of s2.
Proof.
  intros.
  assert (pair_in s1 s2 (s1 :: s2 :: rest)) by constructor.
  find_copy_apply_lem_hyp sufficient_principals_invariant.
  unfold sufficient_principals in *; expand_def.
  pose proof succ_list_len_lower_bound.
  destruct x as [|p [|p' ps]]; simpl in *; try omega.
  assert (principal gst p /\ principal gst p').
  {
    split;
    inv_prop principals; break_and; rewrite -> Forall_forall in *;
      simpl in *; intuition eauto.
  }
  break_and.
  assert (p <> p').
  {
    inv_prop principals; expand_def.
    inv_prop NoDup.
    simpl in *; intuition.
  }
  repeat invcs_prop principal.
  intro.
  assert (id_of s1 = id_of s2).
  {
    assert (wf_ptr s1 /\ wf_ptr s2)
      by (split; eapply wf_ptr_succ_list_invariant'; eauto; repeat find_rewrite; in_crush).
    in_crush; repeat invcs_prop valid_ptr; congruence.
  }
  assert (hash p <> hash p').
  {
    intro; find_eapply_prop (p <> p').
    eapply hash_injective_invariant; eauto.
  }
  assert (between (id_of s1) (hash p) (id_of s2) \/
          between (id_of s1) (hash p') (id_of s2)).
  {
    repeat find_rewrite.
    destruct (id_eq_dec (id_of s2) (hash p));
      [right|left]; eapply between_xyx; congruence.
  }
  assert (not_skipped (ChordIDSpace.hash h) (map id_of (succ_list st)) (ChordIDSpace.hash p))
    by eauto.
  assert (not_skipped (ChordIDSpace.hash h) (map id_of (succ_list st)) (ChordIDSpace.hash p'))
    by eauto.
  break_or_hyp;
    match goal with
    | H: not_skipped _ _ _ |- _ =>
      eapply H; [|eassumption]
    end;
    repeat find_rewrite; simpl;
      change (ChordIDSpace.hash h :: id_of s1 :: id_of s2 :: map id_of rest)
        with ([ChordIDSpace.hash h] ++ id_of s1 :: id_of s2 :: map id_of rest);
      repeat find_rewrite;
      eauto.
Qed.
Hint Resolve first_succ_and_second_distinct.
