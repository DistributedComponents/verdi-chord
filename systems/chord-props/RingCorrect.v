Require Import List.
Import ListNotations.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Omega.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemPointers.
Require Import Chord.ValidPointersInvariant.
Require Import Chord.SuccessorNodesAlwaysValid.
Require Import Chord.NodesNotJoinedHaveNoSuccessors.
Require Import Chord.Stabilize2Matches.

Set Bullet Behavior "Strict Subproofs".

Definition sufficient_principals (gst : global_state) : Prop :=
  exists ps,
    principals gst ps /\
    length ps > SUCC_LIST_LEN.

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

Inductive pair_in {A : Type} : A -> A -> list A -> Prop :=
| pair_in_head :
    forall a b l,
      pair_in a b (a :: b :: l)
| pair_in_rest :
    forall a b l,
      pair_in a b l ->
      forall x,
        pair_in a b (x :: l).

Lemma pair_in_sound :
  forall A (l : list A) xs a b ys,
    l = xs ++ a :: b :: ys ->
    pair_in a b l.
Proof.
move => A.
elim => //=; first by case.
move => a l IH.
case => /= [a0 b|a0 l0 a1 b] ys H_eq.
- find_injection.
  exact: pair_in_head.
- find_injection.
  apply pair_in_rest.
  exact: IH.
Qed.

Hint Resolve pair_in_sound.

Lemma initial_esl_is_sorted_nodes_chopped :
  forall h ns,
    hash h :: map id_of (find_succs h (sort_by_between h (map make_pointer ns))) =
    map id_of (chop_succs (sort_by_between h (map make_pointer (h :: ns)))).
Proof.
move => h ns.
rewrite map_cons /= {2}/sort_by_between.
Admitted.

Lemma sorted_list_elements_not_between :
  forall p l,
    In p l ->
    forall a b h,
      pair_in a b (sort_by_between h l) ->
      ~ ptr_between a p b.
Proof.
Admitted.

Lemma pair_in_firstn :
  forall (A : Type) (a b : A) k l,
    pair_in a b (firstn k l) ->
    pair_in a b l.
Proof.
move => A a b k l.
move: l a b k.
elim => //=.
- move => a b.
  by case.
- move => a l IH.
  move => a0 b.
  case => //=; first by move => H_p; inversion H_p.
  move => n H_p.
  inversion H_p; subst.
  * destruct n => //=.
    destruct l => //=.
    simpl in *.
    find_injection.
    exact: pair_in_head.
  * apply pair_in_rest.
    by eapply IH; eauto.
Qed.

Lemma sorted_list_chopped_elements_not_between :
  forall p l,
    In p l ->
    forall a b h,
      pair_in a b (chop_succs (sort_by_between h l)) ->
      ~ ptr_between a p b.
Proof.
  intros.
  unfold chop_succs in *.
  eauto using pair_in_firstn, sorted_list_elements_not_between.
Qed.

Lemma pair_in_map :
  forall A B (f : A -> B) a b l,
    pair_in a b (map f l) ->
    exists a0 b0,
      a = f a0 /\
      b = f b0 /\
      pair_in a0 b0 l.
Proof.
  intros.
  remember (map f l) as fl; revert Heqfl.
  generalize l.
  induction H; intros; subst.
  - destruct l1 as [|? [|? ?]]; simpl in *.
    + congruence.
    + congruence.
    + find_injection.
      repeat eexists.
      constructor.
  - destruct l1; simpl in *.
    + congruence.
    + find_injection.
      specialize (IHpair_in l1 eq_refl); expand_def.
      repeat eexists; constructor; eauto.
Qed.

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

Lemma in_find_succs :
  forall x h l,
    In x (find_succs h l) ->
    In x l.
Proof.
  move => x h.
  elim => //=.
  move => a l IH.
  break_if => H_in.
  - by right; apply IH.
  - rewrite /chop_succs in H_in.
    apply in_firstn in H_in.
    rewrite /= in H_in.
    break_or_hyp; first by left.
    by right.
Qed.

Lemma in_sort_by_between :
  forall x h l,
    In x (sort_by_between h l) ->
    In x l.
Proof.
  intros.
  eapply Permutation.Permutation_in.
  apply Permutation.Permutation_sym.
  eapply sort_by_between_permutes.
  eauto.
  eauto.
Qed.

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

Lemma joining_start_handler_st_joined:
  forall h k st ms nts,
    start_handler h [k] = (st, ms, nts) ->
    joined st = false.
Proof.
  unfold start_handler.
  intros.
  simpl in *; find_injection.
  reflexivity.
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

Lemma live_node_not_just_started :
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
      l <> h.
Proof.
  intros; intro; subst.
  assert (joined st = true).
  {
    inv_prop live_node; expand_def.
    repeat find_rewrite; rewrite_update; congruence.
  }
  assert (joined st = false) by
      eauto using joining_start_handler_st_joined.
  congruence.
Qed.

Lemma live_before_start_stays_live :
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
      live_node gst l ->
      live_node gst' l.
Proof.
  intros.
  inv_prop live_node; expand_def.
  eapply live_node_characterization; eauto; repeat find_rewrite;
    solve [now rewrite_update | in_crush].
Qed.

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
  autounfold; intros.
  repeat split; break_and.
  + unfold sufficient_principals in *.
    break_exists_exists.
    break_and; split; eauto.
    inv_prop principals; break_and.
    apply principals_intro; auto; intros.
    * inv_prop principals; expand_def.
      eapply principals_involves_joined_node_state_only; eauto.
      eapply Forall_forall; eauto.
      intros.
      intuition; inv_prop live_node; expand_def.
      -- eapply live_node_characterization; eauto;
           repeat find_rewrite;
           try rewrite_update;
           in_crush || eauto.
      -- repeat find_rewrite; rewrite_update; auto.
      -- repeat find_rewrite; update_destruct;
           subst; rewrite_update;
             repeat find_injection.
         cut (joined x0 = false); [congruence|].
         eapply joining_start_handler_st_joined; eauto.
         eapply live_node_characterization; eauto; in_crush.
      -- repeat find_rewrite; update_destruct;
           subst; rewrite_update;
             repeat find_injection.
         cut (joined x0 = false); [congruence|].
         eapply joining_start_handler_st_joined; eauto.
         rewrite_update; auto.
    * find_eapply_prop In.
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
  + unfold live_node_in_succ_lists in *.
    intros; repeat split.
    repeat find_rewrite.
    update_destruct; subst; rewrite_update.
    * inv_prop live_node; expand_def.
      repeat find_rewrite; rewrite_update; repeat find_injection.
      find_eapply_lem_hyp joining_start_handler_st_joined.
      congruence.
    * eapply_lem_prop_hyp adding_nodes_did_not_affect_live_node live_node; eauto.
      find_apply_hyp_hyp.
      break_exists_exists.
      eapply adding_nodes_does_not_affect_best_succ; eauto.
  + admit. (* easy, only one message sent by start handler *)
Admitted.
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

Theorem zave_invariant_fail :
  chord_fail_invariant zave_invariant.
Proof.
  autounfold.
  intros.
  break_and.
  split.
  - inv_prop failure_constraint.
    unfold principal_failure_constraint in *.
    unfold sufficient_principals in *.
    break_and.
    eapply some_principals_ok.
    destruct (principal_dec gst h).
    + concludes.
      break_exists_name ps; break_and.
      exists (remove addr_eq_dec h ps); repeat split.
      * inv_prop principals; auto using remove_NoDup.
      * inv_prop principals.
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
      * inv_prop principals; break_and.
        assert (length ps = SUCC_LIST_LEN + 1 -> False) by eauto.
        cut (length (remove addr_eq_dec h ps) > SUCC_LIST_LEN); [omega|].
        eapply gt_S_n.
        rewrite remove_length_in; eauto.
        omega.
    + unfold principals in * |- ; break_exists_exists; expand_def.
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
  - inv_prop failure_constraint.
    easy.
Qed.
Hint Resolve zave_invariant_fail.

Definition response_payload_dec :
  forall p,
    {response_payload p} + {~ response_payload p}.
Proof.
  destruct p;
    solve [left; constructor|right; intro; inv_prop response_payload].
Defined.

Lemma in_concat :
  forall A (x : A) (l : list (list A)),
    In x (concat l) ->
    exists xs,
      In xs l /\
      In x xs.
Proof.
Admitted.

Lemma handle_query_req_GotPredAndSuccs_response_accurate :
  forall st src m ms,
    handle_query_req st src m = ms ->
    forall dst pr succs,
      In (dst, GotPredAndSuccs pr succs) ms ->
      pr = pred st /\
      succs = succ_list st.
Proof.
  intros.
  unfold handle_query_req in *; break_match; subst;
    try in_crush; try congruence.
Qed.
Hint Resolve handle_query_req_GotPredAndSuccs_response_accurate.

Lemma handle_delayed_queries_GotPredAndSuccs_response_accurate :
  forall h st st' ms nts cts,
    do_delayed_queries h st = (st', ms, nts, cts) ->
    forall dst pr succs,
      In (dst, GotPredAndSuccs pr succs) ms ->
      pr = pred st' /\
      succs = succ_list st'.
Proof.
  unfold do_delayed_queries, handle_delayed_query.
  intros.
  break_match; find_injection; try solve [in_crush].
  find_apply_lem_hyp in_concat; expand_def.
  match goal with
  | H: _ |- _ => rewrite -> in_map_iff in H; expand_def; break_let; subst
  end.
  simpl in *; eauto.
Qed.
Hint Resolve handle_delayed_queries_GotPredAndSuccs_response_accurate.

Lemma handle_query_req_GotSuccList_response_accurate :
  forall st src m ms,
    handle_query_req st src m = ms ->
    forall dst succs,
      In (dst, GotSuccList succs) ms ->
      succs = succ_list st.
Proof.
  intros.
  unfold handle_query_req in *; break_match; subst;
    try in_crush; try congruence.
Qed.
Hint Resolve handle_query_req_GotSuccList_response_accurate.

Lemma handle_delayed_queries_GotSuccList_response_accurate :
  forall h st st' ms nts cts,
    do_delayed_queries h st = (st', ms, nts, cts) ->
    forall dst succs,
      In (dst, GotSuccList succs) ms ->
      succs = succ_list st'.
Proof.
  unfold do_delayed_queries, handle_delayed_query.
  intros.
  break_match; find_injection; try solve [in_crush].
  find_apply_lem_hyp in_concat; expand_def.
  match goal with
  | H: _ |- _ => rewrite -> in_map_iff in H; expand_def; break_let; subst
  end.
  simpl in *.
  simpl in *; eauto.
Qed.
Hint Resolve handle_delayed_queries_GotSuccList_response_accurate.

Lemma recv_handler_GotPredAndSuccs_response_accurate :
  forall src dst st p st' ms nts cts h pr succs,
    recv_handler src dst st p = (st', ms, nts, cts) ->
    In (h, GotPredAndSuccs pr succs) ms ->
    pr = pred st' /\
    succs = succ_list st'.
Proof.
  intros.
  repeat match goal with
         | H : context[do_delayed_queries] |- _ => fail 1
         | |- _ => handler_def
         end.
  find_apply_lem_hyp in_app_or; break_or_hyp; eauto.
  repeat handler_def; simpl in *; try break_or_hyp; repeat find_injection; try (congruence || tauto).
  eauto.
Qed.
Hint Resolve recv_handler_GotPredAndSuccs_response_accurate.

Lemma hd_in_chop_succs :
  forall x l,
    In x (chop_succs (x :: l)).
Proof.
  intros.
  unfold chop_succs.
  pose proof succ_list_len_lower_bound.
  destruct SUCC_LIST_LEN; try omega.
  rewrite firstn_cons; in_crush.
Qed.
Hint Resolve hd_in_chop_succs.

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

Lemma live_node_exists_after_simple_change :
  forall h src dst l succs gst gst' st st',
    live_node_in_msg_succ_lists gst ->
    (exists p, In (src, (dst, GotPredAndSuccs p succs)) l) \/ In (src, (dst, GotSuccList succs)) l ->
    (forall x, In x l -> In x (msgs gst)) ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst h = Some st ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    joined st = joined st' ->
    length succs > 0 ->
    Exists (live_node gst') (map addr_of (chop_succs (make_pointer src :: succs))).
Proof.
  repeat (match goal with H: _ |- _ => clear H end).
  intros.
  assert (Exists (live_node gst) (map addr_of (chop_succs (make_pointer src :: succs))))
    by (repeat break_or_hyp; break_exists;
        eapply_prop live_node_in_msg_succ_lists; eauto).
  apply Exists_exists; find_apply_lem_hyp Exists_exists.
  break_exists_exists; split; break_and; auto.
  break_live_node.
  destruct (addr_eq_dec x h); subst;
    eapply live_node_characterization;
    repeat find_rewrite; rewrite_update; try find_injection; eauto.
  Unshelve. exact None.
Qed.

Theorem zave_invariant_recv_sufficient_principals :
  forall (gst : global_state) (gst' : ChordSemantics.global_state) (src h : addr) (st : data)
    (p : payload) (xs ys : list (addr * (addr * payload))) (st' : data) (ms : list (addr * payload))
    (nts cts : list timeout),
    reachable_st gst ->
    step_dynamic gst gst' ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    msgs gst = xs ++ (src, (h, p)) :: ys ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst') ->
    sigma gst h = Some st ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' = update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (timeouts gst h)) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = map (send h) ms ++ xs ++ ys -> trace gst' = trace gst ++ [e_recv (src, (h, p))] ->
    zave_invariant gst ->
    sufficient_principals gst'.
Proof.
Admitted.
Hint Resolve zave_invariant_recv_sufficient_principals.

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

Lemma recv_handler_sets_succ_list_when_setting_joined :
  forall src dst st m st' ms nts cts,
    recv_handler src dst st m = (st', ms, nts, cts) ->
    joined st = false ->
    joined st' = true ->
    exists succs qdst s p,
      m = GotSuccList succs /\
      cur_request st = Some (qdst, Join2 s, p) /\
      succ_list st' = make_succs s succs.
Proof.
  intros.
  repeat (handler_def || handler_simpl).
  repeat eexists; eauto.
Qed.

Lemma recv_handler_setting_joined_makes_succ_list_nonempty :
  forall src dst st m st' ms nts cts,
    recv_handler src dst st m = (st', ms, nts, cts) ->
    joined st = false ->
    joined st' = true ->
    succ_list st' <> [].
Proof.
  intros.
  find_eapply_lem_hyp recv_handler_sets_succ_list_when_setting_joined; eauto.
  expand_def.
  intro.
  repeat find_rewrite.
  unfold make_succs in *.
  eapply (@in_nil pointer).
  repeat find_reverse_rewrite.
  eauto using hd_in_chop_succs.
Qed.

Theorem zave_invariant_recv_live_node_in_succ_lists :
  forall (gst : global_state) (gst' : ChordSemantics.global_state) (src h : addr) (st : data) 
    (p : payload) (xs ys : list (addr * (addr * payload))) (st' : data) (ms : list (addr * payload))
    (nts cts : list timeout),
    reachable_st gst ->
    step_dynamic gst gst' ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    msgs gst = xs ++ (src, (h, p)) :: ys ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst') ->
    sigma gst h = Some st ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' = update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (timeouts gst h)) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = map (send h) ms ++ xs ++ ys -> trace gst' = trace gst ++ [e_recv (src, (h, p))] ->
    zave_invariant gst ->
    live_node_in_succ_lists gst'.
Proof.
  unfold zave_invariant; intros; break_and.
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
          repeat find_rewrite; constructor; in_crush.
          (* x is joined because we're stabilizing with it. *)
          admit.
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
        unfold best_succ.
        admit.
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
          - simpl in *.
            assert (x11 = x) by admit; subst.
            find_eapply_lem_hyp cur_request_valid; eauto.
            rewrite <- wf_ptr_eq; eauto.
        }
        assert (Exists (live_node gst)
                       (map addr_of (chop_succs (make_pointer (addr_of x) :: x2)))).
        {
          eapply_prop live_node_in_msg_succ_lists;
            try solve [repeat find_rewrite; right; in_crush].
          repeat (handler_def || handler_simpl).
          - admit. (* must have joined = true since we only stabilize2 with joined nodes *)
          - admit. (* again, must have joined = true since we only join2 after
                      talking to a joined node and joined nodes have joined successors *)
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
        admit.
  - assert (live_node gst h0).
    break_live_node; repeat find_rewrite; rewrite_update; eauto using live_node_characterization.
    assert (exists s : addr, best_succ gst h0 s) by eauto.
    break_exists_exists.
    eapply best_succ_preserved; try find_eapply_prop update; eauto.
    eauto using joined_preserved_by_recv_handler.
Admitted.
Hint Resolve zave_invariant_recv_live_node_in_succ_lists.

Theorem zave_invariant_recv_live_node_in_msg_succ_lists :
  forall (gst : global_state) (gst' : ChordSemantics.global_state) (src h : addr) (st : data) 
    (p : payload) (xs ys : list (addr * (addr * payload))) (st' : data) (ms : list (addr * payload))
    (nts cts : list timeout),
    reachable_st gst ->
    step_dynamic gst gst' ->
    recv_handler src h st p = (st', ms, nts, cts) ->
    msgs gst = xs ++ (src, (h, p)) :: ys ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst') ->
    sigma gst h = Some st ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' = update addr_eq_dec (timeouts gst) h (nts ++ remove_all timeout_eq_dec cts (timeouts gst h)) ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    msgs gst' = map (send h) ms ++ xs ++ ys -> trace gst' = trace gst ++ [e_recv (src, (h, p))] ->
    zave_invariant gst ->
    live_node_in_msg_succ_lists gst'.
Proof.
  unfold zave_invariant; intros; break_and.
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

Theorem zave_invariant_recv :
  chord_recv_handler_invariant zave_invariant.
Proof.
  unfold chord_recv_handler_invariant, zave_invariant.
  intuition eauto.
Qed.
Hint Resolve zave_invariant_recv.

Theorem zave_invariant_tick :
  chord_tick_invariant zave_invariant.
Proof.
Admitted.
Hint Resolve zave_invariant_tick.

Theorem zave_invariant_keepalive :
  chord_keepalive_invariant zave_invariant.
Proof.
Admitted.
Hint Resolve zave_invariant_keepalive.

Theorem zave_invariant_rectify :
  chord_rectify_invariant zave_invariant.
Proof.
Admitted.
Hint Resolve zave_invariant_rectify.

Theorem zave_invariant_request :
  chord_request_invariant zave_invariant.
Proof.
Admitted.
Hint Resolve zave_invariant_request.

Theorem zave_invariant_input :
  chord_input_invariant zave_invariant.
Proof.
Admitted.
Hint Resolve zave_invariant_input.

Theorem zave_invariant_output :
  chord_output_invariant zave_invariant.
Proof.
Admitted.
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

Lemma first_succ_and_others_distinct :
  forall gst h st s1 s2 xs ys,
    reachable_st gst ->
    sigma gst h = Some st ->
    succ_list st = xs ++ s1 :: ys ->
    In s2 (xs ++ ys) ->
    addr_of s1 <> addr_of s2.
Proof.
Admitted.
Hint Resolve first_succ_and_others_distinct.
