Require Import List.
Import ListNotations.
Require Import Omega.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.

Set Bullet Behavior "Strict Subproofs".

Definition sufficient_principals (gst : global_state) : Prop :=
  exists ps,
    principals gst ps /\
    length ps > SUCC_LIST_LEN.

Definition zave_invariant (gst : global_state) : Prop :=
  sufficient_principals gst /\
  live_node_in_succ_lists gst.
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

Require Import mathcomp.ssreflect.ssreflect.

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
  split.
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
Qed.
Hint Resolve zave_invariant_init.

Theorem zave_invariant_start :
  chord_start_invariant zave_invariant.
Proof.
  autounfold; intros.
  split; break_and.
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
      split; intros.
      -- admit.
      -- admit.
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
Admitted.
Hint Resolve zave_invariant_start.

Definition live_node_dec :
  forall gst h,
    {live_node gst h} + {~ live_node gst h}.
Proof.
Admitted.

Definition principal_dec :
  forall gst h,
    {principal gst h} + {~ principal gst h}.
Proof.
Admitted.

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
    destruct (principal_dec gst h).
    + concludes.
      break_exists_name ps; break_and.
      exists (remove addr_eq_dec h ps).
      split.
      * inv_prop principals.
        pose proof (principal_preserved gst gst').
        econcludes.
        forwards.
        intros. repeat find_rewrite. in_crush.
        concludes.
        econcludes.
        repeat split.
        -- auto using remove_NoDup.
        -- break_and.
           rewrite -> ?Forall_forall in *; intros.
           repeat find_rewrite.
           eauto.
           eapply H17; eauto using in_remove.
           simpl.
           intro; break_or_hyp; try solve [eapply remove_In; eauto].
           admit.
        -- admit.
      * apply gt_S_n.
        inv_prop principals; break_and.
        assert (length ps = SUCC_LIST_LEN + 1 -> False) by eauto.
        rewrite remove_length_in; eauto; omega.
    + unfold principals in * |- ; break_exists_exists; expand_def.
      rewrite -> ?Forall_forall in *.
      assert (~ In h x) by eauto.
      split; auto.
      unfold principals in *; break_and.
      intuition eauto.
      * eapply Forall_forall; intros.
        eapply principal_preserved; try symmetry; try eassumption; eauto.
        repeat find_rewrite.
        intros.
        in_crush.
        find_rewrite.
        in_crush.
        assert (principal gst x0) by eauto.
        inv_prop principal.
        inv_prop live_node.
        firstorder.
      * assert (principal gst p); [|auto].
        split; intros.
        inv_prop principal.
        inv_prop live_node; intuition eauto using live_node_characterization.
        -- admit.
        -- admit.
  - inv_prop failure_constraint.
    easy.
Admitted.
Hint Resolve zave_invariant_fail.

Theorem zave_invariant_recv :
  chord_recv_handler_invariant zave_invariant.
Proof.
Admitted.
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
