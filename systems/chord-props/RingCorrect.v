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

Lemma pair_in_sound :
  forall A (l : list A) xs a b ys,
    l = xs ++ a :: b :: ys ->
    pair_in a b l.
Proof.
Admitted.
Hint Resolve pair_in_sound.

Lemma initial_esl_is_sorted_nodes_chopped :
  forall h ns,
    hash h :: map id_of (find_succs h (sort_by_between h (map make_pointer ns))) =
    map id_of (chop_succs (sort_by_between h (map make_pointer (h :: ns)))).
Proof.
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
Admitted.

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
  rewrite initial_esl_is_sorted_nodes_chopped in *.
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
  rewrite start_handler_init_state_preset in *; eauto with arith.
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

Lemma initial_successor_lists_full :
  forall h gst,
    initial_st gst ->
    length (find_succs h (sort_by_between h (map make_pointer (nodes gst)))) = SUCC_LIST_LEN.
Proof.
Admitted.

Lemma in_find_succs :
  forall x h l,
    In x (find_succs h l) ->
    In x l.
Proof.
Admitted.

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

Theorem zave_invariant_holds :
  forall gst,
    reachable_st gst ->
    zave_invariant gst.
Proof.
  apply chord_net_invariant; autounfold; intros.
  - inv_prop initial_st.
    split.
    + break_and.
      unfold sufficient_principals.
      exists (nodes gst); split; try omega.
      unfold principals; repeat split.
      * auto.
      * apply Forall_forall; eauto.
      * intros; inv_prop principal; auto.
    + unfold live_node_in_succ_lists.
      intros.
      find_copy_apply_lem_hyp initial_succ_list; auto.
      find_copy_eapply_lem_hyp (initial_successor_lists_full h).
      pose proof succ_list_len_lower_bound.
      destruct (succ_list st) as [|p l] eqn:?.
      * assert (length (@nil pointer) >= 2) by congruence.
        simpl in *; omega.
      * exists (addr_of p).
        unfold best_succ; exists st; exists nil; exists (map addr_of l).
        split; eauto.
        split; eauto.
        split; try split.
        -- simpl.
           change (addr_of p :: map addr_of l) with (map addr_of (p :: l)).
           congruence.
        -- intros; simpl in *; tauto.
        -- eapply initial_nodes_live; eauto.
           assert (In p (find_succs h (sort_by_between h (map make_pointer (nodes gst)))))
             by (cut (In p (p :: l)); [congruence | auto with datatypes]).
           find_apply_lem_hyp in_find_succs.
           find_apply_lem_hyp in_sort_by_between.
           find_apply_lem_hyp in_map_iff; expand_def.
           easy.
  - split; break_and.
    + unfold sufficient_principals in *.
      break_exists_exists.
      break_and; split; eauto.
      inv_prop principals; break_and.
      apply principals_intro; auto; intros.
      * inv_prop principals; expand_def.
        eapply principals_involves_joined_node_state_only; eauto.
        eapply Forall_forall; eauto.
        admit.
      * find_eapply_prop In.
        admit.
    + unfold live_node_in_succ_lists.
      intros; repeat split; intuition eauto.
      admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

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
