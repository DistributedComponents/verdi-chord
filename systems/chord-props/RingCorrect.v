Require Import List.
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

Lemma initial_nodes_principal :
  forall gst h,
    initial_st gst ->
    In h (nodes gst) ->
    principal gst h.
Proof.
  intros.
  unfold principal; split.
  - auto.
  - intros.
    (* hard part *)
    admit.
Admitted.
Hint Resolve initial_nodes_principal.

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
      admit.
  - admit.
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
