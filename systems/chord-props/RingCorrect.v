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

Lemma initial_succ_lists_all_principal :
  forall p l,
    In p l ->
    forall h a b,
      pair_in a b (hash h :: map id_of (find_succs h (sort_by_between h (map make_pointer l)))) ->
      ~ between a (hash p) b.
Proof.
  intros.
  match goal with
  | H: pair_in a b ?ss |- _ =>
    remember ss as succs;
      revert Heqsuccs;
      generalize dependent l;
      induction H
  end.
  - intros; find_injection.
    assert (In (make_pointer p) (map make_pointer l0)) by auto using in_map.
    admit.
  - admit.
Admitted.
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
    inv_prop initial_st; break_and.
    find_copy_apply_lem_hyp initial_nodes_large.
    destruct (start_handler h0 (nodes gst)) as [[?st ?ms] ?nts] eqn:?.
    copy_eapply_prop_hyp start_handler start_handler; auto; break_and.
    rewrite start_handler_init_state_preset in *; eauto with arith.
    repeat find_rewrite; repeat find_injection.
    simpl in *; eauto.
Qed.
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
