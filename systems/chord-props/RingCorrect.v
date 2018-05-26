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
Require Import Chord.PtrCorrectInvariant.
Require Import Chord.Sorting.
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
    + left. unfold principal; autounfold. intuition.
      find_eapply_lem_hyp forallb_forall; eauto using live_addr_In_live_addrs.
      repeat find_rewrite. eauto using not_skipped_bool_not_skipped.
      admit.
    + right. intro. find_apply_lem_hyp forallb_exists.
      break_exists. intuition. find_apply_lem_hyp In_live_addrs_live.
      break_match; try congruence.
      unfold principal in *; autounfold in *.
      intuition.
      admit.
  - right. intuition. unfold principal in *; autounfold in *. intuition.
Admitted.

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

Lemma sorted_trans :
  forall A (le : A -> A -> bool),
    (forall x y z, le x y = true -> le y z = true -> le x z = true) ->
    forall x y l,
      Sorting.sorted A le (x :: l) ->
      In y l ->
      le x y = true.
Proof.
  intros. prep_induction H0.
  induction H0; intros; simpl in *; auto.
  - solve_by_inversion.
  - find_inversion. intuition.
  - intuition. find_inversion. simpl in *.
    intuition; subst; eauto.
Qed.

Lemma sorted_trans_app :
  forall A (le : A -> A -> bool),
    (forall x y z, le x y = true -> le y z = true -> le x z = true) ->
    forall x y l' l,
      Sorting.sorted A le (l' ++ l) ->
      In y l ->
      In x l' ->
      le x y = true.
Proof.
  intros. prep_induction H0.
  induction H0; intros; simpl in *; auto.
  - destruct l', l; subst; simpl in *; solve_by_inversion.
  - destruct l', l; subst; simpl in *; try solve_by_inversion.
    find_inversion. destruct l'; simpl in *; solve_by_inversion.
  - intuition.
    destruct l'; intuition; simpl in *. find_inversion. intuition.
    + subst. destruct l'; simpl in *; intuition.
      * subst. in_crush. eauto using sorted_trans.
      * find_inversion.
        eapply H1; eauto.
        eapply sorted_trans; eauto. in_crush.
    + destruct l'; simpl in *; intuition; subst.
      * find_inversion.
        eapply sorted_trans; eauto. in_crush.
      * find_inversion.
        specialize (H5 x0 y0 (a0 :: l') l0).
        intuition.
Qed.

Lemma between_trans :
  forall a b c d,
    between a b c ->
    between a c d ->
    between a b d.
Proof.
  intros.
  invcs H; invcs H0;
    try solve [econstructor; eauto using lt_trans];
    congruence.
Qed.

Lemma unroll_between_trans :
  forall a b c d,
    unroll_between a b c = true ->
    unroll_between a c d = true ->
    unroll_between a b d = true.
Proof.
  unfold unroll_between; intros.
  repeat break_if; eauto; try congruence.
  repeat find_apply_lem_hyp between_bool_between.
  apply between_between_bool_equiv.
  eauto using between_trans.
Qed.

Lemma unroll_between_ptr_trans :
  forall a b c d,
    unroll_between_ptr a b c = true ->
    unroll_between_ptr a c d = true ->
    unroll_between_ptr a b d = true.
Proof.
  unfold unroll_between_ptr in *.
  eauto using unroll_between_trans.
Qed.

Lemma between_trans' :
  forall a b c d,
    between a b c ->
    between b d c ->
    between a d c.
Proof.
  intros.
  invcs H; invcs H0;
    try solve [econstructor; eauto using lt_trans];
    congruence.
Qed.

Lemma between_swap_not :
  forall x y z,
    between x z y ->
    ~ between x y z.
Proof.
  unfold not.
  intros.
  repeat invcs_prop between;
    solve [id_auto | eapply Chord.ChordIDSpace.lt_asymm; eauto].
Qed.

Lemma between_not_between :
  forall h a b c,
    between h a b ->
    between h b c ->
    ~ between a c b.
Proof.
  intros. intro.
  find_eapply_lem_hyp between_trans'; eauto.
  find_eapply_lem_hyp between_swap_not; eauto.
Qed.


Lemma between_not_between' :
  forall h a b c,
    between h a b ->
    between h c a  ->
    ~ between a c b.
Proof.
  intros. intro.
  specialize (between_not_between h c a b). intros. intuition.
  destruct (id_eq_dec a b); subst.
  - find_apply_lem_hyp not_between_xyy. auto.
  - find_apply_lem_hyp between_rot_l; auto.
Qed.

Lemma sorted_map :
  forall A B (f : A -> B) (leA : A -> A -> bool) (leB : B -> B -> bool),
    (forall x y, leA x y = leB (f x) (f y)) ->
    forall l,
      sorted A leA l -> sorted B leB (map f l).
Proof.
  induction l; intros; simpl in *; auto.
  - constructor.
  - inv_prop sorted.
    + simpl. constructor.
    + intuition. simpl. constructor; eauto.
Qed.

Lemma sorted_prepend_zero :
  forall A (le : A -> A -> bool) z,
    (forall x, le z x = true) ->
    forall l,
      sorted A le l ->
      sorted A le (z :: l).
Proof.
  induction l; intros.
  - constructor.
  - constructor; auto.
Qed.

Lemma sorted_chop_succs :
  forall a n l,
    sorted _ (unroll_between_ptr a) l ->
    sorted _ (unroll_between_ptr a) (firstn n l).
Proof.
  induction n; intros; simpl.
  - constructor.
  - break_match; try solve [constructor].
    inv_prop sorted.
    + destruct n; simpl; constructor.
    + destruct n; simpl; try solve [constructor].
      constructor; auto.
      eapply_prop_hyp sorted sorted. simpl in *. auto.
Qed.

Lemma sorted_tl :
  forall b l,
    sorted _ (unroll_between_ptr b) l ->
    sorted _ (unroll_between_ptr b) (List.tl l).
Proof.
  destruct l.
  - simpl; tauto.
  - simpl.
    intros;
      inv_prop sorted; eauto || constructor.
Qed.

Lemma sort_by_between_sorted :
  forall h l,
    sorted _ (unroll_between_ptr h) (sort_by_between h l).
Proof.
  intros. unfold sort_by_between.
  apply sorted_sort.
  intros. unfold unroll_between_ptr, unroll_between.
  repeat (break_if; auto).
  match goal with
  | |- context [between_bool ?x ?y ?z] => specialize (between_bool_yz_total x y z)
  end. intros. intuition.
Qed.

Lemma chop_succs_partition :
  forall l,
  exists xs,
    l = chop_succs l ++ xs.
Proof.
  intros. unfold chop_succs.
  eexists; eauto using firstn_skipn.
Qed.

Lemma pair_in_sorted :
  forall A (le : A -> A -> bool) l a b,
    sorted _ le l ->
    pair_in a b l ->
    le a b = true.
Proof.
  intros. induction H.
  - inv_prop @pair_in.
  - repeat inv_prop @pair_in.
  - inv_prop @pair_in; eauto.
Qed.

Lemma pair_in_right :
  forall A (a : A) b l,
    pair_in a b l ->
    In a l.
Proof.
  intros. induction H.
  - in_crush.
  - in_crush.
Qed.

Lemma pair_in_left :
  forall A (a : A) b l,
    pair_in a b l ->
    In b l.
Proof.
  intros. induction H.
  - in_crush.
  - in_crush.
Qed.

Lemma pair_in_sorted_in :
  forall A (le : A -> A -> bool) l a b x,
    (forall x y z, le x y = true -> le y z = true -> le x z = true) ->
    sorted _ le l ->
    pair_in a b l ->
    In x l ->
    x = a \/ x = b \/
    le x a = true \/
    le b x = true.
Proof.
  intros. induction H0.
  - solve_by_inversion.
  - in_crush. inv_prop @pair_in. solve_by_inversion.
  - inv_prop @pair_in.
    + in_crush.
       eauto using sorted_trans.
    + intuition. in_crush. inv_prop @pair_in; intuition.
      right. right. left. eauto using sorted_trans, pair_in_right.
Qed.

Lemma NoDup_pair :
  forall A (l : list A) a b,
    NoDup l ->
    pair_in a b l ->
    a <> b.
Proof.
  intros. induction l.
  - solve_by_inversion.
  - inv_prop NoDup. inv_prop @pair_in; eauto.
    intro. subst. intuition.
Qed.

Lemma sorted_zero_prefix :
  forall A (le : A -> A -> bool) (wf : A -> Prop) (A_eq_dec: forall x y : A, {x = y} + {x <> y}) l a,
    (forall x y z, le x y = true -> le y z = true -> le x z = true) ->
    (forall b, le a b = true) ->
    (forall b, wf b -> le b a = true -> b = a) ->
    (forall x, In x l -> wf x) ->
    sorted _ le l ->
    exists xs ys,
      l = xs ++ ys /\
      (forall x, In x xs -> x = a) /\
      (forall y, In y ys -> y <> a).
Proof.
  intros.
  induction H3.
  - exists [],[]. in_crush.
  - destruct (A_eq_dec x a); subst.
    + exists [a],[]. in_crush.
    + exists [],[x]. in_crush.
  - destruct (A_eq_dec x a); subst.
    + conclude_using in_crush.
      break_exists_name xs.
      exists (a :: xs). simpl.
      break_exists_exists. intuition. congruence.
    + conclude_using in_crush.
      break_exists_name xs.
      assert (xs = []). {
        destruct xs; intuition.
        break_exists; intuition. simpl in *. find_inversion.
        find_false.
        apply H1; intuition. specialize (H5 a0). intuition. subst. auto.
      } subst. simpl in *.
      exists [].
      break_exists_name ys.
      exists (x :: ys).
      simpl. intuition; subst; eauto.
Qed.

Lemma sorted_list_elements_between_pair_eq :
  forall A (A_eq_dec : forall x y : A, {x=y}+{x<>y}) le (a b : A) l,
    (forall x, le x x = true) ->
    (forall x y z, le x y = true -> le y z = true -> le x z = true) ->
    (forall x y, le x y = true -> le y x = true -> y = x) ->
    sorted _ le l ->
    pair_in a b l ->
    forall p,
      In p l ->
      le a p = true ->
      le p b = true ->
      p = a \/ p = b.
Proof.
  induction 6.
  - intros.
    assert (forall x, In x l -> le b x = true).
    {
      intros. eapply sorted_trans; eauto.
      now invcs_prop sorted.
    }
    simpl in *; intuition auto.
  - invcs_prop sorted.
    + inv_prop (pair_in a b).
    + concludes; intros.
      break_or_hyp; eauto.
      assert (le y a = true).
      {
        find_eapply_lem_hyp pair_in_right.
        destruct (A_eq_dec y a).
        subst; eauto.
        eapply sorted_trans; eauto.
        simpl in *; tauto.
      }
      eauto.
Qed.

Lemma sorted_by_between_list_elements_between_pair_eq :
  forall h a b l,
    sorted _ (unroll_between_ptr h) l ->
    pair_in a b l ->
    (forall p q, In p l -> In q l -> id_of p = id_of q ->  p = q) ->
    forall p,
      In p l ->
      unroll_between_ptr h a p = true ->
      unroll_between_ptr h p b = true ->
      p = a \/ p = b.
Proof.
  intros.
  unfold unroll_between_ptr in *.
  assert (sorted _ (unroll_between (hash h)) (map id_of l))
    by (eapply sorted_map; eassumption || reflexivity).
  find_eapply_lem_hyp sorted_list_elements_between_pair_eq;
    eauto using unrolling_reflexive, unrolling_transitive, id_eq_dec, unrolling_antisymmetric, in_map, map_pair_in.
  break_or_hyp; [left|right]; eauto using pair_in_left, pair_in_right.
Qed.

(* TODO move to PairIn.v *)
Lemma pair_in_tl :
  forall A (a b : A) l,
    pair_in a b (List.tl l) ->
    pair_in a b l.
Proof.
  destruct l.
  - tauto.
  - simpl; intros.
    now constructor.
Qed.

Lemma sorted_by_between_list_elements_between_pair_eq_tl_chop :
  forall h a b l,
    sorted _ (unroll_between_ptr h) l ->
    pair_in a b (List.tl (chop_succs l)) ->
    (forall p q, In p l -> In q l -> id_of p = id_of q ->  p = q) ->
    forall p,
      In p l ->
      unroll_between_ptr h a p = true ->
      unroll_between_ptr h p b = true ->
      p = a \/ p = b.
Proof.
  eauto using sorted_by_between_list_elements_between_pair_eq, pair_in_firstn, pair_in_tl.
Qed.

Lemma firstn_in :
  forall A n (l : list A) x,
    In x (firstn n l) ->
    In x l.
Proof.
  induction n; intros; simpl in *; intuition.
  break_match; simpl in *; intuition.
Qed.

Lemma NoDup_chop_succs :
  forall l,
    NoDup l ->
    NoDup (chop_succs l).
Proof.
  unfold chop_succs.
  induction SUCC_LIST_LEN; intros; simpl in *; eauto.
  break_match; eauto. inv_prop NoDup.
  constructor; auto.
  intro. eauto using firstn_in.
Qed.

Lemma unroll_between_zero :
  forall h x,
    unroll_between_ptr h (make_pointer h) x = true.
Proof.
  intros. unfold unroll_between_ptr, unroll_between.
  break_if; intuition.
Qed.

Definition hash_injective_on_pair a b :=
  id_of a = id_of b -> a = b.

Lemma unroll_between_zero' :
  forall h x,
    wf_ptr h ->
    wf_ptr x ->
    hash_injective_on_pair h x ->
    unroll_between_ptr (addr_of h) x h = true ->
    x = h.
Proof.
  intros. unfold unroll_between_ptr, unroll_between in *.
  repeat (break_if; intuition); try discriminate;
    unfold wf_ptr, hash_injective_on_pair, id_of, addr_of in *;
    try solve [repeat find_rewrite; intuition|find_false; auto].
Qed.

Definition wf h x := wf_ptr x /\ hash_injective_on_pair (make_pointer h) x.

Lemma in_chop_succs :
  forall x l,
    In x (chop_succs l) ->
    In x l.
Proof.
  eauto using in_firstn.
Qed.

Lemma unroll_between_contra :
  forall h a b c,
    hash_injective_on_pair a b ->
    a <> b ->
    unroll_between_ptr h a b = true ->
    unroll_between_ptr h b c = true ->
    ~ ptr_between a c b.
Proof.
  intros. unfold unroll_between_ptr, unroll_between, ptr_between in *.
  repeat break_if; auto; repeat find_rewrite; eauto using not_between_xxy, not_between_xyy, between_bool_between, between_swap_not, between_not_between.
Qed.

Lemma unroll_between_contra' :
  forall h a b c,
    hash_injective_on_pair a b ->
    a <> b ->
    unroll_between_ptr h a b = true ->
    unroll_between_ptr h c a = true ->
    ~ ptr_between a c b.
Proof.
  intros. unfold unroll_between_ptr, unroll_between, ptr_between in *.
  repeat break_if; auto; repeat find_rewrite; eauto using not_between_xxy, not_between_xyy, between_bool_between, between_swap_not, between_not_between, between_rot_l.
  repeat find_apply_lem_hyp between_bool_between.
  intro. find_apply_lem_hyp between_rot_l; eauto.
  eapply between_not_between;
    [| |eauto]; eauto.
Qed.

Lemma sort_by_between_in :
  forall h l p,
    In p l ->
    In p (sort_by_between h l).
Proof.
  intros. unfold sort_by_between.
  eauto using sort_permutes, Permutation.Permutation_in.
Qed.

Lemma sorted_h_in :
  forall h l,
    (forall a b, In a l -> In b l -> hash a = hash b -> a = b) ->
    In h l ->
    exists xs,
      sort_by_between h (map make_pointer l) = make_pointer h :: xs /\
      sorted _ (unroll_between_ptr h) (make_pointer h :: xs).
Proof.
  intros.
  assert (sorted _ (unroll_between_ptr h) (sort_by_between h (map make_pointer l)))
    by eauto using sort_by_between_sorted.
  match goal with
  | H : sorted _ _ _ |- _ =>
    eapply sorted_zero_prefix with (wf := (wf h)) in H
  end;
    eauto using pointer_eq_dec, unroll_between_zero, unroll_between_ptr_trans.
  - break_exists_name xs. break_exists_name ys.
    destruct xs.
    + intuition. exfalso.
      assert (In (make_pointer h) (sort_by_between h (map make_pointer l))).
      {
        apply sort_by_between_in. in_crush.
      }
      repeat find_rewrite. simpl in *. eauto.
    + intuition. simpl in *.
      assert (p = make_pointer h) by auto.
      subst.
      simpl in *. exists (xs ++ ys). intuition.
      repeat find_reverse_rewrite.
      eauto using sort_by_between_sorted.
  - intros.
    unfold wf in *. intuition.
    apply unroll_between_zero'; eauto using make_pointer_wf.
  - intros.
    find_apply_lem_hyp in_sort_by_between. in_crush.
    unfold wf. intuition; eauto using make_pointer_wf.
    unfold hash_injective_on_pair. simpl. intros. f_equal. eauto.
Qed.

Lemma NoDup_prepend_h_chop_succs_tl :
  forall h l,
    (forall a b, In a l -> In b l -> hash a = hash b -> a = b) ->
    In h l ->
    NoDup l ->
    NoDup (make_pointer h :: (chop_succs (List.tl (sort_by_between h (map make_pointer l))))).
Proof.
  intros.
  assert (NoDup (map make_pointer l)).
  { apply NoDup_map_injective; auto.
    intros. unfold make_pointer in *. find_inversion. auto.
  }
  assert (NoDup (sort_by_between h (map make_pointer l))).
  {
    eapply NoDup_Permutation_NoDup; eauto.
    unfold sort_by_between. eapply sort_permutes; eauto.
  }
  find_copy_apply_lem_hyp sorted_h_in; eauto. break_exists. intuition.
  repeat find_rewrite. inv_prop NoDup.
  simpl.
  constructor; eauto using NoDup_chop_succs.
  eauto using in_chop_succs.
Qed.    


Lemma pair_in_cons :
  forall A (a : A) b c l,
    pair_in a b (c :: l) ->
    a = c \/ pair_in a b l.
Proof.
  intros. inv_prop @pair_in; intuition.
Qed.

Lemma sorted_pair_in_in' :
  forall A (le : A -> A -> bool) (l1 l2 : list A) a b c,
    (forall x y z, le x y = true -> le y z = true -> le x z = true) ->
    pair_in a b l1 ->
    sorted A le (l1 ++ l2) ->
    In c l2 ->
    le c a = true \/ le b c = true \/ c = a \/ c = b.
Proof.
  intros.
  find_apply_lem_hyp pair_in_left.
  right. left. eapply sorted_trans_app; eauto.
Qed.

Lemma sorted_pair_in_in'' :
  forall A (le : A -> A -> bool) (l : list A) a b c,
    (forall x y z, le x y = true -> le y z = true -> le x z = true) ->
    pair_in a b l ->
    sorted A le l ->
    In c l ->
    le c a = true \/ le b c = true \/ c = a \/ c = b.
Proof.
  induction 2.
  - intros. in_crush.
    inv_prop sorted. inv_prop sorted; in_crush.
    right. left.
    eapply sorted_trans; eauto. in_crush.
  - intros. in_crush.
    + find_apply_lem_hyp pair_in_right.
      eauto using sorted_trans.
    + inv_prop sorted; in_crush.
Qed.

Lemma sorted_app_l :
  forall A le l1 l2,
    sorted A le (l1 ++ l2) ->
    sorted A le l1.
Proof.
  intros. induction l1; simpl in *; auto.
  - constructor.
  - inv_prop sorted.
    + match goal with
      | H : [] = _ |- _ => symmetry in H
      end.
      find_apply_lem_hyp app_eq_nil.
      intuition. subst. constructor.
    + repeat find_rewrite.
      destruct l1; simpl in *; auto.
      * constructor.
      * find_inversion. intuition. constructor; auto.
Qed.

Lemma sorted_pair_in_in :
  forall A (le : A -> A -> bool) (l1 l2 : list A) a b c,
    (forall x y z, le x y = true -> le y z = true -> le x z = true) ->
    pair_in a b l1 ->
    sorted A le (l1 ++ l2) ->
    In c (l1 ++ l2) ->
    le c a = true \/ le b c = true \/ c = a \/ c = b.
Proof.
  in_crush.
  - eapply sorted_pair_in_in''; eauto using sorted_app_l.
  - eapply sorted_pair_in_in'; eauto.
Qed.
      
Lemma initial_succ_lists_all_principal :
  forall p l,
    (forall a b, In a l -> In b l -> hash a = hash b -> a = b) ->
    NoDup l ->
    In p l ->
    forall h a b,
      In h l ->
      pair_in a b (hash h :: map id_of (chop_succs (List.tl (sort_by_between h (map make_pointer l))))) ->
      ~ between a (hash p) b.
Proof.
  intros.
  change (hash h) with (id_of (make_pointer h)) in *.
  rewrite <- map_cons in *.
  find_eapply_lem_hyp pair_in_map; expand_def.
  change (between (id_of x) (hash p) (id_of x0)) with (ptr_between x (make_pointer p) x0).
  assert (sorted _ (unroll_between_ptr h) (sort_by_between h (map make_pointer l))) by
      eauto using sort_by_between_sorted.
  assert (sorted _ (unroll_between_ptr h) (tl (sort_by_between h (map make_pointer l)))) by
      eauto using sorted_tl.
  assert (sorted _ (unroll_between_ptr h) (chop_succs (tl (sort_by_between h (map make_pointer l))))) by
      eauto using sorted_chop_succs.
  assert (sorted _ (unroll_between_ptr h) (make_pointer h :: (chop_succs (tl (sort_by_between h (map make_pointer l)))))).
  {
    eapply sorted_prepend_zero; eauto. intros.
    unfold unroll_between_ptr, unroll_between. break_if; auto.
  }
  find_copy_eapply_lem_hyp pair_in_sorted; eauto.
  assert (x <> x0).
  {
    eapply NoDup_pair; [|eauto].
    apply NoDup_prepend_h_chop_succs_tl; eauto.
  }
  assert (hash_injective_on_pair x x0).
  {
    unfold hash_injective_on_pair.
    intros.
    find_copy_apply_lem_hyp pair_in_left.
    find_apply_lem_hyp pair_in_right.
    in_crush;
      repeat find_apply_lem_hyp in_chop_succs;
      repeat find_apply_lem_hyp in_tl;
      repeat find_apply_lem_hyp in_sort_by_between;
      in_crush;
      f_equal; eauto.
  }
  assert (In (make_pointer p) (map make_pointer l)) by in_crush.
  assert (In (make_pointer p) (sort_by_between h (map make_pointer l)))
    by eauto using sort_by_between_in.
  find_copy_apply_lem_hyp sorted_h_in; eauto. break_exists. break_and.
  repeat find_rewrite.
  pose proof chop_succs_partition x1. break_exists.
  cbv [tl] in *.
  match goal with
  | Hsubst : x1 = _,
    Hsorted : sorted _ _ (_ :: x1),
    HIn : In _ (_ :: x1) |- _ =>
    rewrite Hsubst in Hsorted,HIn;
      rewrite app_comm_cons in Hsorted,HIn
  end.
  remember (make_pointer h :: chop_succs x1) as l1.
  find_eapply_lem_hyp sorted_pair_in_in; eauto using unroll_between_ptr_trans.
  intuition; simpl in *; eauto using unroll_between_contra.
  - eapply unroll_between_contra'; eauto.
  - eapply unroll_between_contra; eauto.
  - subst. unfold ptr_between in *. simpl in *.
    eapply not_between_xxy; eauto.
  - subst. unfold ptr_between in *. simpl in *.
    eapply not_between_xyy; eauto.
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
  - unfold not_skipped; autounfold; intros.
    split; intros.
    + find_apply_lem_hyp initial_succ_list; eauto.
      unfold initial_st in *; autounfold in *. intuition.
      repeat find_rewrite; repeat find_injection.
      unfold not_skipped; intros.
      simpl in *; eapply initial_succ_lists_all_principal with (p := h) (h := h0); eauto.
    + unfold initial_st in *; autounfold in *; intuition.
      repeat find_rewrite || find_injection.
      tauto.
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

Lemma principals_involves_joined_node_state_and_msgs_only :
  forall gst gst' p,
    principal gst p ->
    (forall h st,
        live_node gst h /\ sigma gst h = Some st <->
        live_node gst' h /\ sigma gst' h = Some st) ->
    (forall src h m s,
        succs_msg m s ->
        ~ In h (failed_nodes gst') ->
        In h (nodes gst') ->
        In (src, (h, m)) (msgs gst') ->
        ~ In h (failed_nodes gst) /\
        In h (nodes gst) /\
        In (src, (h, m)) (msgs gst)) ->
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
    split; autounfold; intros; eauto.
    + find_eapply_prop no_live_node_skips; eauto.
      find_eapply_prop iff; eauto.
    + find_eapply_prop no_msg_to_live_node_skips;
        try find_eapply_prop In; eauto.
Qed.

Lemma principals_involves_joined_node_state_only :
  forall gst gst' p,
    principal gst p ->
    (forall h st,
        live_node gst h /\ sigma gst h = Some st <->
        live_node gst' h /\ sigma gst' h = Some st) ->
    live_node gst' p /\ no_live_node_skips gst' p.
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
    autounfold; intros; eauto.
    find_eapply_prop no_live_node_skips; eauto.
    find_eapply_prop iff; eauto.
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
         assert (In p (chop_succs (List.tl (sort_by_between h (map make_pointer (nodes gst)))))).
         {
           repeat find_reverse_rewrite.
           replace (succ_list st) with (p :: l).
           eauto with datatypes.
         }
         find_apply_lem_hyp in_firstn.
         find_apply_lem_hyp in_tl.
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

Theorem msgs_out_of_net_go_to_clients :
  forall gst,
    reachable_st gst ->
    forall src dst p,
      In (src, (dst, p)) (msgs gst) ->
      ~ In dst (nodes gst) ->
      client_addr dst.
Proof.
Admitted.

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
  - inv_prop principals; expand_def; autounfold in *.
    unfold principal; rewrite <- and_assoc; split.
    eapply principals_involves_joined_node_state_only;
      [eapply Forall_forall; eassumption |]; intros.
    + intuition; inv_prop live_node; expand_def.
      * eapply live_node_characterization; eauto;
          repeat find_rewrite;
          try rewrite_update;
          in_crush || eauto.
      * repeat find_rewrite; rewrite_update; auto.
      * repeat find_rewrite; update_destruct;
          subst; rewrite_update;
            repeat find_injection.
        cut (joined x0 = false); [congruence|].
        eapply joining_start_handler_st_joined; eauto.
        eapply live_node_characterization; eauto; in_crush.
      * repeat find_rewrite; update_destruct;
          subst; rewrite_update;
            repeat find_injection.
        cut (joined x0 = false); [congruence|].
        eapply joining_start_handler_st_joined; eauto.
        rewrite_update; auto.
    + autounfold; intros.
      unfold start_handler in *; simpl in *.
      repeat find_rewrite || find_injection.
      simpl in *; break_or_hyp.
      * unfold send in *; find_injection; inv_prop succs_msg.
      * assert (principal gst p) by (eapply Forall_forall; eauto).
        inv_prop principal;
          expand_def.
        exfalso; find_eapply_prop client_addr;
          eapply msgs_out_of_net_go_to_clients; eauto.
        eauto.
  - find_eapply_prop In.
    inv_prop principal.
    split; eauto using live_after_start_was_live.
    split; autounfold in *; intros.
    + inv_prop principal;  expand_def.
      find_eapply_prop no_live_node_skips; eauto.
      eapply live_before_start_stays_live; eauto.
      repeat find_rewrite;
        update_destruct; rewrite_update; eauto.
      subst; exfalso; eauto.
    + inv_prop principal; expand_def.
      assert (live_node gst p) by eauto using live_after_start_was_live.
      find_eapply_prop no_msg_to_live_node_skips;
        repeat find_rewrite; try solve [try apply in_cons; eauto].
      in_crush; eauto.
Qed.
Hint Resolve zave_invariant_start.

Lemma principal_preserved :
  forall gst gst',
    nodes gst = nodes gst' ->
    (forall f,
        In f (failed_nodes gst) ->
        In f (failed_nodes gst')) ->
    sigma gst = sigma gst' ->
    msgs gst = msgs gst' ->
    forall h,
      principal gst h ->
      ~ In h (failed_nodes gst') ->
      principal gst' h.
Proof.
  intros.
  unfold principal in *.
  repeat break_and_goal; autounfold in *; intros.
  - break_and.
    inv_prop live_node; expand_def.
    repeat find_rewrite.
    eapply live_node_characterization; eauto.
  - intros; subst.
    inv_prop live_node; expand_def.
    repeat find_rewrite || find_injection.
    find_eapply_prop succ_list; repeat find_rewrite; eauto.
    eapply live_node_characterization; repeat find_rewrite; eauto.
  - intros; subst.
    inv_prop live_node; expand_def.
    repeat find_rewrite || find_injection.
    find_eapply_prop not_skipped; repeat find_rewrite; eauto;
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
    msgs gst' = msgs gst ->
    principal gst' p.
Proof.
  unfold principal.
  intuition eauto;
    autounfold; intros.
  - assert (live_node gst p) by eauto.
    break_live_node.
    destruct (addr_eq_dec p h);
      eapply live_node_characterization; repeat find_rewrite; rewrite_update; eauto.
    congruence.
  - subst.
    repeat find_rewrite; update_destruct; rewrite_update.
    + find_injection.
      find_reverse_rewrite.
      find_eapply_prop no_live_node_skips; eauto.
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
  - find_eapply_prop no_msg_to_live_node_skips;
      repeat find_rewrite; eauto.
Qed.
Hint Resolve succ_lists_same_principal_preserved.

Lemma msgs_succs_principal_preserved :
  forall gst gst' h p st st',
    principal gst p ->
    sigma gst h = Some st ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    succ_list st = succ_list st' ->
    joined st = joined st' ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    (forall src h m succs,
        In h (nodes gst') ->
        ~ In h (failed_nodes gst') ->
        succs_msg m succs ->
        In (src, (h, m)) (msgs gst') ->
        In h (nodes gst) /\
        ~ In h (failed_nodes gst) /\
        In (src, (h, m)) (msgs gst)) ->
    principal gst' p.
Proof.
  unfold principal.
  intuition eauto;
    autounfold; intros.
  - assert (live_node gst p) by eauto.
    break_live_node.
    destruct (addr_eq_dec p h);
      eapply live_node_characterization; repeat find_rewrite; rewrite_update; eauto.
    congruence.
  - subst.
    repeat find_rewrite; update_destruct; rewrite_update.
    + find_injection.
      find_reverse_rewrite.
      find_eapply_prop no_live_node_skips; eauto.
      break_live_node;
        rewrite_update;
        eapply live_node_characterization; repeat find_rewrite; eauto.
      rewrite_update; congruence.
      rewrite_update; congruence.
    + assert (live_node gst h0).
      {
        break_live_node; eapply live_node_characterization; repeat find_rewrite; eauto.
        rewrite_update; congruence.
      }
      eauto.
  - find_copy_apply_lem_hyp live_node_means_state_exists; expand_def.
    find_eapply_prop no_msg_to_live_node_skips;
      repeat find_reverse_rewrite;
      eauto;
      unfold not; find_eapply_prop In; now eauto.
Qed.
Hint Resolve msgs_succs_principal_preserved.

Lemma succ_lists_same_sufficient_principals_preserved :
  forall gst gst' h st st',
    sufficient_principals gst ->
    sigma gst h = Some st ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    succ_list st = succ_list st' ->
    joined st = joined st' ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    msgs gst = msgs gst' ->
    sufficient_principals gst'.
Proof.
  intros.
  eapply some_principals_ok.
  unfold have_principals, sufficient_principals, principals in *.
  break_exists_exists;
    break_and; repeat split; eauto;
      rewrite -> Forall_forall in *;
        solve [eauto using succ_lists_same_principal_preserved
              |intros; omega].
Qed.
Hint Resolve succ_lists_same_sufficient_principals_preserved.

Lemma msgs_state_principals_preserved :
  forall gst gst' h st st',
    sufficient_principals gst ->
    sigma gst h = Some st ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    succ_list st = succ_list st' ->
    joined st = joined st' ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    (forall src h m succs,
        In h (nodes gst) ->
        ~ In h (failed_nodes gst) ->
        succs_msg m succs ->
        In (src, (h, m)) (msgs gst') ->
        In h (nodes gst) /\
        ~ In h (failed_nodes gst) /\
        In (src, (h, m)) (msgs gst)) ->
    sufficient_principals gst'.
Proof.
  intros.
  eapply some_principals_ok.
  unfold have_principals, sufficient_principals, principals in *.
  break_exists_exists.
  break_and.
  repeat split; eauto.
  - rewrite -> Forall_forall in *;
      try solve [eauto using msgs_succs_principal_preserved
                |intros; omega].
    intros; eapply msgs_succs_principal_preserved; eauto.
    intros; eauto.
    eapply H6; eauto; congruence.
  - omega.
Qed.
Hint Resolve msgs_state_principals_preserved.

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
  eauto.
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

Lemma live_node_preserved_by_recv :
  forall h,
    chord_recv_handler_invariant (fun gst => live_node gst h).
Proof.
  repeat autounfold; intros.
  unfold live_node.
  repeat find_rewrite; update_destruct; rewrite_update; auto; subst.
  repeat split; eauto.
  break_live_node.
  eexists; split; eauto.
  eapply joined_preserved_by_recv_handler; eauto; congruence.
Qed.

Theorem live_node_was_live_or_no_succs :
  forall gst gst' h,
    reachable_st gst ->
    step_dynamic gst gst' ->
    live_node gst' h ->
    live_node gst h \/
    ~ In h (nodes gst) \/
    exists st,
      sigma gst h = Some st /\
      succ_list st = [] /\
      joined st = false.
Proof.
  intros.
  inv_prop step_dynamic; repeat find_rewrite; simpl in *; intuition eauto.
  - break_live_node; simpl in *.
    update_destruct; rewrite_update;
      unfold live_node; repeat find_rewrite; intuition eauto.
  - break_live_node; simpl in *.
    unfold live_node.
    repeat find_rewrite; intuition eauto.
  - break_live_node; simpl in *.
    update_destruct; rewrite_update;
      unfold live_node; repeat find_rewrite; intuition eauto.
    subst.
    assert (joined st = joined st')
      by repeat (handler_def; simpl; try congruence).
    repeat find_injection.
    repeat find_rewrite; intuition eauto.
  - break_live_node; simpl in *.
    update_destruct; rewrite_update;
      unfold live_node; repeat find_rewrite; intuition eauto.
    subst.
    destruct (joined d) eqn:?; intuition eauto.
    find_apply_lem_hyp nodes_not_joined_have_no_successors; eauto.
    intuition eauto.
Qed.

Lemma not_skipped_nil :
  forall h n,
    not_skipped h [] n.
Proof.
  unfold not_skipped; intros.
  exfalso.
  find_eapply_lem_hyp (f_equal (@length id)).
  rewrite -> !app_length in *.
  simpl in *; omega.
Qed.
Hint Resolve not_skipped_nil.

Lemma cons_make_succs :
  forall p succs,
    make_succs p succs = p :: firstn (SUCC_LIST_LEN - 1) succs.
Proof.
  pose proof succ_list_len_lower_bound.
  unfold make_succs, chop_succs.
  intros; simpl.
  destruct SUCC_LIST_LEN; try omega.
  simpl.
  replace (n - 0) with n by omega.
  auto.
Qed.

Lemma pair_in_complete :
  forall A a b l,
    @pair_in A a b l ->
    exists xs ys,
      l = xs ++ [a; b] ++ ys.
Proof.
  intros.
Admitted.

Lemma not_skipped_firstn :
  forall h l n k,
    not_skipped h l n ->
    not_skipped h (firstn k l) n.
Proof.
  unfold not_skipped.
  intros.
  change (h :: firstn k l) with (firstn (S k) (h :: l)) in *.
  copy_eapply pair_in_sound H0.
  find_eapply_lem_hyp pair_in_firstn.
  find_eapply_lem_hyp pair_in_complete.
  expand_def; eauto.
Qed.

Lemma map_firstn :
  forall A B (f : A -> B) k l,
    map f (firstn k l) = firstn k (map f l).
Proof.
  induction k; auto.
  intros.
  destruct l; simpl; congruence.
Qed.

Lemma recv_handler_succs_msg_accurate :
  forall src dst st p st' ms nts cts h m succs,
  recv_handler src dst st p = (st', ms, nts, cts) ->
  In (h, m) ms ->
  succs_msg m succs ->
  succs = succ_list st'.
Proof.
  intros; inv_prop succs_msg.
  - handler_def.
    find_apply_lem_hyp in_app_or; break_or_hyp.
    + find_eapply_lem_hyp handle_delayed_queries_GotSuccList_response_accurate; eauto.
    + handler_def;
      repeat match goal with
             | H: False |- _ => elim H
             | H: _ \/ _ |- _ => destruct H
             | H: (_, _) = (_, _) |- _ => injc H; try congruence
             | |- _ => progress simpl in *
             | |- _ => handler_def
             end;
      eapply handle_query_req_GotSuccList_response_accurate; eauto.
  - eapply recv_handler_GotPredAndSuccs_response_accurate; eauto.
Qed.

Lemma weaken_no_live_node_skips :
  forall gst p,
    reachable_st gst ->
    no_live_node_skips gst p ->
    forall h st,
      In h (nodes gst) ->
      ~ In h (failed_nodes gst) ->
      sigma gst h = Some st ->
      not_skipped (ChordIDSpace.hash h) (map id_of (succ_list st)) (ChordIDSpace.hash p).
Proof.
  autounfold; intros; subst.
  destruct (joined st) eqn:?.
  - find_eapply_prop not_skipped; eauto using live_node_characterization.
  - find_apply_lem_hyp nodes_not_joined_have_no_successors; eauto.
    repeat find_rewrite; eauto.
Qed.

Lemma principal_not_before_stabilize_tgt :
  forall gst st h s p,
    reachable_st gst ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    cur_request st = Some (s, Stabilize, GetPredAndSuccs) ->
    no_live_node_skips gst p ->
    ~ between (hash h) (hash p) (id_of s).
Proof.
  intros.
  assert (cur_request_timeouts_ok' (cur_request st) (timeouts gst h)) by eauto.
  repeat find_rewrite.
  inv_prop cur_request_timeouts_ok'.
  find_eapply_lem_hyp stabilize_only_with_first_succ; eauto.
  expand_def.
  repeat find_rewrite || find_injection.
  assert (not_skipped (hash h) (map id_of (succ_list st)) (hash p))
    by eauto using weaken_no_live_node_skips.
  unfold not_skipped in *.
  find_eapply_lem_hyp hd_error_tl_exists.
  break_exists_name succs.
  specialize (H6 (hash h) (id_of x) nil (map id_of succs)).
  apply H6.
  repeat find_rewrite.
  reflexivity.
Qed.

Lemma principal_not_before_stabilize2_tgt :
  forall gst,
    reachable_st gst ->
    forall st h s ns p req,
      In h (nodes gst) ->
      ~ In h (failed_nodes gst) ->
      sigma gst h = Some st ->
      cur_request st = Some (s, Stabilize2 ns, req) ->
      not_skipped (hash h) (map id_of (succ_list st)) (hash p) ->
      ~ between (hash h) (hash p) (id_of s).
Proof.
  intros until 1.
  pattern gst.
  eapply chord_net_invariant; do 2 autounfold; intros.
  - match goal with
    | H: context[cur_request] |- _ =>
      erewrite initial_st_cur_request_None in H; eauto; congruence
    end.
  - repeat find_rewrite.
    destruct (addr_eq_dec h0 h); subst.
    + match goal with
      | H: context[start_handler] |- _ =>
        rewrite start_handler_with_single_known in H
      end.
      rewrite_update.
      repeat find_injection || simpl in *.
      congruence.
    + rewrite_update.
      simpl in *; break_or_hyp; try tauto.
      eauto.
  - repeat find_rewrite.
    eauto with datatypes.
  - repeat find_rewrite.
    update_destruct; rewrite_update.
    + subst. repeat find_injection || find_rewrite.
      repeat (handler_def || handler_simpl).
    + eauto.
  - repeat find_rewrite.
    update_destruct; rewrite_update.
    + subst. repeat find_injection || find_rewrite.
      repeat (handler_def || handler_simpl).
    + eauto.
  - repeat find_rewrite.
    update_destruct; rewrite_update.
    + subst. repeat find_injection || find_rewrite.
      repeat (handler_def || handler_simpl).
    + eauto.
  - repeat find_rewrite.
    update_destruct; rewrite_update.
    + subst. repeat find_injection || find_rewrite.
      repeat (handler_def || handler_simpl).
    + eauto.
  - repeat find_rewrite.
    update_destruct; rewrite_update.
    + subst. repeat find_injection || find_rewrite.
      repeat (handler_def || handler_simpl).
      replace (ptr st) with (make_pointer h0) in *
        by (symmetry; eapply ptr_correct; eauto).
      unfold ptr_between in *; simpl in *.
      assert (cur_request_timeouts_ok' (cur_request st) (timeouts gst0 h0))
        by eauto.
      repeat find_rewrite.
      inv_prop cur_request_timeouts_ok'; inv_prop query_request.
      find_eapply_lem_hyp stabilize_only_with_first_succ; eauto.
      expand_def.
      destruct (succ_list st) eqn:?;
        simpl in *; try congruence.
      find_injection.
      assert (between (hash h0) (hash p0) (id_of x)).
      {
        eapply between_trans.
        eauto.
        rewrite <- (wf_ptr_hash_eq x)
          by eauto using cur_request_valid.
        repeat find_rewrite.
        eauto.
      }
      find_eapply_prop not_skipped; eauto.
      repeat find_reverse_rewrite.
      simpl.
      rewrite cons_make_succs.
      simpl.
      change ChordIDParams.hash with hash.
      rewrite -> (wf_ptr_hash_eq x)
        by eauto using cur_request_valid.
      eauto using app_nil_l with datatypes.
    + eauto.
  - repeat (handler_def || handler_simpl).
  - repeat find_rewrite; simpl in *; eauto.
  - repeat find_rewrite; simpl in *; eauto.
Qed.

Lemma best_predecessor_between :
  forall h x succs p,
    best_predecessor h succs x = p ->
    ptr_between h p x \/ h = p.
Proof.
  unfold best_predecessor, hd.
  intros.
  break_match; subst; eauto.
  assert (In p (p :: l)) by in_crush.
  find_reverse_rewrite.
  find_eapply_lem_hyp filter_In.
  intuition eauto.
Qed.

Lemma best_predecessor_self :
  forall h x succs,
    best_predecessor h succs x = h ->
    id_of h = id_of x \/
    id_of (hd h succs) = id_of x \/
    ptr_between h x (hd h succs).
Proof.
  unfold best_predecessor, hd, ptr_between.
  intros.
  destruct (id_eq_dec (id_of h) (id_of x)); eauto.
  destruct succs as [|s rest];
    [simpl in *; right; right;
     eapply between_xyx;
     unfold id_of in *; congruence|].
  destruct (id_eq_dec (id_of s) (id_of x)); eauto.
  do 2 right.
  repeat break_match; try eauto using between_xyx.
  - assert (~ In s []) by in_crush.
    repeat find_reverse_rewrite; subst.
    erewrite filter_In in *.
    eapply not_between_swap;
      [unfold id_of in *; congruence|].
    intro; eapply_prop not.
    split; in_crush.
  - subst.
    assert (In h (h :: l)) by in_crush.
    repeat find_reverse_rewrite; subst.
    erewrite filter_In in *; expand_def.
    find_apply_lem_hyp ptr_between_bool_true.
    exfalso; eapply not_between_xxy; eauto.
Qed.

Lemma handle_query_req_GotBestPredecessor_between :
  forall st src dst ms p,
    handle_query_req st src (GetBestPredecessor p) = ms ->
    In (dst, GotBestPredecessor (ptr st)) ms ->
    id_of (ptr st) = id_of p \/
    id_of (hd (ptr st) (succ_list st)) = id_of p \/
    ptr_between (ptr st) p (hd (ptr st) (succ_list st)).
Proof.
  unfold handle_query_req.
  intros; subst.
  eapply best_predecessor_self.
  in_crush; congruence.
Qed.

Lemma handle_delayed_query_GotBestPredecessor_accurate :
  forall h st ms dst src p,
    handle_delayed_query h st (src, GetBestPredecessor p) = ms ->
    In (dst, GotBestPredecessor (ptr st)) ms ->
    id_of (ptr st) = id_of p \/
    id_of (hd (ptr st) (succ_list st)) = id_of p \/
    ptr_between (ptr st) p (hd (ptr st) (succ_list st)).
Proof.
  unfold handle_delayed_query.
  intros.
  eapply handle_query_req_GotBestPredecessor_between; eauto.
Qed.

Lemma handle_delayed_query_GotBestPredecessor_not_between :
  forall h st ms dst src p,
    handle_delayed_query h st (src, GetBestPredecessor p) = ms ->
    In (dst, GotBestPredecessor (ptr st)) ms ->
    ~ ptr_between (ptr st) (hd (ptr st) (succ_list st)) p \/
    id_of (ptr st) = id_of p /\
    id_of (hd (ptr st) (succ_list st)) <> id_of (ptr st).
Proof.
  intros.
  eapply handle_delayed_query_GotBestPredecessor_accurate in H; eauto.
  unfold ptr_between, id_of in *.
  repeat break_or_hyp.
  - repeat find_rewrite.
    destruct (succ_list st); simpl in *.
    + repeat find_rewrite.
      eauto using not_between_xxy.
    + destruct (id_eq_dec (ptrId p0) (ptrId p)).
      * repeat find_rewrite.
        eauto using not_between_xxy.
      * tauto.
  - repeat find_rewrite.
    eauto using not_between_xyy.
  - left.
    now apply between_swap_not.
Qed.

Lemma lookup_not_between :
  forall gst p j h,
    reachable_st gst ->
    In (h, (j, GotBestPredecessor p)) (msgs gst) ->
    ~ between (hash h) (id_of p) (hash j).
Proof.
  intros until 1.
  pattern gst.
  eapply chord_net_invariant; do 2 autounfold; intros.
  - inv_prop initial_st; break_and;
      repeat find_rewrite; in_crush.
  - repeat find_rewrite; in_crush.
    unfold send in *; find_injection.
    repeat handler_simpl || handler_def.
  - repeat find_rewrite; in_crush.
  - repeat find_rewrite; in_crush.
    unfold send in *; find_injection.
    repeat handler_simpl || handler_def.
    find_eapply_lem_hyp option_map_Some; expand_def.
  - repeat find_rewrite; in_crush.
    unfold send in *; find_injection.
    repeat handler_simpl || handler_def.
    unfold send_keepalives in *.
    find_apply_lem_hyp in_map_iff.
    expand_def.
  - repeat find_rewrite; in_crush.
    unfold send in *; find_injection.
    repeat handler_simpl || handler_def.
    unfold send_keepalives in *.
    find_eapply_lem_hyp option_map_Some; expand_def.
  - repeat find_rewrite; in_crush.
    unfold send in *; find_injection.
    handler_def.
    in_crush.
    + repeat handler_def || handler_simpl.
      find_eapply_lem_hyp option_map_Some; expand_def.
    + match goal with
      | H: context[handle_query_timeout] |- _ => clear H
      end.
      repeat handler_def || handler_simpl.
      find_apply_lem_hyp in_concat; expand_def.
      find_apply_lem_hyp in_map_iff; expand_def.
Admitted.

Lemma principal_not_before_join2_tgt :
  forall gst st h s ns p req,
    reachable_st gst ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    cur_request st = Some (s, Join2 ns, req) ->

    no_live_node_skips gst p ->
    ~ between (hash h) (hash p) (id_of s).
Proof.
Admitted.

Theorem zave_invariant_recv_sufficient_principals :
  chord_recv_handler_pre_post
    zave_invariant
    sufficient_principals.
Proof.
  autounfold_one; unfold zave_invariant; intros.
  assert (forall h, live_node gst h -> live_node gst' h)
    by (intros; eapply live_node_preserved_by_recv; eauto).
  intros.
  break_and.
  destruct (list_eq_dec pointer_eq_dec (succ_list st) (succ_list st')).
  - destruct (Bool.bool_dec (joined st) (joined st')).
    + autounfold in *.
      eapply some_principals_ok.
      unfold have_principals, principals in *.
      break_exists_exists.
      rewrite -> Forall_forall in *.
      intuition.
      assert (principal gst x0) by auto.
      unfold principal in *.
      assert (no_live_node_skips gst' x0).
      {
        autounfold; intros.
        inv_prop live_node; expand_def.
        repeat find_rewrite.
        update_destruct; rewrite_update;
          repeat find_injection;
          find_eapply_prop no_live_node_skips; congruence || eauto;
           eapply live_node_characterization; eauto.
      }
      autounfold; intuition.
      repeat find_rewrite.
      find_apply_lem_hyp in_app_or; break_or_hyp.
      * in_crush. unfold send in *; find_injection.
        find_copy_eapply_lem_hyp recv_handler_succs_msg_accurate; eauto.
        subst.
        eapply weaken_no_live_node_skips; try solve [econstructor; eauto|eauto|congruence].
        repeat find_rewrite.
        now rewrite_update.
      * find_eapply_prop no_msg_to_live_node_skips; eauto.
        repeat find_rewrite; in_crush.
    + destruct (joined st) eqn:?, (joined st') eqn:?;
        try (find_apply_lem_hyp joined_preserved_by_recv_handler; auto; congruence).
      find_apply_lem_hyp recv_handler_sets_succ_list_when_setting_joined; eauto.
      expand_def.
      find_apply_lem_hyp nodes_not_joined_have_no_successors; eauto.
      repeat find_rewrite.
      exfalso; eapply in_nil.
      rewrite -> e; eapply hd_in_chop_succs.
  - assert (cur_request_timeouts_ok' (cur_request st) (timeouts gst h)) by auto.
    eapply some_principals_ok.
    unfold sufficient_principals, principals in *; break_exists_exists.
    break_and; repeat split; omega || eauto.
    rewrite -> Forall_forall in *; intros.
    assert (principal gst x0) by eauto.
    assert (no_live_node_skips gst' x0).
    {
      autounfold in *; unfold principal in *; intuition.
      repeat find_rewrite; update_destruct; rewrite_update; subst.
      - repeat (handler_def; simpl in *; try congruence);
        repeat (find_rewrite || find_injection); simpl.
      + repeat find_rewrite.
        inv_prop cur_request_timeouts_ok'.
        invcs_prop query_request.
        find_eapply_lem_hyp stabilize_only_with_first_succ; eauto.
        break_exists; break_and.
        repeat find_rewrite || find_injection.
        rewrite cons_make_succs.
        simpl.
        eapply not_skipped_initial'.
        * rewrite map_firstn.
          eapply not_skipped_firstn.
          find_eapply_prop no_msg_to_live_node_skips; eauto.
        * rewrite -> wf_ptr_hash_eq
            by eauto using cur_request_valid.
          eapply principal_not_before_stabilize_tgt; eauto.
      + repeat find_rewrite.
        inv_prop cur_request_timeouts_ok'.
        invcs_prop query_request.
        find_eapply_lem_hyp stabilize_only_with_first_succ; eauto.
        break_exists; break_and.
        repeat find_rewrite || find_injection.
        rewrite cons_make_succs.
        simpl.
        eapply not_skipped_initial'.
        * rewrite map_firstn.
           eapply not_skipped_firstn.
           find_eapply_prop no_msg_to_live_node_skips; eauto.
        * rewrite -> wf_ptr_hash_eq
            by eauto using cur_request_valid.
          eapply principal_not_before_stabilize_tgt; eauto.
      + repeat find_rewrite.
        inv_prop cur_request_timeouts_ok'.
        invcs_prop query_request.
        find_eapply_lem_hyp stabilize_only_with_first_succ; eauto.
        break_exists; break_and.
        repeat find_rewrite || find_injection.
        rewrite cons_make_succs.
        simpl.
        eapply not_skipped_initial'.
        * rewrite map_firstn.
           eapply not_skipped_firstn.
           find_eapply_prop no_msg_to_live_node_skips; eauto.
        * rewrite -> wf_ptr_hash_eq
            by eauto using cur_request_valid.
          eapply principal_not_before_stabilize_tgt; eauto.
      + find_copy_eapply_lem_hyp stabilize2_param_matches; eauto.
        rewrite cons_make_succs.
        simpl; subst.
        erewrite <- wf_ptr_hash_eq
          by eauto using cur_request_valid.
        eapply not_skipped_initial'.
        * rewrite map_firstn.
           eapply not_skipped_firstn.
           find_eapply_prop no_msg_to_live_node_skips; eauto.
        * rewrite -> wf_ptr_hash_eq
            by eauto using cur_request_valid.
          eapply principal_not_before_stabilize2_tgt; eauto.
          eapply weaken_no_live_node_skips; eauto.
      + find_copy_eapply_lem_hyp join2_param_matches; eauto; subst.
        assert (not_skipped (hash (addr_of x12)) (map id_of x13) (ChordIDSpace.hash x0)).
        find_eapply_prop no_msg_to_live_node_skips; eauto.
        eauto.
        rewrite cons_make_succs.
        simpl; subst.
        erewrite <- wf_ptr_hash_eq
          by eauto using cur_request_valid.
        eapply not_skipped_initial'.
        * rewrite map_firstn.
           eapply not_skipped_firstn.
           eauto.
        * destruct x13 as [|s1 rest].
          -- admit.
          -- simpl in *.
             assert (between (hash (addr_of x12)) (hash h0) (id_of s1)).
             {
               admit.
             }
             assert (id_of s1 <> hash (addr_of x12)).
             {
               admit.
             }
             assert (~ between (hash (addr_of x12)) (hash x0) (id_of s1)).
             {
               admit.
             }
             unfold not_skipped in *.
             unfold ChordIDSpace.hash in *.
             set (pred := (hash (addr_of x12))) in *.
             set (principal := (hash x0)) in *.
             set (first_succ := (id_of s1)) in *.
             set (joining := hash h0) in *.
             intro.
             eapply_prop not.
             eapply between_trans; [eauto|].
             eauto.
             apply between_rot_l in H33; [|admit].
             assert (between (hash h0) (id_of s1)).
             eapply not_between_swap in H32; [|admit].
             eauto using between_trans, between_trans'.
             eapply between_trans; eauto.
             apply between_rot_l in H30.

             intro.
            by eauto using cur_request_valid.
          eapply principal_not_before_join2_tgt; eauto.
      - find_eapply_prop no_live_node_skips; eauto.
        eapply live_node_equivalence; eauto.
        repeat find_rewrite; rewrite_update; auto.
    }
    unfold principal in *.
    intuition eauto.
    autounfold; intuition.
    repeat find_rewrite.
    find_apply_lem_hyp in_app_or; break_or_hyp.
    + in_crush. unfold send in *; find_injection.
      find_copy_eapply_lem_hyp recv_handler_succs_msg_accurate; eauto.
      subst.
      eapply weaken_no_live_node_skips; try solve [econstructor; eauto|eauto|congruence].
      repeat find_rewrite.
      now rewrite_update.
    + find_eapply_prop no_msg_to_live_node_skips; eauto.
      repeat find_rewrite; in_crush.
Qed.
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
  eapply msgs_state_principals_preserved; eauto.
  - repeat handler_def; simpl; auto.
  - eauto using joined_preserved_by_tick_handler.
  - repeat find_rewrite.
    intros.
    intuition.
    find_apply_lem_hyp in_app_or; break_or_hyp.
    + exfalso.
      repeat handler_def; simpl in *; unfold send in *.
      intuition; find_injection.
      find_apply_lem_hyp option_map_Some; expand_def.
      inv_prop succs_msg.
    + auto.
Qed.
Hint Resolve zave_invariant_tick.

Theorem zave_invariant_keepalive :
  chord_keepalive_invariant zave_invariant.
Proof.
  unfold zave_invariant.
  split; eauto.
  break_and.
  eapply msgs_state_principals_preserved; eauto.
  - repeat handler_def; simpl; auto.
  - repeat handler_def; reflexivity.
  - repeat find_rewrite.
    intros.
    intuition.
    find_apply_lem_hyp in_app_or; break_or_hyp; auto.
    exfalso.
    repeat handler_def; simpl in *;
      unfold send, send_keepalives in *.
    repeat (find_apply_lem_hyp in_map_iff; expand_def).
    inv_prop succs_msg.
Qed.
Hint Resolve zave_invariant_keepalive.

Theorem zave_invariant_rectify :
  chord_rectify_invariant zave_invariant.
Proof.
  unfold zave_invariant.
  split; eauto.
  break_and.
  eapply msgs_state_principals_preserved; eauto;
    try solve [repeat handler_def; simpl; auto].
  intros; intuition eauto.
  repeat find_rewrite.
  find_apply_lem_hyp in_app_or; break_or_hyp; auto.
  exfalso.
  repeat handler_def; simpl in *; unfold send in *.
  find_apply_lem_hyp option_map_Some; expand_def.
  inv_prop succs_msg; congruence.
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
  assert (forall h, live_node gst h -> live_node gst' h).
  {
    intros.
    unfold live_node in *; expand_def.
    repeat find_rewrite.
    update_destruct; rewrite_update; subst.
    * intuition.
      eexists.
      split; [eauto|].
      repeat find_rewrite || find_injection.
      erewrite <- joined_preserved_by_request_timeout_handler; eauto.
    * eauto.
  }
  assert (forall h, live_node gst' h -> live_node gst h).
  {
    intros.
    unfold live_node in *; expand_def.
    repeat find_rewrite.
    update_destruct; rewrite_update; subst.
    * intuition.
      eexists.
      split; [eauto|].
      repeat find_rewrite || find_injection.
      erewrite -> joined_preserved_by_request_timeout_handler; eauto.
    * eauto.
  }
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
    match goal with
    | |- principal gst' ?p =>
      assert (principal gst p) by auto;
        invcs_prop principal; expand_def
    end.
    assert (live_node gst' h ->
            not_skipped (ChordIDSpace.hash h) (map id_of (succ_list st')) (ChordIDSpace.hash x0)).
    {
      intro.
      assert (sigma gst' h = Some st').
      repeat find_rewrite; rewrite_update; auto.
      autounfold in *.
      repeat find_rewrite.
      update_destruct; rewrite_update.
      repeat handler_def; simpl; eauto;
        repeat match goal with
             | |- not_skipped _ (map id_of ?rest) _ =>
               eapply remove_list_element_still_not_skipped
             | H: succ_list ?st = ?head :: ?rest
               |- not_skipped _ (?h :: map id_of ?rest) _ =>
               erewrite <- map_cons;
                 erewrite <- H;
                 eauto
             end;
      repeat match goal with
             | H: timeout_constraint _ _ _ |- _ =>
               invcs H
             | H: cur_request_timeouts_ok _ _ |- _ =>
               apply cur_request_timeouts_ok'_complete in H
             | H: cur_request_timeouts_ok' (cur_request ?st) ?timeouts,
               Heq: cur_request ?st = Some _ |- _ =>
               rewrite Heq in H
             | H: cur_request_timeouts_ok' (Some _) _ |- _ =>
               invcs H
             | H: query_request Stabilize ?x |- _ =>
               invcs H
             | H: In (Request _ GetPredAndSuccs) (timeouts gst _) |- _ =>
               eapply stabilize_only_with_first_succ in H; eauto; expand_def
             | H: hd_error (succ_list ?st) = Some _,
               Heq: succ_list ?st = _ :: _
               |- _ =>
               rewrite Heq in H; simpl in H; injc H
             end;
      repeat match goal with
             | H: live_node _ _ |- _ =>
               invcs H; expand_def
             | Hfailed: In (addr_of ?dead) (failed_nodes _),
               Hlive: ~ In ?principal (failed_nodes _)
              |- id_of ?ptr <> ChordIDSpace.hash ?principal =>
               intro; assert (principal = addr_of dead); [|congruence]
             | |- _ = addr_of _ =>
               eapply hash_injective_invariant; eauto using in_failed_in_nodes
             | |- context[ChordIDSpace.hash] =>
               change ChordIDSpace.hash with hash in *
             | |- hash ?h = hash (addr_of ?p) =>
               assert (Hwf: wf_ptr p)
                 by (eapply cur_request_valid; [| | eauto]; eauto);
                 rewrite <- Hwf; congruence
             end.
      eauto.
    }
    assert (no_live_node_skips gst' x0).
    {
      autounfold; intros; subst.
      repeat find_rewrite.
      update_destruct; rewrite_update; subst;
        repeat find_rewrite || find_injection;
        eauto.
    }
    unfold principal; repeat break_and_goal; eauto.
    autounfold; intros; subst.
    find_rewrite. find_apply_lem_hyp in_app_or; break_or_hyp.
    * find_copy_apply_lem_hyp in_map_iff; expand_def.
      unfold send in *; find_injection.
      find_eapply_lem_hyp responses_request_timeout_handler_accurate; eauto; subst.
      assert (sigma gst' src = Some st')
        by (repeat find_rewrite; rewrite_update; auto).
      eapply weaken_no_live_node_skips;
        try solve [econstructor 2; eauto
                  |congruence
                  |eauto].
    * find_eapply_prop no_msg_to_live_node_skips;
        repeat find_reverse_rewrite; eauto.
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
    assert (no_live_node_skips gst' x0).
    {
      autounfold; intros.
      assert (not_skipped (ChordIDSpace.hash h)
                          (map id_of (s1 :: succ_list st'))
                          (ChordIDSpace.hash x0))
        by (find_eapply_prop no_live_node_skips; eauto || congruence).
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
    }
    split; eauto.
    split; eauto.
    autounfold; intros; subst.
    find_rewrite. in_crush.
    * unfold send in *; find_injection.
      find_eapply_lem_hyp responses_request_timeout_handler_accurate; eauto; subst.
      find_eapply_prop no_live_node_skips; eauto.
      repeat find_rewrite; rewrite_update; auto.
    * find_eapply_prop no_msg_to_live_node_skips;
        repeat find_reverse_rewrite; eauto.
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
  - rewrite -> Forall_forall in *.
    intros.
    assert (principal gst p) by eauto.
    inv_prop principal; break_and.
    find_copy_apply_lem_hyp live_node_means_state_exists; expand_def.
    eapply principals_involves_joined_node_state_and_msgs_only;
      intuition eauto.
    + simpl in *; unfold send in *.
      break_or_hyp; auto.
      find_injection.
      inv_prop succs_msg; inv_prop client_payload.
  - intros; find_eapply_prop principal.
    eapply principals_involves_joined_node_state_and_msgs_only;
      intuition eauto.
    in_crush.
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
  - intros.
    rewrite -> Forall_forall in *.
    eapply principals_involves_joined_node_state_and_msgs_only;
      intuition eauto.
    simpl in *.
    repeat find_rewrite.
    in_crush.
  - intros.
    find_eapply_prop principal.
    eapply principals_involves_joined_node_state_and_msgs_only;
      intuition eauto.
    repeat find_rewrite.
    in_crush.
    exfalso.
    eapply LiveNodesNotClients.nodes_not_clients; eauto.
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
  autounfold in *; break_and.
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

(* Eventually this should only list the following "assumptions":

    succ_list_len_lower_bound : SUCC_LIST_LEN >= 2
    ocaml_hash : Chord.addr -> {s : String.string | String.length s = N}
    Chord.client_addr : String.string -> Prop
    SUCC_LIST_LEN : nat
    N : nat
*)
Print Assumptions zave_invariant_holds.
