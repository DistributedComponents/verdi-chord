Require Import StructTact.StructTactics.

(* This file defines and provides some lemmas about identifier spaces.
 * The space of all identifiers produced by a given hash function is cyclically
 * ordered. However, this cyclic ordering can be unrolled into a linear one. All
 * operations defined on identifiers are lifted to pointers, which are pairs of
 * a name and the hash of that name, i.e., its identifier. *)

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall a b,
    f a = f b ->
    a = b.

Module Type IDSpaceParams.
  Parameter name : Type.
  Parameter id : Type.
  Parameter hash : name -> id.
  Parameter ltb : id -> id -> bool.
  Parameter lt : id -> id -> Prop.

  (* name and id have decidable equality *)
  Parameter name_eq_dec :
      forall a b : name,
        {a = b} + {a <> b}.
  Parameter id_eq_dec :
      forall a b : id,
        {a = b} + {a <> b}.

  (* useful notations for lt and ltb *)
  Notation "a < b < c" := (and (lt a b) (lt b c)) (at level 70, b at next level) : id_scope.
  Notation "a < b" := (lt a b) (at level 70) : id_scope.
  Notation "a <? b <? c" := (andb (ltb a b) (ltb b c)) (at level 70, b at next level) : id_scope.
  Notation "a <? b" := (ltb a b) (at level 70) : id_scope.
  Delimit Scope id_scope with id.
  Local Open Scope id_scope.

  (* ltb is a decision procedure for the lt relation *)
  Parameter ltb_correct :
    forall a b,
      a <? b = true <-> a < b.

  (* The lt relation is a strict total order *)
  Parameter lt_asymm :
    forall a b,
      a < b ->
      ~ b < a.
  Parameter lt_trans :
    forall a b c,
      a < b ->
      b < c ->
      a < c.
  Parameter lt_irrefl :
    forall a,
      ~ a < a.
  Parameter lt_total :
    forall a b,
      a < b \/ b < a \/ a = b.
End IDSpaceParams.

Module IDSpace(P : IDSpaceParams).

  Include P.
  Local Open Scope id_scope.

  Record pointer :=
    mkPointer { ptrId : P.id;
                ptrAddr : P.name }.

  Definition make_pointer (n : P.name) : pointer :=
    {| ptrId := P.hash n;
       ptrAddr := n |}.

  Definition id_of : pointer -> P.id :=
    ptrId.

  Definition addr_of : pointer -> P.name :=
    ptrAddr.

  Definition pointer_eq_dec : forall x y : pointer,
      {x = y} + {x <> y}.
  Proof using.
    intros.
    repeat decide equality;
      auto using P.id_eq_dec, P.name_eq_dec.
  Defined.

  (* true iff x in (a, b) on some sufficiently large "circle" *)
  Definition between_bool (a x b : P.id) : bool :=
    match a <? b, a <? x, x <? b with
    | true, true, true => true
    | false, true, _ => true
    | false, _, true => true
    | _, _, _ => false
    end.

  (* between_bool as a relation *)
  Inductive between : P.id -> P.id -> P.id -> Prop :=
  | BetweenMono :
      forall a x b,
        a < x ->
        x < b ->
        between a x b
  | BetweenWrapL :
      forall a x b,
        ~ a < b ->
        a < x ->
        between a x b
  | BetweenWrapR :
      forall a x b,
        ~ a < b ->
        x < b ->
        between a x b.
  Hint Constructors between.

  Ltac inv_between :=
    match goal with
    | [H: between _ _ _ |- _] => inv H
    end.

  Lemma ltb_true_lt :
    forall a b,
      a <? b = true ->
      a < b.
  Proof.
    apply P.ltb_correct.
  Qed.

  Lemma ltb_false_lt :
    forall a b,
      a <? b = false ->
      ~ a < b.
  Proof.
    intuition.
    find_apply_lem_hyp P.ltb_correct.
    congruence.
  Qed.

  Lemma lt_true_ltb :
    forall a b,
      a < b ->
      a <? b = true.
  Proof.
    apply P.ltb_correct.
  Qed.

  Lemma lt_false_ltb :
    forall a b,
      ~ a < b ->
      a <? b = false.
  Proof.
    intros.
    destruct (a <? b) eqn:?H;
      try find_apply_lem_hyp P.ltb_correct;
      congruence.
  Qed.

  Ltac ltb_to_lt :=
    repeat
      match goal with
      (* rewrite in goal *)
      | [ |- ?a <? ?b = true ] =>
        apply (lt_true_ltb a b)
      | [ |- ?a <? ?b = false ] =>
        apply (lt_false_ltb a b)
      (* flip goal if that doesn't work *)
      | [ |- true = ?a <? ?b ] =>
        symmetry
      | [ |- false = ?a <? ?b ] =>
        symmetry
      (* rewrite in hypotheses *)
      | [ H : (?a <? ?b) = true |- _ ] =>
        apply (ltb_true_lt a b) in H
      | [ H : (?a <? ?b) = false |- _ ] =>
        apply (ltb_false_lt a b) in H
      (* flip hypotheses if that doesn't work *)
      | [ H : true = (?a <? ?b) |- _ ] =>
        symmetry in H
      | [ H : false = (?a <? ?b) |- _ ] =>
        symmetry in H
      end.

  Lemma between_between_bool_equiv :
    forall a x b,
      between a x b <-> between_bool a x b = true.
  Proof.
    unfold between_bool.
    intros.
    split; intros.
    - inv_between;
        repeat break_if;
        ltb_to_lt;
        break_and;
        congruence.
    - repeat break_if;
        ltb_to_lt;
        (constructor; tauto) || congruence.
  Qed.

  Lemma between_bool_between :
    forall a x b,
      between_bool a x b = true ->
      between a x b.
  Proof.
    apply between_between_bool_equiv.
  Qed.

  Definition ptr_between (a x b : pointer) : Prop :=
    between (ptrId a) (ptrId x) (ptrId b).

  Definition ptr_between_bool (a x b : pointer) : bool :=
    between_bool (ptrId a) (ptrId x) (ptrId b).

  (* this is a total linear less-than-or-equal relation, see proofs below *)
  Definition unroll_between (h : P.id) (x y : P.id) : bool :=
    if P.id_eq_dec h x
    then true
    else if P.id_eq_dec h y
         then false
         else if P.id_eq_dec x y
              then true
              else between_bool h x y.

  Lemma between_bool_yz_antisymmetric :
    forall x y z,
      between_bool x y z = true ->
      ~ between_bool x z y = true.
  Proof using.
    unfold between_bool.
    intros.
    repeat break_if;
      ltb_to_lt;
      try find_eapply_lem_hyp P.lt_asymm;
      congruence.
  Qed.

  Lemma between_bool_yz_total :
    forall x y z,
      between_bool x y z = true \/ between_bool x z y = true \/ y = z.
  Proof.
    unfold between_bool.
    intros.
    repeat break_if; ltb_to_lt;
      tauto || firstorder using P.lt_total.
  Qed.

  Lemma unrolling_antisymmetric :
    forall h x y,
      unroll_between h x y = true ->
      unroll_between h y x = true ->
      x = y.
  Proof using.
    unfold unroll_between.
    intros.
    repeat break_if;
      try find_eapply_lem_hyp between_bool_yz_antisymmetric;
      congruence.
  Qed.

  Lemma unrolling_transitive :
    forall h x y z,
      unroll_between h x y = true ->
      unroll_between h y z = true ->
      unroll_between h x z = true.
  Proof.
    unfold unroll_between.
    intros.
    repeat break_if; try congruence.
    repeat find_apply_lem_hyp between_bool_between.
    apply between_between_bool_equiv.
    repeat invcs_prop between;
      eauto using P.lt_trans, BetweenMono, BetweenWrapL, BetweenWrapR.
    congruence.
  Qed.

  Lemma unrolling_total :
    forall h x y,
      unroll_between h x y = true \/
      unroll_between h y x = true.
  Proof using.
    unfold unroll_between.
    intros.
    repeat break_if;
      congruence || firstorder using between_bool_yz_total.
  Qed.

  Lemma unrolling_reflexive :
    forall h x,
      unroll_between h x x = true.
  Proof.
    intros.
    unfold unroll_between.
    repeat break_if; congruence.
  Qed.

  Definition unroll_between_ptr (h : P.name) (a b : pointer) :=
    unroll_between (P.hash h) (ptrId a) (ptrId b).

  Lemma not_between_xxy :
    forall x y,
      ~ between x x y.
  Proof.
    intros; intro.
    inv_prop between;
      solve [tauto | eapply lt_irrefl; eauto].
  Qed.

  Lemma not_between_xyy :
    forall x y,
      ~ between x y y.
  Proof.
    intros; intro.
    inv_prop between;
      solve [tauto | eapply lt_irrefl; eauto].
  Qed.

  Ltac id_auto := eauto using lt_asymm, lt_irrefl, lt_trans.

  Lemma between_xyx :
    forall x y,
      x <> y ->
      between x y x.
  Proof.
    intros.
    pose proof (lt_total x y); repeat break_or_hyp;
      congruence || id_auto.
  Qed.

  Lemma lt_asymm_neg :
    forall x y,
      ~ lt x y ->
      lt y x \/ x = y.
  Proof.
    intros.
    pose proof (lt_total x y).
    repeat break_or_hyp; tauto.
  Qed.

  Lemma between_rot_l :
    forall x y z,
      x <> z ->
      between x y z ->
      between y z x.
  Proof.
    intros.
    invcs_prop between;
      id_auto;
      find_copy_apply_lem_hyp lt_asymm_neg;
      break_or_hyp;
      congruence || id_auto.
  Qed.

  Lemma between_rot_r :
    forall x y z,
      x <> z ->
      between x y z ->
      between z x y.
  Proof.
    intros.
    invcs_prop between;
      id_auto;
      find_copy_apply_lem_hyp lt_asymm_neg;
      break_or_hyp;
      congruence || id_auto.
  Qed.

  Lemma not_between_cases :
    forall x y z,
      ~ between x y z ->
      x = y \/ y = z \/ between z y x.
  Proof.
    intros.
    pose proof (lt_total x y).
    pose proof (lt_total y z).
    pose proof (lt_total z x).
    repeat break_or_hyp;
      intuition solve [tauto | id_auto |  congruence | find_false; id_auto].
  Qed.

  Lemma between_bool_false_not_between :
    forall x y z,
      between_bool x y z = false ->
      ~ between x y z.
  Proof.
    intuition.
    find_apply_lem_hyp between_between_bool_equiv.
    congruence.
  Qed.
  Hint Resolve between_bool_false_not_between.

  Lemma unrolled_not_between_rot :
    forall x y z,
      unroll_between z x y = false ->
      ~ between x y z.
  Proof.
    intros.
    unfold unroll_between in *.
    repeat break_if; try congruence.
    - subst.
      apply not_between_xyy.
    - intro.
      eapply between_bool_false_not_between;
        eauto using between_rot_r.
  Qed.

  Lemma not_between_swap :
    forall x y z,
      y <> z ->
      ~ between x y z ->
      between x z y.
  Proof.
    intros.
    find_copy_apply_lem_hyp not_between_cases.
    repeat break_or_hyp.
    - now apply between_xyx.
    - congruence.
    - pose proof (lt_total x z).
      pose proof (lt_total x y).
      pose proof (lt_total y z).
      repeat break_or_hyp;
        intuition solve [id_auto | congruence | find_false; id_auto].
  Qed.

  Lemma not_between_between :
    forall x y z,
      unroll_between x y z = false ->
      between z y x.
  Proof.
    unfold unroll_between.
    intros.
    repeat break_if; subst; try congruence.
    - now apply between_xyx.
    - apply between_rot_r; auto.
      apply between_rot_r;
        auto using not_between_swap.
  Qed.

End IDSpace.
