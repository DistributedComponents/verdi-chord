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
  Variable name : Type.
  Variable id : Type.
  Variable hash : name -> id.
  Variable ltb : id -> id -> bool.
  Variable lt : id -> id -> Prop.

  (* problematic (i.e. untrue) hypothesis, there might be a better way to handle this *)
  Variable hash_inj : injective hash.

  (* name and id have decidable equality *)
  Variable name_eq_dec :
      forall a b : name,
        {a = b} + {a <> b}.
  Variable id_eq_dec :
      forall a b : id,
        {a = b} + {a <> b}.

  (* useful notations for lt and ltb *)
  Notation "a < b" := (lt a b) (at level 70).
  Notation "a < b < c" := (and (lt a b) (lt b c)).
  Notation "a <? b <? c" := (andb (ltb a b) (ltb b c)) (at level 70).
  Notation "a <? b" := (ltb a b) (at level 70).

  (* ltb is a decision procedure for the lt relation *)
  Variable ltb_correct :
    forall a b,
      a <? b = true <-> a < b.

  (* The lt relation is a strict total order *)
  Variable lt_asymm :
    forall a b,
      a < b ->
      ~ b < a.
  Variable lt_trans :
    forall a b c,
      a < b ->
      b < c ->
      a < c.
  Variable lt_irrefl :
    forall a,
      ~ a < a.
  Variable lt_total :
    forall a b,
      a < b \/ b < a \/ a = b.
End IDSpaceParams.

Module IDSpace(P : IDSpaceParams).

  Include P.

  Notation "a < b" := (P.lt a b) (at level 70).
  Notation "a < b < c" := (and (P.lt a b) (P.lt b c)).
  Notation "a <? b <? c" := (andb (P.ltb a b) (P.ltb b c)) (at level 70).
  Notation "a <? b" := (P.ltb a b) (at level 70).

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

  Lemma make_pointer_correct_addr :
    forall p a,
      p = make_pointer a ->
      addr_of p = a.
  Proof using.
    intros.
    now find_rewrite.
  Qed.

  Lemma make_pointer_correct_id :
    forall p a,
      p = make_pointer a ->
      id_of p = P.hash a.
  Proof using.
    intros.
    now find_rewrite.
  Qed.

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
        a < x < b ->
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

  Lemma unrolling_makes_h_least :
    forall h x,
      unroll_between h h x = true.
  Proof using.
    unfold unroll_between.
    intros.
    repeat break_if;
      congruence.
  Qed.

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
  Admitted.

  Lemma unrolling_total :
    forall h x y,
      unroll_between h x y = true \/
      unroll_between h y x = true.
  Proof using.
    unfold unroll_between, between_bool.
    intros.
  Admitted.

  Lemma unrolling_reflexive :
    forall h x,
      unroll_between h x x = true.
  Admitted.

  Definition unroll_between_ptr (h : P.name) (a b : pointer) :=
    unroll_between (P.hash h) (ptrId a) (ptrId b).

End IDSpace.
