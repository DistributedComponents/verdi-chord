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
  Variable bits : nat.
  Variable name : Type.
  Variable name_eq_dec :
      forall a b : name,
        {a = b} + {a <> b}.
  Variable id : Type.
  Variable id_eq_dec :
      forall a b : id,
        {a = b} + {a <> b}.
  Variable lt : id -> id -> bool.
  Variable hash : name -> id.
  Variable hash_inj : injective hash.
End IDSpaceParams.

Module IDSpace(P : IDSpaceParams).

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
    match P.lt a b, P.lt a x, P.lt x b with
    | true, true, true => true
    | false, true, _ => true
    | false, _, true => true
    | _, _, _ => false
    end.

  Lemma lt_antisymmetric :
    forall x y,
      P.lt x y = true ->
      ~ P.lt y x = true.
  Admitted.

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
    repeat break_if; try find_eapply_lem_hyp lt_antisymmetric;
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
