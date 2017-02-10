Require Bool.Bvector.
Require Vectors.VectorEq.
Require Import ZArith.
Require Zdigits.
Require Omega.
Require Import List.
Import List.ListNotations.
Require String.
Require Import StructTact.StructTactics.

(* This file defines and provides some lemmas about identifier spaces. An
 * identifier is the hash of a name, which is a string. The space of all
 * identifiers produced by a given hash function is cyclically ordered.
 * However, this cyclic ordering can be unrolled into a linear one. All
 * operations defined on identifiers are lifted to pointers, which are pairs of
 * a name and the hash of that name, i.e., its identifier. *)

Section IdentifierSpaces.
  Variable N : nat.
  Definition id := Bvector.Bvector N.
  Definition name := String.string.
  Variable hash : name -> id.
  Record pointer := mkPointer { ptrId : id;
                                ptrAddr : name }.

  Definition make_pointer (n : name) : pointer :=
    {| ptrId := hash n;
       ptrAddr := n |}.

  Definition id_of : pointer -> id :=
    ptrId.

  Definition addr_of : pointer -> name :=
    ptrAddr.

  Lemma make_pointer_correct_addr :
    forall p a,
      p = make_pointer a ->
      addr_of p = a.
  Proof.
    intros.
    now find_rewrite.
  Qed.

  Lemma make_pointer_correct_id :
    forall p a,
      p = make_pointer a ->
      id_of p = hash a.
  Proof.
    intros.
    now find_rewrite.
  Qed.

  Definition id_eq_dec : forall a b : id, {a = b} + {a <> b} :=
    VectorEq.eq_dec _ Bool.eqb Bool.eqb_true_iff _.

  Definition pointer_eq_dec : forall x y : pointer,
      {x = y} + {x <> y}.
  Proof.
    intros.
    repeat decide equality;
      apply id_eq_dec.
  Defined.

  Definition z_of_id : id -> Z :=
    Zdigits.binary_value N.

  Definition id_of_z : Z -> id :=
    Zdigits.Z_to_binary N.

  Lemma z_of_id_inv :
    forall x,
      id_of_z (z_of_id x) = x.
  Proof.
    unfold id_of_z, z_of_id.
    apply Zdigits.binary_to_Z_to_binary.
  Qed.

  Definition bv_ltb (x y : id) : bool :=
    Z.ltb (z_of_id x) (z_of_id y).

  (* true iff x in (a, b) on some sufficiently large "circle" *)
  Definition between_bool (a x b : id) : bool :=
    match bv_ltb a b, bv_ltb a x, bv_ltb x b with
    | true, true, true => true
    | false, true, _ => true
    | false, _, true => true
    | _, _, _ => false
    end.

  Lemma bv_ltb_antisymmetric :
    forall x y,
      bv_ltb x y = true ->
      ~ bv_ltb y x = true.
  Proof.
    unfold bv_ltb in *.
    intros.
    rewrite Z.ltb_lt in *.
    omega.
  Qed.

  Definition ptr_between_bool (a x b : pointer) : bool :=
    between_bool (ptrId a) (ptrId x) (ptrId b).

  (* this is a total linear less-than-or-equal relation, see proofs below *)
  Definition unroll_between (h : id) (x y : id) : bool :=
    if id_eq_dec h x
    then true
    else if id_eq_dec h y
         then false
         else if id_eq_dec x y
              then true
              else between_bool h x y.

  Lemma unrolling_makes_h_least :
    forall h x,
      unroll_between h h x = true.
  Proof.
    unfold unroll_between.
    intros.
    break_if; auto.
  Qed.

  Lemma between_bool_yz_antisymmetric :
    forall x y z,
      between_bool x y z = true ->
      ~ between_bool x z y = true.
  Proof.
    unfold between_bool.
    intros.
    repeat break_if; try find_eapply_lem_hyp bv_ltb_antisymmetric;
      congruence.
  Qed.

  Lemma unrolling_antisymmetric :
    forall h x y,
      unroll_between h x y = true ->
      unroll_between h y x = true ->
      x = y.
  Proof.
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
    unfold unroll_between, between_bool.
    intros.
    repeat break_if; try subst; try congruence;
    unfold bv_ltb in *;
    rewrite Z.ltb_lt, Z.ltb_nlt in *;
    omega.
  Qed.

  Lemma neq_in_id_implies_neq_in_z :
    forall x y : id,
      x <> y ->
      z_of_id x <> z_of_id y.
  Proof.
    intros.
    intro.
    find_apply_lem_hyp (f_equal id_of_z).
    repeat rewrite z_of_id_inv in *.
    congruence.
  Qed.

  Lemma unrolling_total :
    forall h x y,
      unroll_between h x y = true \/
      unroll_between h y x = true.
  Proof.
    unfold unroll_between, between_bool.
    intros.
    repeat break_if; try subst; try congruence; auto;
      unfold bv_ltb in *;
      try rewrite Z.ltb_lt, Z.ltb_nlt in *;
      find_apply_lem_hyp neq_in_id_implies_neq_in_z;
      try omega.
      rewrite Z.ltb_nlt in *.
      find_apply_lem_hyp neq_in_id_implies_neq_in_z;
      try omega.
  Qed.

  Lemma unrolling_reflexive :
    forall h x,
      unroll_between h x x = true.
  Proof.
    unfold unroll_between, between_bool.
    intros.
    repeat break_if; try omega || subst; auto; try congruence.
  Qed.

  Definition unroll_between_ptr (h : name) (a b : pointer) :=
    unroll_between (hash h) (ptrId a) (ptrId b).

End IdentifierSpaces.
