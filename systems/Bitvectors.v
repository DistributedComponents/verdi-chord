Require Import Bvector.
Require Vector.
Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.

Definition ascii_to_vec (a : Ascii.ascii) : Bvector 8 :=
  let (b1, b2, b3, b4, b5, b6, b7, b8) := a in
  Vector.of_list [b1; b2; b3; b4; b5; b6; b7; b8].

Lemma string_to_vec_helper :
  forall a s,
    8 + 8 * (String.length s) = 8 * String.length (String a s).
Proof using.
  intros.
  simpl.
  now repeat rewrite plus_n_Sm.
Qed.

Fixpoint string_to_vec (s : string) : Bvector (8 * String.length s).
Proof using.
  refine match s as s' return Bvector (8 * String.length s') with
         | EmptyString => Bnil
         | String a s' =>
           let bv := string_to_vec s' in
           _
         end.
  rewrite <- (string_to_vec_helper a s').
  exact (Vector.append (ascii_to_vec a) bv).
Defined.

Definition fixed_length_string_to_vec {n : nat} (asc : { s : string | String.length s = n }) : Bvector (8 * n).
  destruct asc as [str pf].
  rewrite <- pf.
  exact (string_to_vec str).
Defined.

Definition bvec8_to_list (byte : Bvector.Bvector 8) : list bool :=
  Vector.to_list byte.

Fixpoint bit_list_to_string (bits : list bool) : string :=
  match bits with
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest =>
    let a := Ascii.Ascii b1 b2 b3 b4 b5 b6 b7 b8 in
    String a (bit_list_to_string rest)
  | _ => String.EmptyString
  end.

Definition vec_to_string {n : nat} (b : Bvector n) : string :=
  bit_list_to_string (Vector.to_list b).
