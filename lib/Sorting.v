Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.

(**
  Lightly adapted from Coq stdlib mergesort to not be a functor.
*)

Section Sorting.
  Variable t : Type.
  Variable le : t -> t -> bool.

  Variable le_reflexive :
    forall x, le x x = true.

  Variable le_transitive :
    forall x y z,
      le x y = true ->
      le y z = true ->
      le x z = true.

  Variable le_total :
    forall x y,
      le x y = true \/ le y x = true.

  Inductive sorted : list t -> Prop :=
  | SortedNil :
      sorted []
  | SortedSingleton :
      forall x, sorted [x]
  | SortedCons :
      forall x y l,
        sorted (y :: l) ->
        le x y = true ->
        sorted (x :: y :: l).

  (* from Coq stdlib mergesort implementation *)
  Fixpoint merge l1 l2 :=
    let fix merge_aux l2 :=
        match l1, l2 with
        | [], _ => l2
        | _, [] => l1
        | a1::l1', a2::l2' =>
          if le a1 a2
          then a1 :: merge l1' l2
          else a2 :: merge_aux l2'
        end
    in merge_aux l2.

  Definition tstack : Type := list (option (list t)).

  (* from Coq stdlib mergesort implementation *)
  Fixpoint merge_list_to_stack (stack : tstack) (l : list t) : tstack :=
    match stack with
    | [] => [Some l]
    | None :: stack' => Some l :: stack'
    | Some l' :: stack' => None :: merge_list_to_stack stack' (merge l' l)
    end.

  (* from Coq stdlib mergesort implementation *)
  Fixpoint merge_stack (stack : tstack) : list t :=
    match stack with
    | [] => []
    | None :: stack' => merge_stack stack'
    | Some l :: stack' => merge l (merge_stack stack')
    end.

  (* from Coq stdlib mergesort implementation *)
  Fixpoint iter_merge (stack : tstack) (l : list t) : list t :=
    match l with
    | [] => merge_stack stack
    | a::l' => iter_merge (merge_list_to_stack stack [a]) l'
    end.

  (* from Coq stdlib mergesort implementation *)
  Definition sort : list t -> list t :=
    iter_merge [].

  (* all proofs below from Coq stdlib mergesort implementation *)

  Local Ltac invert H := inversion H; subst; clear H.

  Fixpoint flatten_stack (stack : list (option (list t))) :=
    match stack with
    | [] => []
    | None :: stack' => flatten_stack stack'
    | Some l :: stack' => l ++ flatten_stack stack'
    end.

  Theorem Permuted_merge :
   forall l1 l2, Permutation (l1++l2) (merge l1 l2).
  Proof.
    induction l1; simpl merge; intro.
    - assert (forall l, (fix merge_aux (l0 : list t) : list t := l0) l = l)
      as -> by (destruct l; trivial). (* Technical lemma *)
      apply Permutation_refl.
    - induction l2.
      rewrite app_nil_r. apply Permutation_refl.
      destruct (le a a0).
        + constructor; apply IHl1.
        + apply Permutation_sym, Permutation_cons_app, Permutation_sym, IHl2.
  Qed.

  Theorem Permuted_merge_stack : forall stack,
    Permutation (flatten_stack stack) (merge_stack stack).
  Proof.
    induction stack as [|[]]; simpl.
    -  trivial.
    -  transitivity (l ++ merge_stack stack).
        + apply Permutation_app_head; trivial.
        + apply Permuted_merge.
    - assumption.
  Qed.

  Theorem Permuted_merge_list_to_stack :
    forall stack l,
      Permutation (l ++ flatten_stack stack)
                  (flatten_stack (merge_list_to_stack stack l)).
  Proof.
    induction stack as [|[]]; simpl; intros.
    - reflexivity.
    - rewrite app_assoc.
      etransitivity.
      + apply Permutation_app_tail.
        etransitivity.
        * apply Permutation_app_comm.
        * apply Permuted_merge.
      + apply IHstack.
    - reflexivity.
  Qed.

  Theorem Permuted_iter_merge : forall l stack,
    Permutation (flatten_stack stack ++ l) (iter_merge stack l).
  Proof.
    induction l; simpl; intros.
    - rewrite app_nil_r. apply Permuted_merge_stack.
    - change (a::l) with ([a]++l).
      rewrite app_assoc.
      etransitivity.
      +  apply Permutation_app_tail.
         etransitivity.
         apply Permutation_app_comm.
         apply Permuted_merge_list_to_stack.
      + apply IHl.
  Qed.

  Theorem sort_permutes :
    forall l l',
      l' = sort l ->
      Permutation l l'.
  Proof.
    intros; subst; apply (Permuted_iter_merge l []).
  Qed.

End Sorting.
