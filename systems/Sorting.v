Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.

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

  Theorem sort_makes_sorted :
    forall l l',
      l' = sort l ->
      sorted l'.
  Admitted.

  Theorem sort_permutes :
    forall l l',
      l' = sort l ->
      Permutation l l'.
  Admitted.

End Sorting.
