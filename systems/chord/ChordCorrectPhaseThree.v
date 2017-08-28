Require Import List.
Import ListNotations.
Require Import Omega.

Require Verdi.Coqlib.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.

Require Import InfSeqExt.infseq.

Require Import Chord.InfSeqTactics.

Require Import Chord.Chord.

Require Import Chord.LabeledLemmas.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.
Require Import Chord.LabeledMeasures.

Require Import Chord.ValidPointersInvariant.
Require Import Chord.QueriesEventuallyStop.

Require Import Chord.ChordCorrectPhaseOne.
Require Import Chord.ChordCorrectPhaseTwo.

Set Bullet Behavior "Strict Subproofs".
Open Scope nat_scope.

(** Phase three: all successors become correct. *)
Definition all_in_dec
           {A : Type}
           (A_eq_dec : forall x y : A, {x = y} + {x <> y})
           (l1 l2 : list A) :=
  Forall_dec _ (fun a => In_dec A_eq_dec a l2) l1.

(* doesn't deal with possiblity of length of the successor list being longer
   than SUCC_LIST_LEN *)
Fixpoint succs_error_helper (gst : global_state) (h : pointer) (xs ys : list pointer) (suffix_len : nat) :=
  match ys with
  | [] => suffix_len
  | s :: ys' =>
    let xs' := filter (better_succ_bool h s) (live_ptrs gst) in
    if all_in_dec pointer_eq_dec xs' xs
    then succs_error_helper gst h (s :: xs) ys' (suffix_len - 1)
    else suffix_len
  end.

Definition succs_error (h : addr) (gst : global_state) :=
  match sigma gst h with
  | Some st =>
    succs_error_helper gst (make_pointer h) [] (succ_list st) Chord.SUCC_LIST_LEN
  | None =>
    Chord.SUCC_LIST_LEN + 1
  end.

Definition correct_succs (gst : global_state) (h : pointer) (st : data) : Prop :=
  forall s xs ys s',
    wf_ptr h ->
    succ_list st = xs ++ s :: ys ->
    ptr_between h s' s ->
    live_node gst (addr_of s') ->
    In s' xs.

Definition all_succs_correct (gst : global_state) : Prop :=
  forall h st,
    sigma gst (addr_of h) = Some st ->
    live_node gst (addr_of h) ->
    wf_ptr h ->
    correct_succs gst h st /\
    length (succ_list st) = Chord.SUCC_LIST_LEN.

Theorem phase_three :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    always (~_ (now circular_wait)) ex ->
    continuously (lift_gpred_to_ex all_succs_correct) ex.
Proof.
Admitted.
