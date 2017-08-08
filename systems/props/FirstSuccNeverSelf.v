Require Import List.
Import ListNotations.

Require Import Chord.Chord.

Require Import Chord.ChordSystemReachable.

Definition has_first_succ (gst : global_state) (h : addr) (s : pointer) : Prop :=
  exists st,
    sigma gst h = Some st /\
    hd_error (succ_list st) = Some s.

Lemma has_first_succ_intro :
  forall gst h s st,
    sigma gst h = Some st ->
    hd_error (succ_list st) = Some s ->
    has_first_succ gst h s.
Proof.
  intros.
  eexists; eauto.
Qed.

Theorem first_succ_never_self :
  forall gst h s,
    reachable_st gst ->
    has_first_succ gst h s ->
    h <> (addr_of s).
Proof.
(*
Easy consequence of the (difficult) Zave invariant.

DIFFCULTY: 1
USED: In phase two.
*)
Admitted.
