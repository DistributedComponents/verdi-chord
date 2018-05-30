Require Import List.
Import ListNotations.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.

Definition has_pred (gst : global_state) (h : addr) (p : option pointer) : Prop :=
  exists st,
    sigma gst h = Some st /\
    pred st = p.

Lemma has_pred_intro :
  forall gst h p st,
    sigma gst h = Some st ->
    pred st = p ->
    has_pred gst h p.
Proof.
  unfold has_pred.
  eauto.
Qed.
