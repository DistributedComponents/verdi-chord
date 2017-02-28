Require Import List.

Require Import Chord.Chord.
Import Chord.Chord.Chord.
Import ChordIDSpace.
Require Import Chord.ChordProof.
Require Import Chord.ChordSemantics.
Import ChordSemantics.

Definition live (gst : global_state) (p : pointer) :=
  In (addr_of p) (nodes gst) /\
  ~ In (addr_of p) (failed_nodes gst).

Definition correct_succs (gst : global_state) (h : pointer) (succs : list pointer) : Prop :=
  forall s xs ys s',
    succs = xs ++ s :: ys ->
    ptr_between h s' s ->
    live gst s' ->
    In s' xs.

Definition full_succs (gst : global_state) (h : pointer) (succs : list pointer) : Prop :=
  length succs = Chord.SUCC_LIST_LEN.

Definition correct_pred (gst : global_state) (h : pointer) (p : option pointer) : Prop :=
  exists p0,
    p = Some p0 /\
    forall p',
      live gst p' ->
      ~ ptr_between p0 p' h.

Definition ideal (gst : global_state) : Prop :=
  forall h st,
    live gst h ->
    sigma gst (addr_of h) = Some st ->
    correct_succs gst h (succ_list st) /\
    full_succs gst h (succ_list st) /\
    correct_pred gst h (pred st).

Definition deadlock_free : infseq.infseq occurrence -> Prop.
Admitted.

Theorem chord_stabilization :
  forall ex : infseq.infseq occurrence,
    reachable_st (occ_gst (infseq.hd ex)) ->
    lb_execution ex ->
    weak_local_fairness ex ->
    deadlock_free ex ->
    infseq.eventually
      (infseq.always
         (fun ex' => (ideal (occ_gst (infseq.hd ex')))))
      ex.
Admitted.
