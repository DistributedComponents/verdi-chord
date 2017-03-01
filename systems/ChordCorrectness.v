Require Import List.

Require Import Chord.Chord.
Import Chord.Chord.Chord.
Import ChordIDSpace.
Require Import Chord.ChordProof.
Require Import Chord.ChordSemantics.
Import ChordSemantics.
Import ConstrainedChord.

Definition live (gst : global_state) (p : pointer) :=
  In (addr_of p) (nodes gst) /\
  ~ In (addr_of p) (failed_nodes gst).

Definition correct_succs
           (gst : global_state)
           (h : pointer)
           (succs : list pointer) : Prop :=
  forall s xs ys s',
    succs = xs ++ s :: ys ->
    ptr_between h s' s ->
    live gst s' ->
    In s' xs.

Definition full_succs (gst : global_state) (h : pointer) (succs : list pointer) : Prop :=
  length succs = Chord.SUCC_LIST_LEN.

Print best_succ.

(* cf. zave page 11 *)
Definition first_succ_is_best_succ (gst : global_state) (h : addr) :=
  exists st s rest,
    sigma gst h = Some st /\
    succ_list st = s :: rest /\
    best_succ gst h (addr_of s).

Definition all_first_succs_best (gst : global_state) :=
  forall h,
    live gst h ->
    first_succ_is_best_succ gst (addr_of h).

Definition eventually_always_net
           (P : global_state -> Prop) : infseq.infseq occurrence -> Prop :=
  infseq.eventually
    (infseq.always
       (fun ex' => P (occ_gst (infseq.hd ex')))).

Definition phase_one (ex : infseq.infseq occurrence) :=
  lb_execution ex ->
  reachable_st (occ_gst (infseq.hd ex)) ->
  eventually_always_net all_first_succs_best ex.
 

Definition correct_pred (gst : global_state) (h : pointer) (p : option pointer) : Prop :=
  exists p0,
    p = Some p0 /\
    forall p',
      live gst p' ->
      ~ ptr_between p0 p' h.

Definition correct_pointers gst :=
  forall h st,
    correct_pred gst h (pred st) /\
    full_succs gst h (succ_list st) /\
    correct_succs gst h (succ_list st).
 
Definition phase_two (ex : infseq.infseq occurrence) :=
  lb_execution ex ->
  reachable_st (occ_gst (infseq.hd ex)) ->
  eventually_always_net correct_pointers ex.

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

