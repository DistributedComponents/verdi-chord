Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import InfSeqExt.infseq.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.
Require Import Chord.QueryInvariant.

Set Bullet Behavior "Strict Subproofs".

Definition circular_wait : occurrence -> Prop.
(* This is Ryan's problem. *)
Admitted.

Definition busy_if_live (h : addr) (occ : occurrence) :=
  forall st,
    live_node (occ_gst occ) h ->
    sigma (occ_gst occ) h = Some st ->
    cur_request st <> None.

Definition not_busy_if_live (h : addr) (occ : occurrence) :=
  forall st,
    live_node (occ_gst occ) h ->
    sigma (occ_gst occ) h = Some st ->
    cur_request st = None.

Theorem queries_eventually_stop' :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall st dstp q m,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      always (~_ (now circular_wait)) ex ->
      eventually (now (fun o => forall st',
                           sigma (occ_gst o) h = Some st' /\
                           cur_request st' = None)) ex.
Proof.
  intros.
  assert (exists st__dst, sigma (occ_gst (hd ex)) (addr_of dstp) = Some st__dst) by admit.
  break_exists_name st__dst.
  set (gst := occ_gst (hd ex)).
  assert (query_message_ok h (addr_of dstp) (cur_request st) (delayed_queries st__dst)
                           (channel gst h (addr_of dstp)) (channel gst (addr_of dstp) h))
    by eauto using query_message_ok_invariant.
  inv_prop query_message_ok.
  - congruence.
  - congruence.
  - repeat (find_rewrite || find_injection).
    admit.
  - admit.
  - admit.
Admitted.

(** the big assumption for inf_often stabilization *)
Theorem queries_eventually_stop :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    busy_if_live h (hd ex) ->
    always (~_ (now circular_wait)) ex ->
    eventually (now (not_busy_if_live h)) ex.
Proof.
  intros.
  inv_prop live_node; repeat (break_exists || break_and).
  copy_eapply_prop_hyp busy_if_live live_node;
    forwards; eauto; concludes; eauto.
  destruct (cur_request x) as [[[? ?] ?]|] eqn:?; try congruence.
  find_eapply_lem_hyp queries_eventually_stop'; eauto.
  eapply eventually_monotonic_simple; try eassumption.
  destruct s; unfold not_busy_if_live.
  simpl; firstorder.
(*
This is tricky.

  If you have an open request, you're in the middle of some operation.
  Operations (stabilization, rectifying, etc) undertaken by joined nodes complete
  in finitely many request-response pairs.
  A request eventually gets a response if there are no circular waits...

DIFFICULTY: Ryan
USED: In phase one for the proof of eventual stabilization.
*)
Qed.
