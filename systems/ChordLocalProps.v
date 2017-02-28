Require Import Omega.

Require Import Chord.Chord.
Import Chord.Chord.Chord.
Require Import StructTact.StructTactics.

(* Requests and responses *)
Inductive request_payload : payload -> Prop :=
| req_GetBestPredecessor : forall p, request_payload (GetBestPredecessor p)
| req_GetSuccList : request_payload GetSuccList
| req_GetPredAndSuccs : request_payload GetPredAndSuccs
| req_Ping : request_payload Ping.

Ltac request_payload_inversion :=
  match goal with
  | H : request_payload _ |- _ => inv H
  end.

Inductive response_payload : payload -> Prop :=
| res_GotBestPredecessor : forall p, response_payload (GotBestPredecessor p)
| res_GotSuccList : forall l, response_payload (GotSuccList l)
| res_GotPredAndSuccs : forall p l, response_payload (GotPredAndSuccs p l)
| res_Pong : response_payload Pong
| res_Busy : response_payload Busy.

Inductive request_response_pair : payload -> payload -> Prop :=
| pair_GetBestPredecessor : forall n p, request_response_pair (GetBestPredecessor n) (GotBestPredecessor p)
| pair_GetSuccList : forall l, request_response_pair GetSuccList (GotSuccList l)
| pair_GetPredAndSuccs : forall p l, request_response_pair GetPredAndSuccs (GotPredAndSuccs p l)
| pair_Ping : request_response_pair Ping Pong.

Lemma is_request_same_as_request_payload : forall msg : payload,
    is_request msg = true <-> request_payload msg.
Proof.
  unfold is_request.
  intuition.
  - break_match;
      discriminate || eauto using req_GetBestPredecessor, req_GetSuccList, req_GetPredAndSuccs, req_Ping.
  - now request_payload_inversion.
Qed.

(* Safe messages (Notify and Ping) *)
Lemma safe_msgs :
  forall msg,
    is_safe msg = true ->
    msg = Ping \/ msg = Notify.
Proof.
  unfold is_safe.
  intuition.
  break_match; auto || discriminate.
Qed.

Lemma only_safe_request_is_Ping :
  forall msg,
    request_payload msg ->
    is_safe msg = true ->
    msg = Ping.
Proof.
  intuition.
  request_payload_inversion;
    find_apply_lem_hyp safe_msgs;
    break_or_hyp;
    auto || discriminate.
Qed.

Lemma unsafe_msgs_not_safe_ones :
  forall msg,
    is_safe msg = false ->
    msg <> Notify /\ msg <> Ping.
Proof.
  unfold is_safe.
  intuition;
    break_match;
    easy.
Qed.
