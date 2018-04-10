Require Import String.
Require Import List.
Import List.ListNotations.
Require Bvector.
Require ZArith.
Require Zdigits.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import Verdi.DynamicNet.
Require Import Cheerios.Cheerios.

Require Import Chord.Chord.
Require Import Chord.Sorting.
Require Import Chord.IDSpace.
Require Import Chord.Bitvectors.

Import DeserializerNotations.

Import FunctionalExtensionality.

(* types *)
Module Type SerializableSystem.
  Include ConstrainedDynamicSystem.
  Parameter payload_serializer : Serializer payload.
  Parameter default_payload : payload. (* in case deserialization fails but value needed (avoid) *)
End SerializableSystem.

Module SerializedSystem (S : SerializableSystem) <: ConstrainedDynamicSystem.
  Definition addr := S.addr.
  Definition client_addr := S.client_addr.
  Definition client_addr_dec := S.client_addr_dec.
  Definition addr_eq_dec := S.addr_eq_dec.

  Definition payload := IOStreamWriter.wire.
  Definition payload_eq_dec := IOStreamWriter.wire_eq_dec.

  Definition revert_payload p := match deserialize_top deserialize p with
                                 | Some p => p
                                 | None => S.default_payload
                                 end.

  Definition serialized_client_payload (p : payload) : Prop :=
    exists p' : S.payload, @deserialize_top S.payload (@deserialize S.payload _) p = Some p' /\ S.client_payload p'.

  Definition client_payload := serialized_client_payload.

  Lemma client_payload_dec : forall (p : payload), {client_payload p} + {~ client_payload p}.
  Proof.
    intros.
    destruct (deserialize_top deserialize p) eqn:H.
    - destruct (S.client_payload_dec p0) eqn:G.
      + unfold client_payload.
        left.
        unfold serialized_client_payload.
        exists p0.
        auto.
      + right.
        unfold not.
        intros.
        unfold client_payload in *.
        unfold client_payload in *.
        match goal with
        | H : context[serialized_client_payload] |- _ => destruct H
        end.
        break_exists.
        break_and.
        find_rewrite.
        find_inversion.
        congruence.
    - right.
      unfold not.
      intros.
      unfold client_payload in *.
      match goal with
      | H : context[serialized_client_payload] |- _ => destruct H
      end.
      break_exists.
      break_and.
      congruence.
  Qed.

  Definition data := S.data.
  Definition timeout := S.timeout.
  Definition timeout_eq_dec := S.timeout_eq_dec.

  Definition label := S.label.
  Definition label_eq_dec := S.label_eq_dec.

  Definition serialize_dst_msg (a : addr * S.payload) :=
    match a with
    | (a, p) => (a, serialize_top (serialize p))
    end.

  Definition start_handler a l :=
    match S.start_handler a l with
    | (st, ms, ts) => (st, map serialize_dst_msg ms, ts)
    end.

  Definition res := (data * list (addr * payload) * list timeout * list timeout)%type.

  Definition serialize_res (r : S.res) : res := match r with
                                                | (st, msgs, ts1, ts2) =>
                                                  (st, map serialize_dst_msg msgs, ts1, ts2)
                                                end.

  Definition recv_handler (src : addr) (dst : addr) (st : data) (p : payload) : res :=
    serialize_res (S.recv_handler src dst st (revert_payload p)).

  Definition timeout_handler h st t :=
    serialize_res (S.timeout_handler h st t).

  Definition recv_handler_l src dst st p :=
    match S.recv_handler_l src dst st (revert_payload p) with
    | (r, l) => (serialize_res r, l)
    end.

  Definition timeout_handler_l h st t :=
    match S.timeout_handler_l h st t with
    | (r, l) => (serialize_res r, l)
    end.

  Definition label_input src dst p :=
    S.label_input src dst (revert_payload p).

  Definition label_output src dst p :=
    S.label_output src dst (revert_payload p).

  Lemma recv_handler_labeling : forall (src dst : addr) st p r,
      (recv_handler src dst st p = r ->
       exists l,
         recv_handler_l src dst st p = (r, l)) /\
      (forall l,
          recv_handler_l src dst st p = (r, l) ->
          recv_handler src dst st p = r).
  Proof.
    split; intros.
    - unfold recv_handler, serialize_res in *.
      repeat break_let.
      match goal with
      | H : S.recv_handler ?src ?dst ?st ?msg = _ |- _ =>
        apply (S.recv_handler_labeling src dst st msg) in H
      end.
      break_exists.
      unfold recv_handler_l.
      break_let.
      exists l2.
      unfold serialize_res.
      find_inversion.
      reflexivity.
    - unfold recv_handler_l in *.
      break_let.
      match goal with
      | H : context[S.recv_handler_l] |- _ => apply S.recv_handler_labeling in H
      end.
      unfold recv_handler.
      find_inversion.
      reflexivity.
  Qed.

  Lemma timeout_handler_labeling : forall h st t r,
      (timeout_handler h st t = r ->
       exists l,
         timeout_handler_l h st t = (r, l)) /\
      (forall l,
          timeout_handler_l h st t = (r, l) ->
          timeout_handler h st t = r).
    split; intros.
    - unfold timeout_handler, serialize_res in *.
      repeat break_let.
      match goal with
      | H : S.timeout_handler ?h ?st ?t = _ |- _ =>
        apply (S.timeout_handler_labeling h st t) in H
      end.
      break_exists.
      unfold timeout_handler_l.
      break_let.
      exists l2.
      unfold serialize_res.
      find_inversion.
      reflexivity.
    - unfold timeout_handler_l in *.
      break_let.
      match goal with
      | H : context[S.timeout_handler_l] |- _ => apply S.timeout_handler_labeling in H
      end.
      unfold timeout_handler.
      find_inversion.
      reflexivity.
  Qed.

  (* ConstrainedDynamicSystem fields *)
  Definition msg := (addr * (addr * payload))%type.

  Definition revert_msg (m : msg) :=
    match m with
    | (src, (dst, p)) => (src, (dst, (revert_payload p)))
    end.

  Inductive event : Type :=
  | e_send : msg -> event
  | e_recv : msg -> event
  | e_timeout : addr -> timeout -> event
  | e_fail : addr -> event.

  Definition revert_event e :=
    match e with
    | e_send m => S.e_send (revert_msg m)
    | e_recv m => S.e_recv (revert_msg m)
    | e_timeout h t => S.e_timeout h t
    | e_fail h => S.e_fail h
    end.

  Record global_state :=
    { nodes : list addr;
      failed_nodes : list addr;
      timeouts : addr -> list timeout;
      sigma : addr -> option data;
      msgs : list msg;
      trace : list event
    }.

  Definition revert_global_state (gst : global_state) : S.global_state :=
    {| S.nodes := nodes gst;
       S.failed_nodes := failed_nodes gst;
       S.timeouts := fun h =>  (timeouts gst h);
       S.sigma := sigma gst;
       S.msgs := map revert_msg (msgs gst);
       S.trace := map revert_event (trace gst) |}.

  (* are these too weak, since the revert functions "fail" silently with default values? *)
  Definition timeout_constraint gst h t :=
    S.timeout_constraint (revert_global_state gst) h t.

  Definition failure_constraint gst h gst' :=
    S.failure_constraint (revert_global_state gst) h (revert_global_state gst').

  Definition start_constraint gst h := S.start_constraint (revert_global_state gst) h.
End SerializedSystem.

(* serializers *)

(* pointer *)
Definition pointer_serialize (ptr : pointer) : IOStreamWriter.t :=
  serialize (ptrId ptr) +$+ serialize (ptrAddr ptr).

Definition pointer_deserialize : ByteListReader.t pointer :=
  id <- deserialize;;
     addr <- deserialize;;
     ByteListReader.ret (mkPointer id addr).

Lemma pointer_serialize_deserialize_id : serialize_deserialize_id_spec pointer_serialize
                                                                       pointer_deserialize.
Proof.
  intros.
  unfold pointer_serialize, pointer_deserialize.
  destruct a.
  cheerios_crush.
Qed.

Instance pointer_Serializer : Serializer pointer.
Proof.
  exact {| serialize := pointer_serialize;
             deserialize := pointer_deserialize;
             serialize_deserialize_id := pointer_serialize_deserialize_id |}.
Qed.

(* payload *)
Definition payload_serialize (pl : ChordSystem.payload) :=
  match pl with
  | Busy => serialize x00
  | GetBestPredecessor ptr => serialize x01 +$+ serialize ptr
  | GotBestPredecessor ptr => serialize x02 +$+ serialize ptr
  | GetSuccList => serialize x03
  | GotSuccList l => serialize x04 +$+ serialize l
  | GetPredAndSuccs => serialize x05
  | GotPredAndSuccs ptr l => serialize x06 +$+ serialize ptr +$+ serialize l
  | Notify => serialize x07
  | Ping => serialize x08
  | Pong => serialize x09
  end.

Definition payload_deserialize :=
  tag <- deserialize;;
      match tag with
      | x00 => ByteListReader.ret Busy
      | x01 => ptr <- deserialize;;
                   ByteListReader.ret (GetBestPredecessor ptr)
      | x02 => ptr <- deserialize;;
                   ByteListReader.ret (GotBestPredecessor ptr)
      | x03 => ByteListReader.ret GetSuccList
      | x04 => l <- deserialize;;
                 ByteListReader.ret (GotSuccList l)
      | x05 => ByteListReader.ret GetPredAndSuccs
      | x06 => ptr <- deserialize;;
                   l <- deserialize;;
                   ByteListReader.ret (GotPredAndSuccs ptr l)
      | x07 => ByteListReader.ret Notify
      | x08 => ByteListReader.ret Ping
      | x09 => ByteListReader.ret Pong
      | _ => ByteListReader.error
      end.

Lemma payload_serialize_deserialize_id : serialize_deserialize_id_spec payload_serialize
                                                                       payload_deserialize.
Proof.
  intros.
  unfold payload_serialize, payload_deserialize.
  destruct a;
    repeat (cheerios_crush; simpl).
Qed.

Instance payload_Serializer : Serializer payload.
Proof.
  exact {| serialize := payload_serialize;
             deserialize := payload_deserialize;
             serialize_deserialize_id := payload_serialize_deserialize_id |}.
Qed.

(* timeout *)
Definition timeout_serialize (t : timeout) :=
  match t with
  | Tick => serialize x00
  | RectifyTick => serialize x01
  | KeepaliveTick => serialize x02
  | Request a pl => serialize x03 +$+ serialize a +$+ serialize pl
  end.

Definition timeout_deserialize :=
  tag <- deserialize;;
      match tag with
      | x00 => ByteListReader.ret Tick
      | x01 => ByteListReader.ret RectifyTick
      | x02 => ByteListReader.ret KeepaliveTick
      | x03 => a <- deserialize;;
                 pl <- deserialize;;
                 ByteListReader.ret (Request a pl)
      | _ => ByteListReader.error
      end.

Lemma timeout_serialize_deserialize_id : serialize_deserialize_id_spec timeout_serialize
                                                                       timeout_deserialize.
Proof.
  intros.
  unfold timeout_serialize, timeout_deserialize.
  destruct a;
    repeat (cheerios_crush; simpl).
Qed.

Instance timeout_Serializer : Serializer timeout.
Proof.
  exact {| serialize := timeout_serialize;
             deserialize := timeout_deserialize;
             serialize_deserialize_id := timeout_serialize_deserialize_id |}.
Qed.

(* query *)
Definition query_serialize (q : query) :=
  match q with
  | Rectify ptr => serialize x00 +$+ serialize ptr
  | Stabilize => serialize x01
  | Stabilize2 ptr => serialize x02 +$+ serialize ptr
  | Join ptr => serialize x03 +$+ serialize ptr
  | Join2 ptr => serialize x04 +$+ serialize ptr
  end.

Definition query_deserialize :=
  tag <- deserialize;;
      match tag with
      | x00 => ptr <- deserialize;;
                   ByteListReader.ret (Rectify ptr)
      | x01 => ByteListReader.ret Stabilize
      | x02 => ptr <- deserialize;;
                   ByteListReader.ret (Stabilize2 ptr)
      | x03 => ptr <- deserialize;;
                   ByteListReader.ret (Join ptr)
      | x04 => ptr <- deserialize;;
                   ByteListReader.ret (Join2 ptr)
      | _ => ByteListReader.error
      end.

Lemma query_serialize_deserialize_id : serialize_deserialize_id_spec query_serialize
                                                                       query_deserialize.
Proof.
  intros.
  unfold query_serialize, query_deserialize.
  destruct a;
    repeat (cheerios_crush; simpl).
Qed.

Instance query_Serializer : Serializer query.
Proof.
  exact {| serialize := query_serialize;
             deserialize := query_deserialize;
             serialize_deserialize_id := query_serialize_deserialize_id |}.
Qed.

Module ChordSerializable <: SerializableSystem.
  Include ConstrainedChord.
  Definition payload_serializer := payload_Serializer.
  Definition default_payload := Busy.
End ChordSerializable.

Module ChordSerializedSystem <: DynamicSystem := SerializedSystem(ChordSerializable).
Export ChordSerializedSystem.

Module ChordSerializedSemantics := DynamicSemantics(ChordSerializedSystem).
Export ChordSerializedSemantics.