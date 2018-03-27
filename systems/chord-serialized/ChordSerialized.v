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

(* types *)
Module Type SerializableSystem.
  Include ConstrainedDynamicSystem.
  Parameter payload_serializer : Serializer payload.
  Parameter default_payload : payload. (* in case deserialization fails but value needed (avoid) *)

  Parameter timeout' : Type.
  Parameter timeout'_eq_dec : forall a b : timeout', {a = b} + {~ a = b}.
  Parameter f : timeout -> timeout'.
  Parameter g : timeout' -> option timeout.
  Parameter timeout_spec : forall t, g (f t) = Some t.
  Parameter default_timeout : timeout.
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
    exists p', deserialize_top deserialize p = Some p' /\ S.client_payload p'.

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
  Definition timeout := S.timeout'.

  Definition revert_timeout (t' : S.timeout') :=
    match S.g t' with
    | Some t => t
    | None => S.default_timeout
    end.

  Definition timeout_eq_dec := S.timeout'_eq_dec.

  Definition label := S.label.
  Definition label_eq_dec := S.label_eq_dec.

  Definition serialize_msg (a : addr * S.payload) :=
    match a with
    | (a, p) => (a, serialize_top (serialize p))
    end.

  Definition start_handler a l :=
    match S.start_handler a l with
    | (st, ms, ts) => (st, map serialize_msg ms, map S.f ts)
    end.

  Definition res := (data * list (addr * payload) * list timeout * list timeout)%type.

  Definition serialize_res (r : S.res) : res := match r with
                                                | (st, msgs, ts1, ts2) =>
                                                  (st, map serialize_msg msgs, map S.f ts1, map S.f ts2)
                                                end.

  Definition recv_handler (src : addr) (dst : addr) (st : data) (p : payload) : res :=
    serialize_res (S.recv_handler src dst st (revert_payload p)).

  Definition timeout_handler h st t :=
    serialize_res (S.timeout_handler h st (revert_timeout t)).

  Definition recv_handler_l src dst st p :=
    match S.recv_handler_l src dst st (revert_payload p) with
    | (r, l) => (serialize_res r, l)
    end.

  Definition timeout_handler_l h st t :=
    match S.timeout_handler_l h st (revert_timeout t) with
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

  Definition revert_event (e : event) : S.event :=
    match e with
    | e_send m => S.e_send (revert_msg m)
    | e_recv m => S.e_recv (revert_msg m)
    | e_timeout h t => S.e_timeout h (revert_timeout t)
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
       S.timeouts := fun h =>  map revert_timeout (timeouts gst h);
       S.sigma := sigma gst;
       S.msgs := map revert_msg (msgs gst);
       S.trace := map revert_event (trace gst) |}.


  (* are these too weak, since the revert functions "fail" silently with default values? *)
  Definition timeout'_constraint (gst : global_state) (h : addr) (t' : S.timeout') :=
    exists t, S.g t' = t /\
              S.timeout_constraint (revert_global_state gst) h (revert_timeout t').

  Definition timeout_constraint := timeout'_constraint.

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

  (* ideally timeout would just take payload type as a parameter *)
  (* or, does this even need to have the serialized payload? *)
  Inductive _timeout' :=
  | Tick' : _timeout'
  | RectifyTick' : _timeout'
  | KeepaliveTick' : _timeout'
  | Request' : addr -> IOStreamWriter.wire -> _timeout'.
  Definition timeout' := _timeout'.

  Lemma timeout'_eq_dec : forall x y : timeout', {x = y} + {~ x = y}.
    decide equality.
    - apply IOStreamWriter.wire_eq_dec.
    - apply addr_eq_dec.
  Qed.

  Definition f t :=
    match t with
    | Tick => Tick'
    | RectifyTick => RectifyTick'
    | KeepaliveTick => KeepaliveTick'
    | Request h p => Request' h (serialize_top (serialize p))
    end.

  Definition g t' :=
    match t' with
    | Tick' => Some Tick
    | RectifyTick' => Some RectifyTick
    | KeepaliveTick' => Some KeepaliveTick
    | Request' h p => (match deserialize_top deserialize p with
                                 | Some p => Some (Request h p)
                                 | None => None
                                 end)
    end.
End ChordSerializable.

Module ChordSerializedSystem <: DynamicSystem := SerializedSystem(ChordSerializable).
Export ChordSerializedSystem.

Module ConstrainedChordSerialized <: ConstrainedDynamicSystem.
  Include ChordSerializedSystem.
  Definition msg : Type := (addr * (addr * payload))%type.

  Inductive event : Type :=
  | e_send : msg -> event
  | e_recv : msg -> event
  | e_timeout : addr -> timeout -> event
  | e_fail : addr -> event.

  Record global_state :=
    { nodes : list addr;
      failed_nodes : list addr;
      timeouts : addr -> list timeout;
      sigma : addr -> option data;
      msgs : list msg;
      trace : list event
    }.


  Inductive request_response_pair : payload -> payload -> Prop :=
  | pair_GetBestPredecessor : forall n p,
      request_response_pair (serialize_top (serialize (GetBestPredecessor n)))
                            (serialize_top (serialize (GotBestPredecessor p)))
  | pair_GetSuccList : forall l,
      request_response_pair (serialize_top (serialize GetSuccList))
                            (serialize_top (serialize (GotSuccList l)))
  | pair_GetPredAndSuccs : forall p l,
      request_response_pair (serialize_top (serialize GetPredAndSuccs))
                            (serialize_top (serialize (GotPredAndSuccs p l)))
  | pair_Ping : request_response_pair (serialize_top (serialize Ping))
                                      (serialize_top (serialize Pong)).

  Definition _timeout_constraint : global_state -> addr -> timeout -> Prop.
  Admitted.
(*
  | Tick_unconstrained : forall gst h,
      _timeout_constraint gst h Tick
  | KeepaliveTick_unconstrained : forall gst h,
      _timeout_constraint gst h KeepaliveTick
  | RectifyTick_unconstrained : forall gst h,
      _timeout_constraint gst h RectifyTick
  | Request_needs_dst_dead_and_no_msgs : forall gst dst h p,
      In dst (failed_nodes gst) ->
      (forall m, request_response_pair p m -> ~ In (dst, (h, m)) (msgs gst)) ->
      _timeout_constraint gst h (Request dst p).
*)
  Definition timeout_constraint := _timeout_constraint.

  Definition start_constraint (gst : global_state) (h : addr) : Prop :=
    ~ In (hash h) (map hash (nodes gst)).

  Definition live_node (gst : global_state) (h : addr) : Prop :=
    In h (nodes gst) /\
    ~ In h (failed_nodes gst) /\
    exists st,
      sigma gst h = Some st /\
      joined st = true.

  Definition dead_node (gst : global_state) (h : addr) : Prop :=
    In h (nodes gst) /\
    In h (failed_nodes gst) /\
    exists st,
      sigma gst h = Some st.

  Definition best_succ (gst : global_state) (h s : addr) : Prop :=
    exists st xs ys,
      live_node gst h /\
      sigma gst h = Some st /\
      map ChordIDSpace.addr_of (succ_list st) = xs ++ s :: ys /\
      (forall o, In o xs -> dead_node gst o) /\
      live_node gst s.

  Definition live_node_in_msg_succ_lists' (gst : global_state) (ms : list msg) : Prop :=
    forall src dst succs p,
      In (src, (dst, serialize_top (serialize (GotPredAndSuccs p succs)))) ms \/
      In (src, (dst, serialize_top (serialize (GotSuccList succs)))) ms ->
      length succs > 0 \/ (exists st, sigma gst src = Some st /\ joined st = true) ->
      Exists (live_node gst) (map addr_of (chop_succs (make_pointer src :: succs))).
  Hint Unfold live_node_in_msg_succ_lists'.

  Definition live_node_in_msg_succ_lists (gst : global_state) : Prop :=
    live_node_in_msg_succ_lists' gst (msgs gst).
  Hint Unfold live_node_in_msg_succ_lists.

  Definition live_node_in_succ_lists (gst : global_state) : Prop :=
    forall h st,
      sigma gst h = Some st ->
      live_node gst h ->
      exists s,
        best_succ gst h s.

  Definition not_skipped (h : id) (succs : list id) (n : id) : Prop :=
    forall a b xs ys,
      h :: succs = xs ++ [a; b] ++ ys ->
      ~ between a n b.

  (* "A principal node is a member that is not skipped by any member's
     extended successor list" *)
  Definition principal (gst : global_state) (p : addr) : Prop :=
    live_node gst p /\
    forall h st succs,
      live_node gst h ->
      sigma gst h = Some st ->
      succs = map ChordIDSpace.id_of (succ_list st) ->
      not_skipped (hash h) succs (hash p).

  Definition principals (gst : global_state) (ps : list addr) : Prop :=
    NoDup ps /\
    Forall (principal gst) ps /\
    forall p,
      principal gst p ->
      In p ps.

  (* f can fail unless it's the (SUCC_LIST_LEN+1)th principal. *)
  Definition principal_failure_constraint (gst : global_state) (f : addr) : Prop :=
    principal gst f ->
    forall ps,
      principals gst ps ->
      length ps = SUCC_LIST_LEN + 1 ->
      False.

  Definition failure_constraint (gst : global_state) (f : addr) (gst' : global_state) : Prop :=
    live_node_in_msg_succ_lists gst' /\
    live_node_in_succ_lists gst' /\
    principal_failure_constraint gst f.
End ConstrainedChordSerialized.

Module ChordSemantics := DynamicSemantics(ConstrainedChord).

Export ChordSemantics.
Export ConstrainedChordSerialized.
