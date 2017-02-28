Require Import Chord.Chord.
Require Import Chord.ChordLocalProps.
Require Import Verdi.DynamicNet.
Require Import List.

Module ConstrainedChord <: ConstrainedDynamicSystem.
  Include Chord.

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

  Inductive _timeout_constraint : global_state -> addr -> timeout -> Prop :=
  | Tick_unconstrained : forall gst h,
      _timeout_constraint gst h Tick
  | KeepaliveTick_unconstrained : forall gst h,
      _timeout_constraint gst h KeepaliveTick
  | Request_needs_dst_dead_and_no_msgs : forall gst dst h p,
      In dst (failed_nodes gst) ->
      (forall m, request_response_pair p m -> ~ In (dst, (h, m)) (msgs gst)) ->
      _timeout_constraint gst h (Request dst p).
  Definition timeout_constraint := _timeout_constraint.

  Definition timeouts_detect_failure (gst : global_state) : Prop :=
    forall xs t ys h dead req,
      (trace gst) = xs ++ t :: ys ->
      (* if a request timeout occurs at some point in the trace... *)
      t = (e_timeout h (Request dead req)) ->
      (* then it corresponds to an earlier node failure. *)
      In (e_fail dead) xs.

  (* tip: treat this as opaque and use lemmas: it never gets stopped except by failure *)
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

  Definition joining_node (gst : global_state) (h : addr) : Prop :=
    exists st,
      sigma gst h = Some st /\
      joined st = false /\
      In h (nodes gst) /\
      ~ In h (failed_nodes gst).

  Definition best_succ (gst : global_state) (h s : addr) : Prop :=
    exists st xs ys,
      live_node gst h /\
      sigma gst h = Some st /\
      map ChordIDSpace.addr_of (succ_list st) = xs ++ s :: ys /\
      (forall o, In o xs -> dead_node gst o) /\
      live_node gst s.

  Definition live_node_in_succ_lists (gst : global_state) : Prop :=
    forall h st,
      sigma gst h = Some st ->
      live_node gst h ->
      exists s,
        best_succ gst h s.

  (* This is a way of dealing with succ lists missing entries
     mid-stabilization that doesn't involve putting artificial entries
     into the actual successor list. *)
  Definition ext_succ_list_span_includes (h : id) (succs : list id) (n : id) : Prop.
  Admitted.
  (* fix this definition to work with bitvectors.
    forall n l e,
      length (h :: succs) = n ->
      l = last succs h ->
      e = l + (Chord.SUCC_LIST_LEN - n) ->
      ChordIDSpace.between h n e.
   *)

  (* "A principal node is a member that is not skipped by any member's
     extended successor list" *)
  Definition principal (gst : global_state) (p : addr) : Prop :=
    forall h st succs pid,
      live_node gst h ->
      sigma gst h = Some st ->
      succs = map ChordIDSpace.id_of (succ_list st) ->
      pid = hash p ->
      ext_succ_list_span_includes (hash h) succs pid ->
      In pid succs.

  Definition principals (gst : global_state) (ps : list addr) : Prop :=
    NoDup ps /\
    Forall (principal gst) ps /\
    forall p, principal gst p -> In p ps.

  Definition sufficient_principals (gst : global_state) : Prop :=
    exists ps,
      principals gst ps /\
      length ps > Chord.SUCC_LIST_LEN.

  Definition principal_failure_constraint (gst : global_state) (f : addr) : Prop :=
    principal gst f ->
    forall ps,
      principals gst ps ->
      length ps > (Chord.SUCC_LIST_LEN + 1).

  Definition failure_constraint (gst : global_state) (f : addr) (gst' : global_state) : Prop :=
    live_node_in_succ_lists gst' /\
    principal_failure_constraint gst f.

End ConstrainedChord.

Module ChordSemantics := DynamicSemantics(ConstrainedChord).
