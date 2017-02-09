Require Import Arith.
Require Import Omega.
Require Vectors.VectorEq.
Require Bool.Bvector.
Require Import List.
Import List.ListNotations.
Require Import String.
Require ZArith.Zdigits.

Require Import StructTact.Dedup.
Require Import StructTact.RemoveAll.
Require Import StructTact.StructTactics.
Require Import Verdi.DynamicNet.

Require Import Chord.Sorting.

(* number of successors each node has to track *)
Variable SUCC_LIST_LEN : nat.
(* bit-width of node identifiers *)
Variable N : nat.
(* hash function from names to identifiers *)
Variable hash : string -> Bvector.Bvector N.
Variable hash_inj :
  forall a b,
    hash a = hash b ->
    a = b.
Variable client_addr : string -> Prop.
Variable client_addr_dec :
  forall a,
    {client_addr a} + {~ client_addr a}.

Module Chord <: DynamicSystem.
  Definition addr := string.
  Definition addr_eq_dec :
    forall a b : addr, {a = b} + {a <> b}
    := string_dec.
  Definition id := Bvector.Bvector N.
  Definition id_eq_dec :
    forall a b : id, {a = b} + {a <> b}
    := (VectorEq.eq_dec _ Bool.eqb Bool.eqb_true_iff _).

  Definition pointer := (id * addr)%type.
  Definition id_of (p : pointer) : id := fst p.
  Definition addr_of (p : pointer) : addr := snd p.

  Definition client_addr := client_addr.
  Definition client_addr_dec := client_addr_dec.

  Definition pointer_eq_dec : forall x y : pointer,
      {x = y} + {x <> y}.
  Proof using.
    decide equality;
      auto using id_eq_dec, addr_eq_dec.
  Defined.

  Definition make_pointer (a : addr) : pointer :=
    (hash a, a).

  Inductive _payload :=
  | Busy : _payload
  | GetBestPredecessor : pointer -> _payload
  | GotBestPredecessor : pointer -> _payload
  | GetSuccList : _payload
  | GotSuccList : list pointer -> _payload
  | GetPredAndSuccs : _payload
  | GotPredAndSuccs : option pointer -> list pointer -> _payload
  | Notify : _payload
  | Ping : _payload
  | Pong : _payload.
  Definition payload := _payload.

  Inductive _client_payload : payload -> Prop :=
  | CPGetBestPredecessor : forall p, _client_payload (GetBestPredecessor p)
  | CPGetSuccList : _client_payload GetSuccList.
  Definition client_payload := _client_payload.
  Definition client_payload_dec :
    forall p,
      {client_payload p} + {~client_payload p}.
  Proof.
    destruct p; (left; constructor) || right; intro H; inversion H.
  Defined.

  Lemma option_eq_dec : forall A : Type,
    (forall x y : A, {x = y} + {x <> y}) ->
    forall a b : option A, {a = b} + {a <> b}.
  Proof using.
    decide equality.
  Defined.

  Definition payload_eq_dec : forall x y : payload,
      {x = y} + {x <> y}.
  Proof using.
    repeat decide equality;
      auto using id_eq_dec, addr_eq_dec.
  Defined.

  Inductive _timeout :=
  | Tick : _timeout
  | KeepaliveTick : _timeout
  | Request : addr -> payload -> _timeout.
  Definition timeout := _timeout.

  Definition timeout_eq_dec : forall x y : timeout,
      {x = y} + {x <> y}.
  Proof using.
    repeat decide equality;
      auto using id_eq_dec, addr_eq_dec.
  Defined.

  Inductive _query :=
  (* needs a pointer to the notifier *)
  | Rectify : pointer -> _query
  | Stabilize : _query
  (* needs a new successor *)
  | Stabilize2 : pointer -> _query
  (* needs a known node *)
  | Join : pointer -> _query
  (* needs to know new successor *)
  | Join2 : pointer -> _query.
  Definition query := _query.

  Record _data := mkData { ptr : pointer;
                          pred : option pointer;
                          succ_list : list pointer;
                          known : pointer;
                          joined : bool;
                          rectify_with : option pointer;
                          cur_request : option (pointer * query * payload);
                          delayed_queries : list (addr * payload) }.
  Definition data := _data.

  Definition res := (data * list (addr * payload) * list timeout * list timeout)%type.

  Definition is_request (p : payload) : bool :=
    match p with
    | GetBestPredecessor _ => true
    | GetSuccList => true
    | GetPredAndSuccs => true
    | Ping => true
    | _ => false
    end.

  Definition closes_request (req res : payload) : bool :=
    match req, res with
    | GetBestPredecessor _, GotBestPredecessor _ => true
    | GetSuccList, GotSuccList _ => true
    | GetPredAndSuccs, GotPredAndSuccs _ _ => true
    | Ping, Pong => true
    | _, _ => false
    end.
  Definition t : timeout := Tick.
  Definition tts (l : list timeout) := Tick :: l.

  Definition add_tick (r : res) : res :=
    let '(st, sends, newts, cts) := r in
    (st, sends, Tick :: newts, cts).

  Definition chop_succs (succs : list pointer) : list pointer :=
    firstn SUCC_LIST_LEN succs.

  Definition make_succs (head : pointer) (rest : list pointer) : list pointer :=
    chop_succs (head :: rest).

  Definition update_pred (st : data) (p : pointer) : data :=
    {| ptr := ptr st;
       pred := Some p;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := cur_request st;
       delayed_queries := delayed_queries st |}.

  Definition update_succ_list (st : data) (succs : list pointer) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succs;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := cur_request st;
       delayed_queries := delayed_queries st |}.

  Definition update_query (st : data) (dst : pointer) (q : query) (m : payload) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := Some (dst, q, m);
       delayed_queries := delayed_queries st |}.

  Definition update_for_join (st : data) (succs : list pointer) : data :=
    {| ptr := ptr st;
       pred := None;
       succ_list := succs;
       known := known st;
       joined := true;
       rectify_with := rectify_with st;
       cur_request := cur_request st;
       delayed_queries := delayed_queries st |}.

  Definition clear_rectify_with (st : data) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := None;
       cur_request := cur_request st;
       delayed_queries := delayed_queries st |}.

  Definition clear_query (st : data) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := None;
       delayed_queries := delayed_queries st |}.

  Definition clear_delayed_queries (st : data) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := cur_request st;
       delayed_queries := [] |}.

  Definition init_state_preset (h : addr) (pred : option pointer) (succs : list pointer) : data :=
    {| ptr := make_pointer h;
       pred := pred;
       succ_list := succs;
       known := (make_pointer h);
       joined := true;
       rectify_with := None;
       cur_request := None;
       delayed_queries := [] |}.

  Definition init_state_join (h k : addr) : data :=
    {| ptr := make_pointer h;
       pred := None;
       succ_list := [];
       known := make_pointer k;
       joined := false;
       rectify_with := None;
       cur_request := None;
       delayed_queries := [] |}.

  Definition empty_start_res (h : addr) : data * list (addr * payload) * list timeout :=
    ({| ptr := make_pointer h;
        pred := None;
        succ_list := [];
        known := make_pointer h;
        joined := false;
        rectify_with := None;
        cur_request := None;
        delayed_queries := [] |},
     [],
     []).

  Definition z_of_id : id -> Z :=
    Zdigits.binary_value _.

  Definition id_of_z : Z -> id :=
    Zdigits.Z_to_binary _.

  Lemma z_of_id_inv :
    forall x,
      id_of_z (z_of_id x) = x.
  Proof.
    unfold id_of_z, z_of_id.
    intros.
    apply Zdigits.binary_to_Z_to_binary.
  Qed.

  Definition bv_lt (x y : id) : bool :=
    Z.ltb (z_of_id x) (z_of_id y).

  (* true iff x in (a, b) on some sufficiently large "circle" *)
  Definition between_bool (a x b : id) : bool :=
    match bv_lt a b, bv_lt a x, bv_lt x b with
    | true, true, true => true
    | false, true, _ => true
    | false, _, true => true
    | _, _, _ => false
    end.

  Definition ptr_between_bool (a x b : pointer) : bool :=
    between_bool (id_of a) (id_of x) (id_of b).

  Definition set_rectify_with (st : data) (rw : pointer) : data :=
    match rectify_with st with
    | Some rw0 =>
      if ptr_between_bool rw0 rw (ptr st)
      then {| ptr := ptr st;
              pred := pred st;
              succ_list := succ_list st;
              known := known st;
              joined := joined st;
              rectify_with := Some rw;
              cur_request := cur_request st;
              delayed_queries := delayed_queries st |}
      else st
    | None => st
    end.

  Definition send_eq_dec :
    forall x y : addr * payload,
      {x = y} + {x <> y}.
  Proof using.
    repeat decide equality;
      auto using id_eq_dec, payload_eq_dec.
  Defined.

  Definition delay_query (st : data) (src : addr) (msg : payload) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := rectify_with st;
       cur_request := cur_request st;
       delayed_queries := dedup send_eq_dec ((src, msg) :: delayed_queries st) |}.

  Definition make_request (h : addr) (st : data) (k : query) : option (pointer * payload) :=
    match k with
    | Rectify notifier =>
      option_map (fun p => (p, Ping)) (pred st)
    | Stabilize =>
      option_map (fun succ => (succ, GetPredAndSuccs)) (hd_error (succ_list st))
    | Stabilize2 new_succ =>
      Some (new_succ, GetSuccList)
    | Join known =>
      Some (known, GetBestPredecessor (make_pointer h))
    | Join2 new_succ =>
      Some (new_succ, GetSuccList)
    end.

  Definition timeouts_in (st : data) : list timeout :=
    match cur_request st with
    | Some (dst, _, m) => [Request (addr_of dst) m]
    | None => []
    end.

  Definition start_query (h : addr) (st : data) (k : query) : res :=
    let cst := timeouts_in st in
    match make_request h st k with
    | Some (dst, msg) =>
      (update_query st dst k msg,
       [(addr_of dst, msg)],
       [Request (addr_of dst) msg],
       cst)
    | None =>
      (* only happens if succ_list = [], which is contra protocol assumptions *)
      (st, [], [], [])
    end.

  Definition do_rectify (h : addr) (st : data) : res :=
    match joined st, cur_request st, rectify_with st with
    | true, None, Some new =>
      let st := clear_rectify_with st in
      match pred st with
      | Some _ => start_query h st (Rectify new)
      | None => (update_pred st new, [], [], [])
      end
    | _, _, _ => (st, [], [], [])
    end.

  Definition best_predecessor (h : pointer) (succs : list pointer) (them : pointer) : pointer :=
    hd h (filter (fun s => ptr_between_bool h s them)
                 (rev succs)).

  Definition handle_query_req (st : data) (src : addr) (msg : payload) : list (addr * payload) :=
    match msg with
    | GetSuccList =>
      [(src, GotSuccList (succ_list st))]
    | GetPredAndSuccs =>
      [(src, GotPredAndSuccs (pred st) (succ_list st))]
    | GetBestPredecessor p =>
      [(src, GotBestPredecessor (best_predecessor (ptr st) (succ_list st) p))]
    | _ => []
    end.

  Definition handle_delayed_query (h : addr) (st : data) (q : addr * payload) : list (addr * payload) :=
    let (src, msg) := q in
    handle_query_req st src msg.

  Definition do_delayed_queries (h : addr) (st : data) : res :=
    match cur_request st with
    | Some _ => (st, [], [], [])
    | None =>
      let sends := concat (map (handle_delayed_query h st) (delayed_queries st)) in
      (clear_delayed_queries st, sends, [], [KeepaliveTick])
    end.

  (* need to prove that this never gets called with requests in the sends of r *)
  Definition end_query (r : res) : res :=
    let '(st, outs, nts, cts) := r in
    let clearreq := timeouts_in st in
    let st' := clear_query st in
    (st', outs, nts, clearreq ++ cts).

  Definition ptrs_to_addrs : list (pointer * payload) -> list (addr * payload) :=
    map (fun p => (addr_of (fst p), (snd p))).

  Definition handle_rectify (st : data) (my_pred : pointer) (notifier : pointer) : res :=
    if ptr_between_bool my_pred notifier (ptr st)
    then (update_pred st notifier, [], [], [])
    else (st, [], [], []).

  Definition handle_stabilize (h : addr) (src : pointer) (st : data) (q : query) (new_succ : pointer) (succs : list pointer) : res :=
    let new_st := update_succ_list st (make_succs src succs) in
    if ptr_between_bool (ptr st) new_succ src
    then start_query h new_st (Stabilize2 new_succ)
    else end_query (new_st, [(addr_of src, Notify)], [], []).

  Definition next_msg_for_join (self : pointer) (src best_pred : addr) : payload :=
    if addr_eq_dec best_pred src
    then GetSuccList
    else GetBestPredecessor self.

  Definition handle_query_res (src h : addr) (st : data) (q : query) (p : payload) : res :=
    match q, p with
    | Rectify notifier, Pong =>
      match pred st with
      | Some p => end_query (handle_rectify st p notifier)
      | None => end_query (update_pred st notifier, [], [], [])
      end
    | Stabilize, GotPredAndSuccs new_succ succs =>
      match new_succ with
      | Some ns => (handle_stabilize h (make_pointer src) st q ns succs)
      | None => end_query (st, [], [], [])
      end
    | Stabilize2 new_succ, GotSuccList succs =>
      end_query (update_succ_list st (make_succs new_succ succs),
                 [(addr_of new_succ, Notify)],
                 [],
                 [])
    | Join known, GotBestPredecessor best_pred =>
      let a := addr_of best_pred in
      let req := next_msg_for_join (ptr st) src a in
      (st,
       [(a, req)],
       [Request a req],
       [Request src (GetBestPredecessor (ptr st))])
    | Join known, GotSuccList l =>
      match l with
      | (new_succ :: _) => start_query (addr_of new_succ) st (Join2 new_succ)
      | [] => end_query (st, [], [], []) (* this is bad *)
      end
    | Join2 new_succ, GotSuccList l =>
      let succs := make_succs new_succ l in
      add_tick (end_query (update_for_join st succs, [], [], []))
    | _, Busy => (st, [], timeouts_in st, timeouts_in st)
    | _, _ => (st, [], [], [])
    end.

  Definition handle_query_req_busy (src : addr) (st : data) (msg : payload) : res :=
    if list_eq_dec send_eq_dec (delayed_queries st) nil
    then (delay_query st src msg, [(src, Busy)], [KeepaliveTick], [])
    else (delay_query st src msg, [(src, Busy)], [], []).

  Definition is_safe (msg : payload) :=
    match msg with
    | Notify => true
    | Ping => true
    | _ => false
    end.

  Definition handle_msg (src : addr) (dst : addr) (st : data) (msg : payload) : res :=
    match msg, cur_request st, is_request msg with
    | Notify, _, _ => (set_rectify_with st (make_pointer src), [], [], [])
    | Ping, _, _ => (st, [(src, Pong)], [], [])
    | _, Some (query_dst, q, _), true => handle_query_req_busy src st msg
    | _, Some (query_dst, q, _), false => handle_query_res src dst st q msg
    | _, None, _ => (st, handle_query_req st src msg, [], [])
    end.

  Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) : res :=
    let '(st, ms1, nts1, cts1) := handle_msg src dst st msg in
    let '(st, ms2, nts2, cts2) := do_delayed_queries dst st in
    let '(st, ms3, nts3, cts3) := do_rectify dst st in
    let nts := nts3 ++ remove_all timeout_eq_dec cts3
                    (nts2 ++ remove_all timeout_eq_dec cts2 nts1) in
    (st, ms3 ++ ms2 ++ ms1, nts, cts1 ++ cts2 ++ cts3).

  Definition pi {A B C D : Type} (t : A * B * C * D) : A * B * C :=
    let '(a, b, c, d) := t in (a, b, c).

  (* this is a total linear less-than-or-equal relation, see proofs below *)
  Definition unroll_between (h : id) (x y : id) : bool :=
    if id_eq_dec h x
    then true
    else if id_eq_dec h y
         then false
         else if id_eq_dec x y
              then true
              else between_bool h x y.

  Lemma unrolling_makes_h_least :
    forall h x,
      unroll_between h h x = true.
  Proof.
    unfold unroll_between.
    intros.
    break_if; auto.
  Qed.

  Require Import Lia.
  Lemma unrolling_antisymmetric :
    forall h x y,
      unroll_between h x y = true ->
      unroll_between h y x = true ->
      x = y.
  Proof.
    unfold unroll_between, between_bool.
    intros.
    repeat break_if; try subst; try congruence;
    unfold bv_lt in *;
    rewrite Z.ltb_lt in *;
    omega.
  Qed.

  Lemma unrolling_transitive :
    forall h x y z,
      unroll_between h x y = true ->
      unroll_between h y z = true ->
      unroll_between h x z = true.
  Proof.
    unfold unroll_between, between_bool.
    intros.
    repeat break_if; try subst; try congruence;
    unfold bv_lt in *;
    rewrite Z.ltb_lt, Z.ltb_nlt in *;
    omega.
  Qed.
  Lemma neq_in_id_implies_neq_in_z :
    forall x y : id,
      x <> y ->
      z_of_id x <> z_of_id y.
  Proof.
    intros.
    intro.
    find_apply_lem_hyp (f_equal id_of_z).
    repeat rewrite z_of_id_inv in *.
    congruence.
  Qed.

  Lemma unrolling_total :
    forall h x y,
      unroll_between h x y = true \/
      unroll_between h y x = true.
  Proof.
    unfold unroll_between, between_bool.
    intros.
    repeat break_if; try subst; try congruence; auto;
      unfold bv_lt in *;
      try rewrite Z.ltb_lt, Z.ltb_nlt in *;
      find_apply_lem_hyp neq_in_id_implies_neq_in_z;
      try lia.
      rewrite Z.ltb_nlt in *.
      find_apply_lem_hyp neq_in_id_implies_neq_in_z;
      try lia.
  Qed.

  Lemma unrolling_reflexive :
    forall h x,
      unroll_between h x x = true.
  Proof.
    unfold unroll_between, between_bool.
    intros.
    repeat break_if; try omega || subst; auto; try congruence.
  Qed.

  Definition unroll_between_ptr (h : addr) (a b : pointer) :=
    unroll_between (hash h) (id_of a) (id_of b).

  Definition sort_by_between (h : addr) : list pointer -> list pointer :=
    sort pointer (unroll_between_ptr h).

  Fixpoint find_succs (h : addr) (sorted_ring : list pointer) : list pointer :=
    match sorted_ring with
    | [] => []
    | s :: rest =>
      if pointer_eq_dec s (make_pointer h)
      then find_succs h rest
      else chop_succs (s :: rest)
    end.

  Fixpoint find_pred (h : addr) (sorted_ring : list pointer) : option pointer :=
    hd_error (rev sorted_ring).

  Definition start_handler (h : addr) (knowns : list addr) : data * list (addr * payload) * list timeout :=
    match sort_by_between h (map make_pointer knowns) with
    (* prohibited by semantics *)
    | [] =>
      empty_start_res h
    | [k] =>
      pi (start_query h (init_state_join h (addr_of k)) (Join k))
    | sorted_ring =>
      let succs := find_succs h sorted_ring in
      let pred := find_pred h sorted_ring in
      (init_state_preset h pred succs, [], [Tick])
    end.

  Definition tick_handler (h : addr) (st : data) : res :=
    match cur_request st, joined st with
    | None, true => add_tick (start_query h st Stabilize)
    | _, _ => (st, [], [Tick], [])
    end.

  Definition handle_query_timeout (h : addr) (st : data) (dead : pointer) (q : query) : res :=
    match q with
    | Rectify notifier =>
      end_query (update_pred st notifier, [], [], [])
    | Stabilize =>
      match succ_list st with
      | _ :: rest =>
        start_query h (update_succ_list st rest) Stabilize
      (* will not happen in a good network *)
      | [] =>
        end_query (st, [], [], [])
      end
    | Stabilize2 new_succ =>
      match succ_list st with
      | next :: _ =>
        end_query (st, [(addr_of next, Notify)], [], [])
      (* again, won't happen in a good network *)
      | [] =>
        end_query (st, [], [], [])
      end
    (* Join, Join2 *)
    | _ => end_query (st, [], [], [])
    end.

  Definition send_keepalives (st : data) : list (addr * payload) :=
    map (fun q => (fst q, Busy)) (delayed_queries st).

  Definition keepalive_handler (st : data) : res :=
    (st, send_keepalives st, [KeepaliveTick], []).

  Definition request_timeout_handler (h : addr) (st : data) (dst : addr) (msg : payload) : res :=
    match cur_request st with
    | Some (ptr, q, _) =>
      if addr_eq_dec (addr_of ptr) dst
      then handle_query_timeout h st ptr q
      else (st, [], [], []) (* shouldn't happen *)
    | None => (st, [], [], []) (* shouldn't happen *)
    end.

  Definition timeout_handler (h : addr) (st : data) (t : timeout) : res :=
    match t with
    | Request dst msg => request_timeout_handler h st dst msg
    | Tick => tick_handler h st
    | KeepaliveTick => keepalive_handler st
    end.

  Inductive _label : Set :=
  | RecvMsg : addr -> addr -> payload -> _label
  | Timeout : addr -> timeout -> _label.
  Definition label := _label.

  Definition label_eq_dec :
    forall x y : label,
      {x = y} + {x <> y}.
  Proof using.
    decide equality;
      auto using addr_eq_dec, payload_eq_dec, timeout_eq_dec.
  Defined.

  Definition timeout_handler_l (h : addr) (st : data) (t : timeout) :=
    (timeout_handler h st t, Timeout h t).

  Definition recv_handler_l (src : addr) (dst : addr) (st : data) (msg : payload) :=
    (recv_handler src dst st msg, RecvMsg src dst msg).

  Lemma recv_handler_labeling :
    forall src dst st p r,
      (recv_handler src dst st p = r ->
       exists l,
         recv_handler_l src dst st p = (r, l)) /\
      (forall l,
          recv_handler_l src dst st p = (r, l) ->
          recv_handler src dst st p = r).
  Proof using.
    unfold recv_handler_l.
    intuition.
    - find_rewrite.
      now eexists.
    - now tuple_inversion.
  Qed.

  Definition label_input : addr -> addr -> payload -> label := RecvMsg.
  Definition label_output : addr -> addr -> payload -> label := RecvMsg.

  Lemma timeout_handler_labeling :
    forall h st t r,
      (timeout_handler h st t = r ->
      exists l,
        timeout_handler_l h st t = (r, l)) /\
      (forall l,
          timeout_handler_l h st t = (r, l) ->
          timeout_handler h st t = r).
  Proof.
    unfold timeout_handler_l.
  Admitted.

End Chord.
