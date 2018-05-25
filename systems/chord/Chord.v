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

Require Import Chord.Sorting.
Require Import Chord.IDSpace.
Require Import Chord.Bitvectors.

(* Axioms and top-level parameters *)

(* number of successors each node has to track *)
Parameter SUCC_LIST_LEN : nat.
Parameter succ_list_len_lower_bound :
  SUCC_LIST_LEN >= 2.
(* byte-width of node identifiers *)
Parameter N : nat.
(* bit-width of node identifiers *)
Definition bit_len := 8 * N.
Definition id := Bvector.Bvector bit_len.
Definition addr := String.string.

(* ID type is finite so it has decidable equality *)
Definition id_eq_dec :
  forall a b : id, {a = b} + {a <> b}
  := (VectorEq.eq_dec _ Bool.eqb Bool.eqb_true_iff _).

(* hash function from names to our mystery type (it's probably a 16-byte string...) *)
Parameter ocaml_hash : addr -> { s : string | String.length s = N }.

(* conversions between strings and ids *)
Definition ascii_to_id (asc : { s : string | String.length s = N }) : id :=
  Bitvectors.fixed_length_string_to_vec asc.

(* n.b. only used in extracted code *)
Definition id_to_ascii : id -> string :=
  Bitvectors.vec_to_string.

Definition hash (a : addr) : id :=
  ascii_to_id (ocaml_hash a).

Parameter client_addr : string -> Prop.
Parameter client_addr_dec :
  forall a,
    {client_addr a} + {~ client_addr a}.

Definition z_of_id : id -> BinNums.Z :=
  Zdigits.binary_value _.

Definition id_of_z : BinNums.Z -> id :=
  Zdigits.Z_to_binary _.

Lemma z_of_id_inv :
  forall x,
    id_of_z (z_of_id x) = x.
Proof using.
  unfold id_of_z, z_of_id.
  intros.
  apply Zdigits.binary_to_Z_to_binary.
Qed.

Definition id_ltb (x y : id) : bool :=
  BinInt.Z.ltb (z_of_id x) (z_of_id y).

Definition addr_eq_dec := String.string_dec.

Module ChordIDParams <: IDSpaceParams.
  Definition name := addr.
  Definition id := id.
  Definition hash := hash.
  Definition ltb := id_ltb.
  Definition lt := fun a b => id_ltb a b = true.

  Definition name_eq_dec := addr_eq_dec.
  Definition id_eq_dec := id_eq_dec.

  (* useful notations for lt and ltb *)
  Notation "a < b" := (lt a b) : id_scope.
  Notation "a <? b" := (ltb a b) : id_scope.
  Open Scope id_scope.

  (* ltb is a decision procedure for the lt relation *)
  Definition ltb_correct :
    forall a b,
      a <? b = true <-> a < b.
  Proof.
    intuition.
  Qed.

  Lemma ltb_leb :
    forall x y,
      BinInt.Z.ltb x y = true ->
      BinInt.Z.leb x y = true.
  Proof.
    intros.
    unfold BinInt.Z.ltb, BinInt.Z.leb in *.
    repeat break_match; congruence.
  Qed.

  (* The lt relation is a strict total order *)
  Definition lt_asymm :
    forall a b,
      a < b ->
      ~ b < a.
  Proof.
    intuition.
    unfold lt, id_ltb in *.
    find_rewrite_lem BinInt.Z.ltb_antisym.
    find_apply_lem_hyp ltb_leb.
    find_rewrite. simpl in *. congruence.
  Qed.

  Definition lt_trans :
    forall a b c,
      a < b ->
      b < c ->
      a < c.
  Proof.
    intros.
    unfold lt, id_ltb in *.
    apply BinInt.Z.ltb_lt.
    find_apply_lem_hyp BinInt.Z.ltb_lt.
    eapply BinInt.Z.lt_trans; [|eauto].
    now apply BinInt.Z.ltb_lt.
  Qed.

  Definition lt_irrefl :
    forall a,
      ~ a < a.
  Proof.
    intros.
    unfold lt, id_ltb in *.
    rewrite BinInt.Z.ltb_irrefl.
    congruence.
  Qed.

  Lemma plus_2x_inj :
    forall b x y,
      BinInt.Z.add b (2 * x) = BinInt.Z.add b (2 * y) ->
      x = y.
  Proof. intros. omega.
  Qed.

  Lemma bit_adds_equal :
    forall b1 b2  x y,
      ((Zdigits.bit_value b1) + (2 * x))%Z = ((Zdigits.bit_value b2) + (2 * y))%Z ->
      b1 = b2.
  Proof.
    intros. destruct b1; destruct b2; auto.
    - exfalso. unfold Zdigits.bit_value in *. omega.
    - exfalso. unfold Zdigits.bit_value in *. omega.
  Qed.

  Lemma binary_value_inj :
    forall n (a : Bvector.Bvector n) b,
      Zdigits.binary_value n a = Zdigits.binary_value n b ->
      a = b.
  Proof.
    induction n; intros.
    - destruct a using Vector.case0.
      destruct b using Vector.case0.
      auto.
    - destruct a using Vector.caseS'.
      destruct b using Vector.caseS'.
      repeat rewrite Zdigits.binary_value_Sn in H.
      find_copy_apply_lem_hyp bit_adds_equal.
      subst.
      find_copy_apply_lem_hyp plus_2x_inj.
      find_apply_hyp_hyp. congruence.
  Qed.

  Definition lt_total :
    forall a b,
      a < b \/ b < a \/ a = b.
  Proof.
    intros.
    unfold lt, id_ltb, z_of_id.
    match goal with
    | |- context [(?x <? ?y)%Z] =>
      destruct ( Z_lt_le_dec x y)
    end; auto.
    - left. apply Z.ltb_lt. auto.
    - find_apply_lem_hyp Z_le_lt_eq_dec.
      intuition.
      + right. left.
        apply Z.ltb_lt. auto.
      + find_apply_lem_hyp binary_value_inj.
        auto.
  Qed.

  Close Scope id_scope.
End ChordIDParams.

Module ChordIDSpace := IDSpace(ChordIDParams).
Export ChordIDSpace.

(* only need this to make client.ml work :/ *)
Definition forge_pointer (i : id) : ChordIDSpace.pointer :=
  {| ptrAddr := "FAKE"%string;
     ptrId := i |}.

Ltac inv_prop P :=
  match goal with
  | [ H : context[P] |- _] =>
    inv H
  end.

Module ChordSystem <: DynamicSystem.
  Definition addr := addr.
  Definition addr_eq_dec :
    forall a b : addr, {a = b} + {a <> b}
    := string_dec.
  Definition id := id.

  Definition client_addr := client_addr.
  Definition client_addr_dec := client_addr_dec.

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
  Proof using.
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
    decide equality.
    - apply pointer_eq_dec.
    - apply pointer_eq_dec.
    - apply (list_eq_dec pointer_eq_dec).
    - apply (list_eq_dec pointer_eq_dec).
    - apply (option_eq_dec _ pointer_eq_dec).
  Defined.

  Inductive _timeout :=
  | Tick : _timeout
  | RectifyTick : _timeout
  | KeepaliveTick : _timeout
  | Request : addr -> payload -> _timeout.
  Definition timeout := _timeout.

  Definition timeout_eq_dec : forall x y : timeout,
      {x = y} + {x <> y}.
    decide equality.
    - subst.
      apply payload_eq_dec.
    - apply addr_eq_dec.
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
       known := make_pointer h;
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

  Definition set_rectify_with (st : data) (rw : pointer) : data :=
    {| ptr := ptr st;
       pred := pred st;
       succ_list := succ_list st;
       known := known st;
       joined := joined st;
       rectify_with := Some rw;
       cur_request := cur_request st;
       delayed_queries := delayed_queries st |}.

  Definition schedule_rectify_with (st : data) (rw : pointer) : res :=
    match rectify_with st with
    | Some rw0 =>
      if ptr_between_bool rw0 rw (ptr st)
      then (set_rectify_with st rw, [], [], [])
      else (st, [], [], [])
    | None => (set_rectify_with st rw, [], [RectifyTick], [])
    end.

  Definition send_eq_dec :
    forall x y : addr * payload,
      {x = y} + {x <> y}.
    decide equality.
    - subst.
      apply payload_eq_dec.
    - apply addr_eq_dec.
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
      (clear_query st, [], [], cst)
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

  Definition handle_rectify (st : data) (my_pred : pointer) (notifier : pointer) : res :=
    if ptr_between_bool my_pred notifier (ptr st)
    then (update_pred st notifier, [], [], [])
    else (st, [], [], []).

  Definition handle_stabilize (h : addr) (src : pointer) (st : data) (q : query) (new_succ : option pointer) (succs : list pointer) : res :=
    let new_st := update_succ_list st (make_succs src succs) in
    match new_succ with
    | Some new_succ =>
      if ptr_between_bool (ptr st) new_succ src
      then start_query h new_st (Stabilize2 new_succ)
      else end_query (new_st, [(addr_of src, Notify)], [], [])
    | None =>
      end_query (new_st, [(addr_of src, Notify)], [], [])
    end.

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
      handle_stabilize h (make_pointer src) st q new_succ succs
    | Stabilize2 new_succ, GotSuccList succs =>
      end_query (update_succ_list st (make_succs new_succ succs),
                 [(addr_of new_succ, Notify)],
                 [],
                 [])
    | Join known, GotBestPredecessor best_pred =>
      let a := addr_of best_pred in
      let req := next_msg_for_join (ptr st) src a in
      (update_query st best_pred (Join known) req,
       [(a, req)],
       [Request a req],
       timeouts_in st)
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
    | Notify, _, _ => schedule_rectify_with st (make_pointer src)
    | Ping, _, _ => (st, [(src, Pong)], [], [])
    | _, Some (query_dst, q, _), true => handle_query_req_busy src st msg
    | _, Some (query_dst, q, _), false =>
      if addr_eq_dec (addr_of query_dst) src
      then handle_query_res src dst st q msg
      else (st, [], [], [])
    | _, None, _ => (st, handle_query_req st src msg, [], [])
    end.

  Definition recv_handler (src : addr) (dst : addr) (st : data) (msg : payload) : res :=
    let '(st, ms1, nts1, cts1) := handle_msg src dst st msg in
    let '(st, ms2, nts2, cts2) := do_delayed_queries dst st in
    let nts := nts2 ++ remove_all timeout_eq_dec cts2 nts1 in
    (st, ms2 ++ ms1, nts, cts1 ++ cts2).

  Definition pi {A B C D : Type} (t : A * B * C * D) : A * B * C :=
    let '(a, b, c, d) := t in (a, b, c).

  Definition sort_by_between (h : addr) : list pointer -> list pointer :=
    sort pointer (unroll_between_ptr h).

  Lemma sort_by_between_permutes :
    forall h l l',
      l' = sort_by_between h l ->
      Permutation.Permutation l l'.
  Proof.
    unfold sort_by_between, unroll_between_ptr.
    intro.
    apply sort_permutes;
      eauto using unrolling_reflexive, unrolling_transitive, unrolling_total.
  Qed.

  Definition find_pred (h : addr) (sorted_ring : list pointer) : option pointer :=
    hd_error (rev sorted_ring).

  Definition start_handler (h : addr) (knowns : list addr) : data * list (addr * payload) * list timeout :=
    match sort_by_between h (map make_pointer knowns) with
    (* prohibited by semantics *)
    | [] =>
      empty_start_res h
    | [k] =>
      pi (start_query h (init_state_join h (addr_of k)) (Join k))
    | sorted_ring =>
      let succs := chop_succs (List.tl sorted_ring) in
      let pred := find_pred h sorted_ring in
      (init_state_preset h pred succs, [], [Tick])
    end.

  Inductive timeout_effect :=
  | Ineffective : timeout_effect
  | StartStabilize : timeout_effect
  | DetectFailure : timeout_effect
  | StartRectify : timeout_effect
  | SetPred : timeout_effect
  | SendKeepalives : timeout_effect.

  Definition timeout_effect_eq_dec :
    forall x y : timeout_effect,
      {x = y} + {x <> y}.
  Proof using.
    decide equality; auto using addr_eq_dec, list_eq_dec, pointer_eq_dec.
  Defined.

  Definition tick_handler (h : addr) (st : data) : res * timeout_effect :=
    match cur_request st, joined st with
    | None, true => (add_tick (start_query h st Stabilize), StartStabilize)
    | _, _ => ((st, [], [Tick], []), Ineffective)
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

  Definition keepalive_handler (st : data) : res * timeout_effect :=
    let ms := send_keepalives st in
    ((st, ms, [KeepaliveTick], []), SendKeepalives).

  Definition request_timeout_handler (h : addr) (st : data) (dst : addr) (msg : payload) : res * timeout_effect :=
    match cur_request st with
    | Some (ptr, q, _) =>
      if addr_eq_dec (addr_of ptr) dst
      then let '(st', ms, nts, cts) := handle_query_timeout h st ptr q in
           let '(st'', ms', nts', cts') := do_delayed_queries h st' in
           (st'', ms ++ ms', nts ++ nts', cts ++ cts', DetectFailure)
      else ((st, [], [], []), Ineffective) (* shouldn't happen *)
    | None => ((st, [], [], []), Ineffective) (* shouldn't happen *)
    end.

  Definition do_rectify (h : addr) (st : data) : res * timeout_effect :=
    match joined st, cur_request st, rectify_with st with
    | true, None, Some new =>
      let st := clear_rectify_with st in
      match pred st with
      | Some _ => (start_query h st (Rectify new), StartRectify)
      | None => ((update_pred st new, [], [], []), SetPred)
      end
    | _, Some cr, Some new =>
      ((st, [], [RectifyTick], []), Ineffective)
    | _, _, _ =>
      ((st, [], [], []), Ineffective) (* shouldn't happen *)
    end.

  Definition timeout_handler_eff (h : addr) (st : data) (t : timeout) : res * timeout_effect :=
    match t with
    | Request dst msg => request_timeout_handler h st dst msg
    | Tick => tick_handler h st
    | KeepaliveTick => keepalive_handler st
    | RectifyTick => do_rectify h st
    end.

  Definition timeout_handler (h : addr) (st : data) (t : timeout) : res :=
    fst (timeout_handler_eff h st t).

  Inductive _label :=
  | Input : addr -> addr -> payload -> _label
  | Output : addr -> addr -> payload -> _label
  | RecvMsg : addr -> addr -> payload -> _label
  | Timeout : addr -> timeout -> timeout_effect -> _label.
  Definition label := _label.

  Definition label_eq_dec :
    forall x y : label,
      {x = y} + {x <> y}.
  Proof using.
    decide equality;
      auto using addr_eq_dec, payload_eq_dec, timeout_eq_dec, timeout_effect_eq_dec.
  Defined.

  Definition data_eq_dec :
    forall st st' : data,
      {st = st'} + {st <> st'}.
  Proof using.
    repeat (decide equality; auto using list_eq_dec, pointer_eq_dec, addr_eq_dec, id_eq_dec).
  Defined.

  Definition timeout_handler_l (h : addr) (st : data) (t : timeout) :=
    let '(res, effect) := timeout_handler_eff h st t in
    (res, Timeout h t effect).

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

  Definition label_input : addr -> addr -> payload -> label := Input.
  Definition label_output : addr -> addr -> payload -> label := Output.

  Lemma timeout_handler_labeling :
    forall h st t r,
      (timeout_handler h st t = r ->
      exists l,
        timeout_handler_l h st t = (r, l)) /\
      (forall l,
          timeout_handler_l h st t = (r, l) ->
          timeout_handler h st t = r).
  Proof using.
    unfold timeout_handler_l, timeout_handler.
    intuition.
    - destruct (timeout_handler_eff h st t) as [r' l].
      simpl in *.
      subst_max.
      eexists; eauto.
    - break_let.
      tuple_inversion.
      reflexivity.
  Qed.

End ChordSystem.
Export ChordSystem.

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

(* this is not quite what it sounds like, since Chord.start_query will sometimes not send anything *)
Inductive query_request : query -> payload -> Prop :=
| QReq_RectifyPing : forall n, query_request (Rectify n) Ping
| QReq_StabilizeGetPredAndSuccs : query_request Stabilize GetPredAndSuccs
| QReq_Stabilize2 : forall p, query_request (Stabilize2 p) GetSuccList
| QReq_JoinGetBestPredecessor : forall k a, query_request (Join k) (GetBestPredecessor a)
| QReq_JoinGetSuccList : forall k, query_request (Join k) GetSuccList
| QReq_Join2 : forall n, query_request (Join2 n) GetSuccList.
Hint Constructors query_request.

Inductive query_response : query -> payload -> Prop :=
| QRes_RectifyPong : forall n, query_response (Rectify n) Pong
| QRes_StabilizeGetPredAndSuccs : forall p l, query_response Stabilize (GotPredAndSuccs p l)
| QRes_Stabilize2 : forall p l, query_response (Stabilize2 p) (GotSuccList l)
| QRes_JoinGotBestPredecessor : forall k p, query_response (Join k) (GotBestPredecessor p)
| QRes_JoinGotSuccList : forall k l, query_response (Join k) (GotSuccList l)
| QRes_Join2 : forall n l, query_response (Join2 n) (GotSuccList l).
Hint Constructors query_response.

Inductive response_payload : payload -> Prop :=
| res_GotBestPredecessor : forall p, response_payload (GotBestPredecessor p)
| res_GotSuccList : forall l, response_payload (GotSuccList l)
| res_GotPredAndSuccs : forall p l, response_payload (GotPredAndSuccs p l)
| res_Pong : response_payload Pong
| res_Busy : response_payload Busy.

Definition response_payload_dec :
  forall p,
    {response_payload p} + {~ response_payload p}.
Proof.
  destruct p;
    solve [left; constructor|right; intro; inv_prop response_payload].
Defined.


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

Module ConstrainedChord <: ConstrainedDynamicSystem.
  Include ChordSystem.

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
  | RectifyTick_unconstrained : forall gst h,
      _timeout_constraint gst h RectifyTick
  | Request_needs_dst_dead_and_no_msgs : forall gst dst h p,
      In dst (failed_nodes gst) ->
      (forall m, request_response_pair p m -> ~ In (dst, (h, m)) (msgs gst)) ->
      _timeout_constraint gst h (Request dst p).
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
      In (src, (dst, GotPredAndSuccs p succs)) ms \/
      In (src, (dst, GotSuccList succs)) ms ->
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

  Inductive succs_msg : payload -> list pointer -> Prop :=
  | SuccsMsgGotSuccList :
      forall succs, succs_msg (GotSuccList succs) succs
  | SuccsMsgGotPredAndSuccs :
      forall p succs,
      succs_msg (GotPredAndSuccs p succs) succs.
  Hint Constructors succs_msg.

  Definition no_live_node_skips (gst : global_state) (p : addr) : Prop :=
    forall h st succs,
      live_node gst h ->
      sigma gst h = Some st ->
      succs = map ChordIDSpace.id_of (succ_list st) ->
      not_skipped (hash h) succs (hash p).
  Hint Unfold no_live_node_skips.

  Definition no_msg_to_live_node_skips (gst : global_state) (p : addr) : Prop :=
    forall src h m succs,
      In h (nodes gst) ->
      ~ In h (failed_nodes gst) ->
      In (src, (h, m)) (msgs gst) ->
      succs_msg m succs ->
      not_skipped (hash src) (map ChordIDSpace.id_of succs) (hash p).
  Hint Unfold no_msg_to_live_node_skips.
  
  (* "A principal node is a member that is not skipped by any member's
     extended successor list" *)
  Definition principal (gst : global_state) (p : addr) : Prop :=
    live_node gst p /\
    no_live_node_skips gst p /\
    no_msg_to_live_node_skips gst p.

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

End ConstrainedChord.

Module ChordSemantics := DynamicSemantics(ConstrainedChord).

Export ChordSemantics.
Export ConstrainedChord.

Definition hash_injective_on (gst : global_state) : Prop :=
  forall n m,
    In n (nodes gst) ->
    In m (nodes gst) ->
    hash n = hash m ->
    n = m.

Definition initial_st (gst : global_state) : Prop :=
  (* at least N+1 nodes *)
  length (nodes gst) >= SUCC_LIST_LEN + 1 /\
  (* no duplicate addresses *)
  NoDup (nodes gst) /\
  (* all addresses hash to distinct IDs *)
  hash_injective_on gst /\
  (* nodes aren't clients *)
  (forall h, In h (nodes gst) -> ~client_addr h) /\
  (* no messages, failed nodes, or events *)
  failed_nodes gst = [] /\
  msgs gst = [] /\
  trace gst = [] /\
  (* start handler has been run at all nodes *)
  (forall h,
      In h (nodes gst) ->
      forall st ms nts,
        start_handler h (nodes gst) = (st, ms, nts) ->
        ms = [] /\
        timeouts gst h = nts /\
        sigma gst h = Some st) /\
  (* no other timeouts or state *)
  (forall h, ~ In h (nodes gst) -> timeouts gst h = []) /\
  (forall h, ~ In h (nodes gst) -> sigma gst h = None).
