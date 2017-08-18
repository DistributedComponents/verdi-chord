open ExtractedChord
open ExtractedChord.ChordSystem
open Printf
open Str

let show_id i =
  Digest.to_hex (Util.bytes_of_char_list (id_to_ascii i))

let show_pointer p =
  show_id p.ChordIDSpace.ptrId

let show_pointer_list ps =
  let strs = map show_pointer ps in
  "[" ^ String.concat ", " strs ^ "]"

let show_addr a =
  Util.bytes_of_char_list a

let caps_bool b =
  if b then "True" else "False"

let show_opt_pointer p =
  Util.map_default show_pointer "None" p

let show_msg = function
  | GetBestPredecessor p -> "GetBestPredecessor " ^ show_pointer p
  | GotBestPredecessor p -> "GotBestPredecessor " ^ show_pointer p
  | GetSuccList -> "GetSuccList"
  | GotSuccList ps -> "GotSuccList " ^ show_pointer_list ps
  | GetPredAndSuccs -> "GetPredAndSuccs"
  | GotPredAndSuccs (pred, succs) -> "GotPredAndSuccs " ^ show_opt_pointer pred ^ " " ^ show_pointer_list succs
  | Notify -> "Notify"
  | Ping -> "Ping"
  | Pong -> "Pong"
  | Busy -> "Busy"

let show_query = function
  | Rectify p -> "Rectify " ^ show_pointer p
  | Stabilize -> "Stabilize"
  | Stabilize2 p -> "Stabilize2 " ^ show_pointer p
  | Join p -> "Join " ^ show_pointer p
  | Join2 p -> "Join2 " ^ show_pointer p

let show_st_ptr st =
  show_pointer st.ptr

let show_request ((ptr, q), _) =
  Printf.sprintf "query(%s, %s)" (show_pointer ptr) (show_query q)

let show_st_cur_request st =
  Util.map_default show_request "None" st.cur_request

let log_info_from st msg =
  let prefix = Printf.sprintf "node(%s):" (show_st_ptr st) in
  Util.info (prefix ^ msg)

let log_dbg_from st msg =
  let prefix = Printf.sprintf "node(%s):" (show_st_ptr st) in
  Util.debug (prefix ^ msg)

let log_st st =
  let log = log_info_from st in
  log ("succ_list := " ^ show_pointer_list st.succ_list);
  log ("pred := " ^ show_opt_pointer st.pred);
  log ("known := " ^ show_pointer st.known);
  log ("joined := " ^ caps_bool st.joined);
  log ("rectify_with := " ^ show_opt_pointer st.rectify_with);
  log ("cur_request := " ^ show_st_cur_request st)

let log_recv st src msg =
  let log = log_dbg_from st in
  log ("recv from " ^ show_addr src ^ ": " ^ show_msg msg)

let log_send st dst msg =
  let log = log_dbg_from st in
  log ("send to " ^ show_addr dst ^ ":" ^ show_msg msg)

let log_timeout st = function
  | Tick -> log_dbg_from st "ticked"
  | RectifyTick -> log_dbg_from st "ticked for rectify"
  | KeepaliveTick -> log_dbg_from st "ticked for keepalive"
  | Request (dead, msg) ->
    log_dbg_from st ("request " ^ show_msg msg
                     ^ " from " ^ show_pointer st.ptr
                     ^ " to " ^ show_addr dead ^ " timed out")

let rebracket4 (((a, b), c), d) = (a, b, c, d)
let rebracket3 ((a, b), c) = (a, b, c)

module type ChordConfig = sig
  val tick_timeout : float
  val keepalive_timeout : float
  val request_timeout : float
  val debug : bool
end

type chord_config =
  { tick_timeout : float
  ; keepalive_timeout : float
  ; request_timeout : float
  ; debug : bool
  }

let make_config_module cc =
  (module struct
     let tick_timeout = cc.tick_timeout
     let keepalive_timeout = cc.keepalive_timeout
     let request_timeout = cc.request_timeout
     let debug = cc.debug
   end : ChordConfig)

module ChordArrangement (C : ChordConfig) : DynamicShim.DYNAMIC_ARRANGEMENT = struct
  type name = addr
  type state = _data
  type msg = payload
  type timeout = ExtractedChord.ChordSystem._timeout
  type res = state * (name * msg) list * (timeout list) * (timeout list)
  let addr_of_name n =
    let (a :: p :: _) = split (regexp ":") (Util.bytes_of_char_list n) in
    (a, int_of_string p)
  let name_of_addr (s, p) =
    Util.char_list_of_string (s ^ ":" ^ string_of_int p)
  let start_handler n ks =
    Random.self_init ();
    rebracket3 (init n ks)
  let recv_handler s d m st =
    rebracket4 (handleNet s d m st)
  let timeout_handler n s t =
    rebracket4 (handleTimeout n s t)

  let fuzzy_timeout t =
    let fuzz = max (t /. 5.0) 2.0 in
    t +. Random.float fuzz

  let set_timeout = function
    | Tick -> fuzzy_timeout C.tick_timeout
    | RectifyTick -> fuzzy_timeout C.tick_timeout
    (* must be less than the request timeout *)
    | KeepaliveTick -> C.keepalive_timeout
    | Request (a, b) -> C.request_timeout

  let default_timeout = 1.0
  let debug = C.debug
  let debug_recv st (src, msg) =
    log_st st;
    log_recv st src msg;
    flush_all ()
  let debug_send st (dst, msg) =
    log_st st;
    log_send st dst msg;
    flush_all ()
  let debug_timeout st t =
    log_timeout st t;
    flush_all ()
end

let run cc nm knowns =
  let (module Conf) = make_config_module cc in
  let (module Shim : DynamicShim.ShimSig) =
    (module DynamicShim.Shim(ChordArrangement(Conf))) in
  Shim.main nm knowns
