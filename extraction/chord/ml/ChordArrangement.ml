open ExtractedChord
open Printf
open Str

let chord_default_port = 7000

let show_id i =
  Digest.to_hex (Util.string_of_char_list (id_to_ascii i))

let show_pointer p =
  show_id p.ChordIDSpace.ptrId

let show_pointer_list ps =
  let strs = map show_pointer ps in
  "[" ^ String.concat ", " strs ^ "]"

let show_addr a =
  Util.string_of_char_list a

let caps_bool b =
  if b then "True" else "False"

let show_opt_pointer p =
  Util.map_default show_pointer "None" p

let show_msg = function
  | ChordSystem.GetBestPredecessor p -> "GetBestPredecessor " ^ show_pointer p
  | ChordSystem.GotBestPredecessor p -> "GotBestPredecessor " ^ show_pointer p
  | ChordSystem.GetSuccList -> "GetSuccList"
  | ChordSystem.GotSuccList ps -> "GotSuccList " ^ show_pointer_list ps
  | ChordSystem.GetPredAndSuccs -> "GetPredAndSuccs"
  | ChordSystem.GotPredAndSuccs (pred, succs) -> "GotPredAndSuccs " ^ show_opt_pointer pred ^ " " ^ show_pointer_list succs
  | ChordSystem.Notify -> "Notify"
  | ChordSystem.Ping -> "Ping"
  | ChordSystem.Pong -> "Pong"
  | ChordSystem.Busy -> "Busy"

let show_query = function
  | ChordSystem.Rectify p -> "Rectify " ^ show_pointer p
  | ChordSystem.Stabilize -> "Stabilize"
  | ChordSystem.Stabilize2 p -> "Stabilize2 " ^ show_pointer p
  | ChordSystem.Join p -> "Join " ^ show_pointer p
  | ChordSystem.Join2 p -> "Join2 " ^ show_pointer p

let show_st_ptr st =
  show_pointer st.ChordSystem.ptr

let show_request ((ptr, q), _) =
  Printf.sprintf "query(%s, %s)" (show_pointer ptr) (show_query q)

let show_st_cur_request st =
  Util.map_default show_request "None" st.ChordSystem.cur_request

let log_info_from st msg =
  let prefix = Printf.sprintf "node(%s):" (show_st_ptr st) in
  Util.info (prefix ^ msg)

let log_dbg_from st msg =
  let prefix = Printf.sprintf "node(%s):" (show_st_ptr st) in
  Util.debug (prefix ^ msg)

let log_st st =
  let log = log_info_from st in
  log ("succ_list := " ^ show_pointer_list st.ChordSystem.succ_list);
  log ("pred := " ^ show_opt_pointer st.ChordSystem.pred);
  log ("known := " ^ show_pointer st.ChordSystem.known);
  log ("joined := " ^ caps_bool st.ChordSystem.joined);
  log ("rectify_with := " ^ show_opt_pointer st.ChordSystem.rectify_with);
  log ("cur_request := " ^ show_st_cur_request st)

let log_recv st src msg =
  let log = log_dbg_from st in
  log ("recv from " ^ show_addr src ^ ": " ^ show_msg msg)

let log_send st dst msg =
  let log = log_dbg_from st in
  log ("send to " ^ show_addr dst ^ ":" ^ show_msg msg)

let log_timeout st = function
  | ChordSystem.Tick -> log_dbg_from st "ticked"
  | ChordSystem.RectifyTick -> log_dbg_from st "ticked for rectify"
  | ChordSystem.KeepaliveTick -> log_dbg_from st "ticked for keepalive"
  | ChordSystem.Request (dead, msg) ->
    log_dbg_from st ("request " ^ show_msg msg
                     ^ " from " ^ show_pointer st.ChordSystem.ptr
                     ^ " to " ^ show_addr dead ^ " timed out")

let rebracket4 (((a, b), c), d) = (a, b, c, d)
let rebracket3 ((a, b), c) = (a, b, c)

module type ChordConfig = sig
  val tick_timeout : float
  val keepalive_timeout : float
  val request_timeout : float
  val debug : bool
end

module ChordArrangement (C : ChordConfig) = struct
  type addr = string
  type name = ChordSystem.addr
  type state = ChordSystem._data
  type msg = ChordSystem.payload
  type timeout = ExtractedChord.ChordSystem._timeout
  type res = state * (name * msg) list * (timeout list) * (timeout list)
  let port = chord_default_port
  let addr_of_name n =
    let (a :: p :: _) = split (regexp ":") (Util.string_of_char_list n) in
    a
  let name_of_addr s =
    Util.char_list_of_string s
  let start_handler n ks =
    Random.self_init ();
    rebracket3 (init n ks)
  let msg_handler s d m st =
    rebracket4 (handleNet s d m st)
  let timeout_handler n s t =
    rebracket4 (handleTimeout n s t)

  let deserialize_msg b = Marshal.from_bytes b 0

  let serialize_msg msg = Marshal.to_bytes msg []

  let fuzzy_timeout t =
    let fuzz = max (t /. 5.0) 2.0 in
    t +. Random.float fuzz

  let set_timeout = function
    | ChordSystem.Tick -> fuzzy_timeout C.tick_timeout
    | ChordSystem.RectifyTick -> fuzzy_timeout C.tick_timeout
    (* must be less than the request timeout *)
    | ChordSystem.KeepaliveTick -> C.keepalive_timeout
    | ChordSystem.Request (a, b) -> C.request_timeout

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

type chord_config =
  { tick_timeout : float
  ; keepalive_timeout : float
  ; request_timeout : float
  ; debug : bool
  }

let run cc nm knowns =
  let module Conf = struct
     let tick_timeout = cc.tick_timeout
     let keepalive_timeout = cc.keepalive_timeout
     let request_timeout = cc.request_timeout
     let debug = cc.debug
  end in
  let module Shim = DynamicShim.Shim(ChordArrangement(Conf)) in
  Shim.main nm knowns
