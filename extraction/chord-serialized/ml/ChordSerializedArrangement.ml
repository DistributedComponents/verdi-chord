open ExtractedChordSerialized
open Printf
open Str

let chord_default_port = 7000

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
  | ChordSerializedSystem.GetBestPredecessor p -> "GetBestPredecessor " ^ show_pointer p
  | ChordSerializedSystem.GotBestPredecessor p -> "GotBestPredecessor " ^ show_pointer p
  | ChordSerializedSystem.GetSuccList -> "GetSuccList"
  | ChordSerializedSystem.GotSuccList ps -> "GotSuccList " ^ show_pointer_list ps
  | ChordSerializedSystem.GetPredAndSuccs -> "GetPredAndSuccs"
  | ChordSerializedSystem.GotPredAndSuccs (pred, succs) -> "GotPredAndSuccs " ^ show_opt_pointer pred ^ " " ^ show_pointer_list succs
  | ChordSerializedSystem.Notify -> "Notify"
  | ChordSerializedSystem.Ping -> "Ping"
  | ChordSerializedSystem.Pong -> "Pong"
  | ChordSerializedSystem.Busy -> "Busy"

let show_query = function
  | ChordSerializedSystem.Rectify p -> "Rectify " ^ show_pointer p
  | ChordSerializedSystem.Stabilize -> "Stabilize"
  | ChordSerializedSystem.Stabilize2 p -> "Stabilize2 " ^ show_pointer p
  | ChordSerializedSystem.Join p -> "Join " ^ show_pointer p
  | ChordSerializedSystem.Join2 p -> "Join2 " ^ show_pointer p

let show_st_ptr st =
  show_pointer st.ChordSerializedSystem.ptr

let show_request ((ptr, q), _) =
  Printf.sprintf "query(%s, %s)" (show_pointer ptr) (show_query q)

let show_st_cur_request st =
  Util.map_default show_request "None" st.ChordSerializedSystem.cur_request

let log_info_from st msg =
  let prefix = Printf.sprintf "node(%s):" (show_st_ptr st) in
  Util.info (prefix ^ msg)

let log_dbg_from st msg =
  let prefix = Printf.sprintf "node(%s):" (show_st_ptr st) in
  Util.debug (prefix ^ msg)

let log_st st =
  let log = log_info_from st in
  log ("succ_list := " ^ show_pointer_list st.ChordSerializedSystem.succ_list);
  log ("pred := " ^ show_opt_pointer st.ChordSerializedSystem.pred);
  log ("known := " ^ show_pointer st.ChordSerializedSystem.known);
  log ("joined := " ^ caps_bool st.ChordSerializedSystem.joined);
  log ("rectify_with := " ^ show_opt_pointer st.ChordSerializedSystem.rectify_with);
  log ("cur_request := " ^ show_st_cur_request st)

let log_recv st src msg =
  let log = log_dbg_from st in
  log ("recv from " ^ show_addr src ^ ": " ^ show_msg msg)

let log_send st dst msg =
  let log = log_dbg_from st in
  log ("send to " ^ show_addr dst ^ ":" ^ show_msg msg)

let log_timeout st = function
  | ChordSerializedSystem.Tick -> log_dbg_from st "ticked"
  | ChordSerializedSystem.RectifyTick -> log_dbg_from st "ticked for rectify"
  | ChordSerializedSystem.KeepaliveTick -> log_dbg_from st "ticked for keepalive"
  | ChordSerializedSystem.Request (dead, msg) ->
    log_dbg_from st ("request " ^ show_msg msg
                     ^ " from " ^ show_pointer st.ChordSerializedSystem.ptr
                     ^ " to " ^ show_addr dead ^ " timed out")

let rebracket4 (((a, b), c), d) = (a, b, c, d)
let rebracket3 ((a, b), c) = (a, b, c)

module type ChordSerializedConfig = sig
  val tick_timeout : float
  val keepalive_timeout : float
  val request_timeout : float
  val debug : bool
end

module ChordSerializedArrangement (C : ChordSerializedConfig) = struct
  type addr = string
  type name = ChordSerializedSystem.addr
  type state = ChordSerializedSystem._data
  type msg = ChordSerializedSystem.payload
  type timeout = ExtractedChordSerialized.ChordSerializedSystem._timeout
  type res = state * (name * msg) list * (timeout list) * (timeout list)
  let port = chord_default_port
  let addr_of_name n =
    let (a :: p :: _) = split (regexp ":") (Util.bytes_of_char_list n) in
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
    | ChordSerializedSystem.Tick -> fuzzy_timeout C.tick_timeout
    | ChordSerializedSystem.RectifyTick -> fuzzy_timeout C.tick_timeout
    (* must be less than the request timeout *)
    | ChordSerializedSystem.KeepaliveTick -> C.keepalive_timeout
    | ChordSerializedSystem.Request (a, b) -> C.request_timeout

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
  let module Shim = DynamicShim.Shim(ChordSerializedArrangement(Conf)) in
  Shim.main nm knowns
