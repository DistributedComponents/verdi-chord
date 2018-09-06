open ExtractedChord
open Printf
open Str
module VRUtil = Util
open Yojson.Basic

let chord_default_port = 7000

let type_of_msg = function
  | ChordSystem.GetBestPredecessor _ -> "GetBestPredecessor"
  | ChordSystem.GotBestPredecessor _ -> "GotBestPredecessor"
  | ChordSystem.GetSuccList -> "GetSuccList"
  | ChordSystem.GotSuccList _ -> "GotSuccList"
  | ChordSystem.GetPredAndSuccs -> "GetPredAndSuccs"
  | ChordSystem.GotPredAndSuccs _ -> "GotPredAndSuccs"
  | ChordSystem.Notify -> "Notify"
  | ChordSystem.Ping -> "Ping"
  | ChordSystem.Pong -> "Pong"
  | ChordSystem.Busy -> "Busy"

(*
let json_of_addr a =
  `String (VRUtil.string_of_char_list a)
*)
let json_of_addr a =
  let s = VRUtil.string_of_char_list a in
  let d = Digest.string s in
  let ds = Digest.to_hex d in
  `String ds

let json_of_id i =
  `String (Digest.to_hex (VRUtil.string_of_char_list (id_to_ascii i)))

let json_of_pointer p =
  json_of_id p.ChordIDSpace.ptrId

let json_of_opt_pointer po =
  VRUtil.map_default json_of_pointer `Null po

let json_of_msg = function
  | ChordSystem.GetBestPredecessor p ->
     `Assoc [("pointer", json_of_pointer p)]
  | ChordSystem.GotBestPredecessor p ->
     `Assoc [("pointer", json_of_pointer p)]
  | ChordSystem.GetSuccList ->
     `Null
  | ChordSystem.GotSuccList ps ->
     `Assoc [("pointers", `List (List.map json_of_pointer ps))]
  | ChordSystem.GetPredAndSuccs ->
     `Null
  | ChordSystem.GotPredAndSuccs (pred, succs) ->
     `Assoc [ ("pred", json_of_opt_pointer pred)
            ; ("succs", `List (List.map json_of_pointer succs))]
  | ChordSystem.Notify ->
     `Null
  | ChordSystem.Ping ->
     `Null
  | ChordSystem.Pong ->
     `Null
  | ChordSystem.Busy ->
     `Null

let json_of_query = function
  | ChordSystem.Rectify p ->
     `Assoc [("type", `String "Rectify")
            ; ("pointer", json_of_pointer p)]
  | ChordSystem.Stabilize ->
     `Assoc [("type", `String "Stabilize")]
  | ChordSystem.Stabilize2 p ->
     `Assoc [("type", `String "Stabilize2")
            ; ("pointer", json_of_pointer p)]
  | ChordSystem.Join p ->
     `Assoc [("type", `String "Join")
            ; ("pointer", json_of_pointer p)]
  | ChordSystem.Join2 p ->
     `Assoc [("type", `String "Join2")
            ; ("pointer", json_of_pointer p)]

let json_of_st_ptr st =
  json_of_pointer st.ChordSystem.ptr

let json_of_request ((ptr, q), _) =
  `Assoc [("pointer", json_of_pointer ptr)
         ; ("query", json_of_query q)]

let json_of_st_cur_request st =
  VRUtil.map_default json_of_request `Null st.ChordSystem.cur_request

let json_of_st st =
  `Assoc [ ("succ_list", `List (List.map json_of_pointer st.ChordSystem.succ_list))
         ; ("pred", json_of_opt_pointer st.ChordSystem.pred)
         ; ("known", json_of_pointer st.ChordSystem.known)
         ; ("joined", `Bool st.ChordSystem.joined)
         ; ("rectify_with", json_of_opt_pointer st.ChordSystem.rectify_with)
         ; ("cur_request", json_of_st_cur_request st)]

let json_of_recv st src msg =
  `Assoc [ ("from", json_of_addr src)
         ; ("to", json_of_st_ptr st)
         ; ("type", `String (type_of_msg msg))
         ; ("body", json_of_msg msg)]

let json_of_send st dst msg =
  `Assoc [ ("from", json_of_st_ptr st)
         ; ("to", json_of_addr dst)
         ; ("type", `String (type_of_msg msg))
         ; ("body", json_of_msg msg)]

let json_of_timeout = function
  | ChordSystem.Tick ->
     `Assoc [("type", `String "Tick")]
  | ChordSystem.RectifyTick ->
     `Assoc [("type", `String "RectifyTick")]
  | ChordSystem.KeepaliveTick ->
     `Assoc [("type", `String "KeepaliveTick")]
  | ChordSystem.Request (dead, msg) ->
     `Assoc [ ("type", `String "Request")
            ; ("dead", json_of_addr dead)
            ; ("msg", json_of_msg msg)]

let show_id i =
  Digest.to_hex (VRUtil.string_of_char_list (id_to_ascii i))

let show_pointer p =
  show_id p.ChordIDSpace.ptrId

let show_pointer_list ps =
  let strs = map show_pointer ps in
  "[" ^ String.concat ", " strs ^ "]"

let show_addr a =
  VRUtil.string_of_char_list a

let caps_bool b =
  if b then "True" else "False"

let show_opt_pointer p =
  VRUtil.map_default show_pointer "None" p

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
  VRUtil.map_default show_request "None" st.ChordSystem.cur_request

let log_info_from st msg =
  let prefix = Printf.sprintf "node(%s):" (show_st_ptr st) in
  VRUtil.info (prefix ^ msg)

let log_dbg_from st msg =
  let prefix = Printf.sprintf "node(%s):" (show_st_ptr st) in
  VRUtil.debug (prefix ^ msg)

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
  type timeout = ChordSystem._timeout
  type res = state * (name * msg) list * (timeout list) * (timeout list)
  let port = chord_default_port
  let addr_of_name = VRUtil.string_of_char_list
  let name_of_addr = VRUtil.char_list_of_string
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
    let js =
      `Assoc [ ("update-state", `Assoc [(show_st_ptr st, json_of_st st)])
             ; ("deliver-message", json_of_recv st src msg)]
    in
    Printf.printf "%s ; %s\n" (string_of_float (Unix.gettimeofday ())) (to_string js);
    flush_all ()
  let debug_send st (dst, msg) =
    let js =
      `Assoc [ ("update-state", `Assoc [(show_st_ptr st, json_of_st st)])
             ; ("send-messages", `List [json_of_send st dst msg]) ]
    in
    Printf.printf "%s ; %s\n" (string_of_float (Unix.gettimeofday ())) (to_string js);
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
