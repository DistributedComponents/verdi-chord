open ExtractedChord
open ExtractedChord.ChordSystem
open ExtractedChord.ChordIDSpace

module type ClientSig = sig
  exception Wrong_response of string
  val lookup : string -> string -> id -> pointer
  val get_pred_and_succs : string -> string -> pointer option * pointer list
end

module Client : ClientSig = struct

  let connect_and_send me addr msg =
    let remote = Util.mk_addr_inet (addr, ChordArrangement.chord_default_port) in
    let self = Util.mk_addr_inet (me, 0) in
    let conn = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.setsockopt conn Unix.SO_REUSEADDR true;
    Unix.bind conn self;
    Unix.connect conn remote;
    let recv_chan = Unix.in_channel_of_descr conn in
    let send_chan = Unix.out_channel_of_descr conn in
    print_endline "connected successfully";
    output_value send_chan msg;
    flush send_chan;
    print_endline "sent message";
    send_chan, recv_chan, conn

  let debug_unix_error prefix errno fn arg =
    let err_msg = Unix.error_message errno in
    let full_msg = Printf.sprintf "in %s - %s(%s): %s" prefix fn arg err_msg in
    print_endline full_msg

  let query bind node p =
    let send_chan, recv_chan, conn = connect_and_send bind node p in
    let res = input_value recv_chan in
    Unix.shutdown conn Unix.SHUTDOWN_ALL;
    res

  exception Wrong_response of string

  let lookup bind node id =
    let p = forge_pointer id in
    match query bind node (GetBestPredecessor p) with
    | GotBestPredecessor p -> p
    | r -> raise (Wrong_response (ChordArrangement.show_msg r))

  let get_pred_and_succs bind node =
    match query bind node GetPredAndSuccs with
    | GotPredAndSuccs (p, ss) -> (p, ss)
    | r -> raise (Wrong_response (ChordArrangement.show_msg r))
end

let validate bind node query_type lookup_id =
  let handle_lookup b n =
    function
    | None -> invalid_arg "please specify an ID to look up"
    | Some id -> b, n, "lookup", id
  in
  match bind, node, query_type with
  | "", _, _ ->
     invalid_arg "please specify an IP to connect from with -bind"
  | b, Some n, "" ->
     invalid_arg "please specify a query type with -query"
  | b, Some n, "lookup" ->
     handle_lookup b n (Some lookup_id)
  | b, Some n, "get_ptrs" ->
     b, n, "get_ptrs", lookup_id
  | _, _, _ ->
     invalid_arg "please specify both -bind and -node"

let parse argv =
  let bind = ref "" in
  let node = ref None in
  let lookup_id = ref None in
  let query_type = ref "" in
  let set_query_type s = query_type := s in
  let spec =
    [ ChordUtil.ip_spec "-bind" bind "{ip} address to connect from"
    ; ChordUtil.addr_spec "-node" node "{ip:port} node to query"
    ; ( "-query"
      , Arg.Symbol (["lookup"; "get_ptrs"], set_query_type)
      , " type of query to run. lookup <ID> asks the node to look up the given ID. get_ptrs \
         asks the node for its predecessor and successors.")
    ]
  in
  let anonarg a =
    if !query_type = "lookup"
    then lookup_id := Some (ascii_to_id (Util.char_list_of_string a))
    else raise (Arg.Bad "not a lookup")
  in
  let usage = "USAGE:\n\
      client.native -bind {ip} -node {ip:port} -query [ lookup {id} | get_ptrs ]\n"
  in
  Arg.parse spec anonarg usage;
  try
    validate !bind !node !query_type !lookup_id
  with Invalid_argument msg ->
    let full_usage = msg ^ "\n\n" ^ usage in
    Arg.usage spec full_usage;
    exit 1

let _ =
  let bind, node, query_type, lookup_id = parse Sys.argv in
  match query_type, lookup_id with
  | "lookup", Some id ->
     let p = Client.lookup bind node id in
     print_endline (ChordArrangement.show_pointer p)
  | "get_ptrs", _->
     let p, succs = Client.get_pred_and_succs bind node in
     print_endline (ChordArrangement.show_opt_pointer p);
     print_endline (ChordArrangement.show_pointer_list succs)
  | _ ->
     print_endline "unknown query type";
     exit 1
