let connect_and_send me addr msg =
  let remote = Util.mk_addr_inet addr in
  let self = Util.mk_addr_inet me in
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

let read_and_unpack sock : ExtractedChord.payload =
  input_value sock

type req_params =
  { bind : string * int
  ; node : string * int
  ; msg : ExtractedChord.payload
  }

let request params =
  let send_chan, recv_chan, conn = connect_and_send params.bind params.node params.msg in
  let res = read_and_unpack recv_chan in
  Unix.shutdown conn Unix.SHUTDOWN_ALL;
  res

let mk_lookup id =
  ExtractedChord.GetBestPredecessor (id, id)

let mk_config bind node query_type lookup_id =
  match bind, node, query_type with
  | Some b, Some n, "" -> invalid_arg "please specify a query type with -query"
  | Some b, Some n, "lookup" ->
     { bind = b
     ; node = n
     ; msg = mk_lookup lookup_id
     }
  | Some b, Some n, "get_pred_and_succs" ->
     { bind = b
     ; node = n
     ; msg = ExtractedChord.GetPredAndSuccs
     }
  | _, _, _ -> invalid_arg "please specify both -bind and -node"

let parse argv =
  let bind = ref None in
  let node = ref None in
  let lookup_id = ref (-1) in
  let query_type = ref "" in
  let set_query_type s = query_type := s in
  let spec =
    [ ChordUtil.addr_spec "-bind" bind "{ip:port} address to connect from"
    ; ChordUtil.addr_spec "-node" node "{ip:port} node to query"
    ; ( "-query"
      , Arg.Symbol (["lookup"; "get_pred_and_succs"], set_query_type)
      , "type of query to run")
    ]
  in
  let anonarg a =
    if !query_type = "lookup"
    then lookup_id := int_of_string a
    else raise (Arg.Bad "not a lookup")
  in
  let usage = "-bind {ip:port} -node {ip:port} \
               [ -query lookup {id} | -query get_pred_and_succs ]"
  in
  Arg.parse spec anonarg usage;
  try
    mk_config !bind !node !query_type !lookup_id
  with Invalid_argument msg ->
    Arg.usage spec msg;
    exit 1

let _ =
  let params = parse Sys.argv in
  let res = request params in
  print_endline (ChordArrangement.show_msg res)
