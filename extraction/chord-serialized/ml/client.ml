open ExtractedChordSerialized
open ExtractedChordSerialized.ChordSerializedSystem
open ExtractedChordSerialized.ChordIDSpace

module type ClientSig = sig
  exception Wrong_response of string
  val lookup : string -> string -> id -> pointer
  val get_pred_and_succs : string -> string -> pointer option * pointer list
end

module Client : ClientSig = struct

  let setup_listen_fd listen_addr =
    let listen_fd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.setsockopt listen_fd Unix.SO_REUSEADDR true;
    Unix.bind listen_fd (Unix.ADDR_INET (listen_addr, ChordSerializedArrangement.chord_serialized_default_port));
    Unix.listen listen_fd 8;
    Unix.set_nonblock listen_fd;
    Printf.printf "[%s] started listening for connections" (Util.timestamp ());
    print_newline ();
    listen_fd

  let setup_write_fd write_addr listen_addr =
    let write_fd = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.setsockopt write_fd Unix.SO_REUSEADDR true;
    Unix.bind write_fd (Unix.ADDR_INET (listen_addr, 0));
    Unix.connect write_fd (Unix.ADDR_INET (write_addr, ChordSerializedArrangement.chord_serialized_default_port));
    Printf.printf "[%s] opened connection" (Util.timestamp ());
    print_newline ();
    write_fd

  let accept_read_fd listen_fd =
    Printf.printf "[%s] incoming connection" (Util.timestamp ());
    print_newline ();
    let (read_fd, read_addr) = Unix.accept listen_fd in
    Unix.set_nonblock read_fd;
    begin
      match read_addr with
      | Unix.ADDR_INET (addr, port) ->
        Printf.printf "[%s] done processing new connection from %s" (Util.timestamp ()) (Unix.string_of_inet_addr addr);
        print_newline ()
      | _ -> ()
    end;
    read_fd

  let rec eloop timeout listen_fd read_fds read_bufs =
    let select_fds = listen_fd :: read_fds in
    let (ready_fds, _, _) =
      Util.select_unintr select_fds [] [] timeout
    in
    let (new_fds, res) =
      List.fold_left
        (fun (fds, res) fd ->
          if fd = listen_fd then
            let read_fd = accept_read_fd fd in
            (read_fd :: fds, res)
          else begin
            Printf.printf "[%s] receiving data" (Util.timestamp ());
            print_newline ();
            match Util.recv_buf_chunk fd read_bufs with
            | None -> (fds, res)
            | Some buf -> (fds, Some buf)
          end) ([], None) ready_fds
    in
    match res with
    | None -> eloop timeout listen_fd (new_fds @ read_fds) read_bufs
    | Some m -> m

  let query listen_addr write_addr msg =
    let listen_fd = setup_listen_fd listen_addr in
    let write_fd = setup_write_fd write_addr listen_addr in
    let buf = serialize_top (payload_Serializer.serialize msg) in
    let read_bufs = Hashtbl.create 1 in
    Util.send_chunk write_fd buf;
    Printf.printf "[%s] sent message" (Util.timestamp ());
    print_newline ();
    let buf = eloop 1.0 listen_fd [] read_bufs in
    deserializePayload buf

  exception Wrong_response of string

  let lookup bind node id =
    let p = forge_pointer id in
    let listen_addr = Unix.inet_addr_of_string bind in
    let write_addr = Unix.inet_addr_of_string node in
    match query listen_addr write_addr (GetBestPredecessor p) with
    | Some (GotBestPredecessor p) -> p
    | Some r -> raise (Wrong_response (ChordSerializedArrangement.show_msg r))
    | None -> raise (Wrong_response "undeserializable")

  let get_pred_and_succs bind node =
    let listen_addr = Unix.inet_addr_of_string bind in
    let write_addr = Unix.inet_addr_of_string node in
    match query listen_addr write_addr GetPredAndSuccs with
    | Some (GotPredAndSuccs (p, ss)) -> (p, ss)
    | Some r -> raise (Wrong_response (ChordSerializedArrangement.show_msg r))
    | None -> raise (Wrong_response "undeserializable")

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
     print_endline (ChordSerializedArrangement.show_pointer p)
  | "get_ptrs", _->
     let p, succs = Client.get_pred_and_succs bind node in
     print_endline (ChordSerializedArrangement.show_opt_pointer p);
     print_endline (ChordSerializedArrangement.show_pointer_list succs)
  | _ ->
     print_endline "unknown query type";
     exit 1
