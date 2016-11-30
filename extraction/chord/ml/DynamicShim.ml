open Printf
open Sys
open Util

module M = Marshal

module type DYNAMIC_ARRANGEMENT = sig
  type name
  type state
  type msg
  type timeout
  type res = state * (name * msg) list * timeout list * timeout list
  val addr_of_name : name -> (string * int)
  val name_of_addr : (string * int) -> name
  val init : name -> name list -> state * (name * msg) list * timeout list
  val handleNet : name -> name -> state -> msg -> res
  val handleTimeout : name -> state -> timeout -> res
  val setTimeout : timeout -> float
  val default_timeout : float
  val debug : bool
  val debugRecv : state -> (name * msg) -> unit
  val debugSend : state -> (name * msg) -> unit
  val debugTimeout : state -> timeout -> unit
end
module Shim (A: DYNAMIC_ARRANGEMENT) = struct
  type env =
    { bound_ip : string
    ; bound_port : int
    ; listen_sock : Unix.file_descr
    ; recv_conns : (Unix.file_descr, A.name) Hashtbl.t
    ; send_conns : (A.name, Unix.file_descr) Hashtbl.t
    ; mutable last_tick : float
    }

  let bound_addr env =
    (env.bound_ip, env.bound_port)

  let debug_log s =
    if A.debug then print_endline s else ()

  let debug_timeout s' t =
    if A.debug
    then A.debugTimeout s' t

  let debug_recv st packet =
    if A.debug
    then A.debugRecv st packet

  let debug_send st packet =
    if A.debug
    then A.debugSend st packet

  let debug_unix_error prefix errno fn arg =
    let err_msg = Unix.error_message errno in
    let full_msg = sprintf "in %s - %s(%s): %s" prefix fn arg err_msg in
    debug_log full_msg

  let unpack_msg buf : A.msg =
    M.from_string buf 0

  let recv_fds env =
    keys_of_hashtbl (env.recv_conns)

  let readable_socks_in_env env =
    env.listen_sock :: keys_of_hashtbl env.recv_conns

  (* Create a socket listening at A.addr_of_name nm.
     Returns the ip address that the socket is bound to,
     or (TODO) a host ip if the address is 0.0.0.0. *)
  let mk_sock_and_listen nm =
    let ip, port = A.addr_of_name nm in
    let sa = mk_addr_inet (ip, port) in
    let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Unix.setsockopt sock Unix.SO_REUSEADDR true;
    Unix.bind sock sa;
    Unix.listen sock 20;
    ip, sock

  let setup nm =
    Hashtbl.randomize ();
    Random.self_init ();
    let ip, sock = mk_sock_and_listen nm in
    let ip, port = A.addr_of_name nm in
    { bound_ip = ip
    ; bound_port = port
    ; listen_sock = sock
    ; recv_conns = Hashtbl.create 64
    ; send_conns = Hashtbl.create 64
    ; last_tick = Unix.gettimeofday ()
    }

  let connect_to env remote =
    let sock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    let sa = mk_addr_inet_random_port env.bound_ip  in
    Unix.bind sock sa;
    Unix.connect sock (mk_addr_inet remote);
    sock

  let send_all sock buf =
    let rec send_chunk sock buf i l =
      let sent = Unix.send sock buf i l [] in
      if sent < l
      then send_chunk sock buf (i + sent) (l - sent)
      else () in
    send_chunk sock buf 0 (String.length buf)

  let rec find_conn_and_send_all env nm buf =
    if Hashtbl.mem env.send_conns nm
    then
      let conn = Hashtbl.find env.send_conns nm in
      try
        send_all conn buf;
      with Unix.Unix_error (errno, fn, arg) ->
        debug_unix_error "find_conn_and_send_all (found conn)" errno fn arg;
        (* close this connection and try again *)
        Hashtbl.remove env.send_conns nm;
        find_conn_and_send_all env nm buf
    else
      try
        let conn = connect_to env (A.addr_of_name nm) in
        send_all conn buf;
        Hashtbl.replace env.send_conns nm conn
      with Unix.Unix_error (errno, fn, arg) ->
        (* this should do something different if errno = EAGAIN, etc *)
        debug_unix_error "find_conn_and_send_all (made conn)" errno fn arg

  let respond_one env st (dst, msg) =
    debug_send st (dst, msg);
    let serialized = M.to_string msg [] in
    find_conn_and_send_all env dst serialized

  let filter_cleared clearedts ts =
    let not_cleared (_, t) = not (List.mem t clearedts) in
    List.filter not_cleared ts

  let add_times ts =
    let now = Unix.gettimeofday () in
    let add_time t = (now +. A.setTimeout t, t) in
    List.map add_time ts

  let respond env ts (s, ps, newts, clearedts) =
    let ts' = filter_cleared clearedts ts @ add_times newts in
    List.iter (respond_one env s) ps;
    s, ts'

  let ensure_conn_shutdown env nm =
    try
      Unix.shutdown (Hashtbl.find env.send_conns nm) Unix.SHUTDOWN_ALL
    with
    | Not_found -> ()
    | Unix.Unix_error (errno, fn, arg) ->
       debug_unix_error "ensure_conn_shutdown" errno fn arg

  let sockaddr_to_name =
    function
    | Unix.ADDR_UNIX _ -> failwith "UNEXPECTED MESSAGE FROM UNIX ADDR"
    | Unix.ADDR_INET (addr, port) -> A.name_of_addr (Unix.string_of_inet_addr addr, port)

  (* Read exactly len bytes from sock.
     Return (Some buf), where buf has length len, if everything works.
     Return None otherwise. *)
  let recv_len sock len =
    let rec aux sock acc len =
      let buf = String.make len '\x00' in
      let count = Unix.recv sock buf 0 len [] in
      let acc' = acc ^ buf in
      if count == 0
      then None
      else if count == len
      then Some acc'
      else aux sock acc' (len - count) in
    try
      aux sock "" len
    with Unix.Unix_error (errno, fn, arg) ->
      debug_unix_error "recv_len" errno fn arg;
      None

  let read_and_unpack sock : A.msg option =
    let read = recv_len sock in
    match read M.header_size with
    | None -> None
    | Some header ->
       let data_len = M.data_size header 0 in
       match read data_len with
       | Some body -> Some (unpack_msg (header ^ body))
       | None -> None

  let rec iterated_select rs t =
    try
      Unix.select rs [] [] t
    with Unix.Unix_error (errno, fn, arg) ->
      debug_unix_error "iterated_select" errno fn arg;
      iterated_select rs t

  let rec uniqappend l =
    function
    | [] -> l
    | h :: rest ->
       if List.mem h l
       then uniqappend l rest
       else uniqappend (l @ [h]) rest

  let do_timeout env nm (s, sends, newts, clearedts) (deadline, t) =
    if not (List.mem t clearedts)
    then
      let (s', sends', newts', clearedts') = A.handleTimeout nm s t in
      debug_timeout s' t;
      (s', sends @ sends', newts @ newts', uniqappend clearedts clearedts')
    else (s, sends, newts, clearedts)

  let timeout_step env nm s ts =
    let now = Unix.gettimeofday () in
    let active = List.filter (fun (deadline, _) -> now > deadline) ts in
    let do_t = do_timeout env nm in
    let res = (s, [], [], []) in
    let (s, sends, newts, clearedts) = List.fold_left do_t res active in
    let cts = uniqappend clearedts (List.map snd active) in
    respond env ts (s, sends, newts, cts)

  let min_of_list default l =
    List.fold_left (fun acc x -> min acc x) default l

  let free_time ts =
    let now = Unix.gettimeofday () in
    let min_deadline = min_of_list now (List.map fst ts) in
    max A.default_timeout (min_deadline -. now)

  let accept_connection env =
    let conn, sa = Unix.accept env.listen_sock in
    Hashtbl.add env.recv_conns conn (sockaddr_to_name sa)

  let send_connected_filter nm fd =
    try
      ignore (Unix.getpeername fd);
      Some fd
    with Unix.Unix_error (errno, fn, arg) ->
      debug_unix_error "send_connected_filter" errno fn arg;
      None

  let recv_connected_filter fd nm =
    try
      ignore (Unix.getpeername fd);
      Some nm
    with Unix.Unix_error (errno, fn, arg) ->
      debug_unix_error "recv_connected_filter" errno fn arg;
      None

  let prune_conns env =
    Hashtbl.filter_map_inplace recv_connected_filter env.recv_conns;
    Hashtbl.filter_map_inplace send_connected_filter env.send_conns

  let recv_step env nm s ts sock =
    match read_and_unpack sock with
    | Some m ->
       let src = Hashtbl.find env.recv_conns sock in
       let (s', ms, newts, clearedts) = A.handleNet src nm s m in
       debug_recv s' (src, m);
       respond env ts (s', ms, newts, clearedts)
    | None ->
       s, ts

  let handle_readable_fds env nm s ts fds =
    if List.length fds > 0
    then
      if List.mem env.listen_sock fds
      then (accept_connection env; s, ts)
      else recv_step env nm s ts (List.hd fds)
    else s, ts

  let rec eloop env nm (s, ts) =
    prune_conns env;
    let fds, _, _ = iterated_select (readable_socks_in_env env) (free_time ts) in
    let s', ts' = handle_readable_fds env nm s ts fds in
    let s'', ts'' = timeout_step env nm s' ts' in
    eloop env nm (s'', ts'')

  let init nm knowns =
    let (st, sends, nts) = A.init nm knowns in
    (st, sends, nts, [])

  let main nm knowns =
    let env = Unix.handle_unix_error setup nm in
    print_endline "starting";
    eloop env nm (respond env [] (init nm knowns));
end
