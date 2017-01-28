let parse_ip s =
  Util.ip_of_int (Util.int_of_ip s)

let parse_addr s =
  match Str.split (Str.regexp ":") s with
  | addr::port::[] ->
     (* this should throw invalid arg when this is broken *)
     (addr, int_of_string port)
  | _ -> invalid_arg s

let parse_addr_arg opt =
  try
    parse_addr opt
  with Invalid_argument _ ->
    let msg = (Printf.sprintf "invalid address '%s', should take the form ip:port" opt) in
    invalid_arg msg

let ip_spec arg addr_ref doc =
  let parse opt =
    addr_ref := parse_ip opt
  in (arg, Arg.String parse, doc)

let addr_spec arg addr_ref doc =
  let parse opt =
    addr_ref := Some (parse_addr_arg opt)
  in (arg, Arg.String parse, doc)

let addrs_spec arg addrs_ref doc =
  let parse opt =
    addrs_ref := !addrs_ref @ [parse_addr_arg opt]
  in (arg, Arg.String parse, doc)
