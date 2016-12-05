open Str
open Printf

let parse_addr s =
  match split (regexp ":") s with
  | addr::port::[] ->
     (* this will throw Invalid_argument if the ip is invalid... *)
     (Util.ip_of_int (Util.int_of_ip addr), int_of_string port)
  | _ -> invalid_arg s

let parse_addr_arg opt =
  try
    parse_addr opt
  with Invalid_argument _ ->
    let msg = (sprintf "invalid address '%s', should take the form ip:port" opt) in
    invalid_arg msg

let addrs_spec arg addrs_ref doc =
  let parse opt =
    addrs_ref := !addrs_ref @ [parse_addr_arg opt]
  in (arg, Arg.String parse, doc)

let addr_spec arg addr_ref doc =
  let parse opt =
    addr_ref := Some (parse_addr_arg opt)
  in (arg, Arg.String parse, doc)

type command_line_opts =
  { bind : (string * int) option ref
  ; pred : (string * int) option ref
  ; succs : (string * int) list ref
  ; known : (string * int) option ref
  ; debug : bool ref
  ; request_timeout : float ref
  ; tick_timeout : float ref
  ; keepalive_timeout : float ref
  }

let mk_default_opts () : command_line_opts =
  { bind = ref None
  ; pred = ref None
  ; succs = ref []
  ; known = ref None
  ; debug = ref true
  ; request_timeout = ref 30.0
  ; tick_timeout = ref 10.0
  ; keepalive_timeout = ref 5.0
  }

let mk_chord_config opts =
  if !(opts.keepalive_timeout) > !(opts.request_timeout)
  then invalid_arg "keepalive timeout must be greater than request timeout"
  else
    { ChordArrangement.tick_timeout = !(opts.tick_timeout)
    ; ChordArrangement.keepalive_timeout = !(opts.keepalive_timeout)
    ; ChordArrangement.request_timeout = !(opts.request_timeout)
    ; ChordArrangement.debug = !(opts.debug)
    }

let validate_nm_knowns opts =
  match !(opts.bind), !(opts.pred), !(opts.succs), !(opts.known) with
  | Some b, Some p, s :: uccs, None -> b, p :: s :: uccs
  | Some b, None, [], Some k -> b, [k]
  | Some b, None, [], None -> invalid_arg "please provide either -known or both -succ and -pred"
  | Some b, None, s :: uccs, None -> invalid_arg "please specify a predecessor with -pred"
  | Some b, Some p, [], None -> invalid_arg "please specify a successor list with -succ"
  | None, _, _, _ -> invalid_arg "please specify an address to bind to with -bind"
  | Some b, Some p, _, Some k -> invalid_arg "-known and -pred are mutually exclusive"
  | Some b, _, s :: uccs, Some k -> invalid_arg "-known and -succ are mutually exclusive"

let validate (opts : command_line_opts) =
  let cc = mk_chord_config opts in
  let nm, knowns = validate_nm_knowns opts in
  cc, nm, knowns

let parse argv opts =
  let spec =
    [ addr_spec "-bind" opts.bind "{ip:port} address to listen for connections on"
    ; addr_spec "-pred" opts.pred "{ip:port} node to start with as predecessor"
    ; addrs_spec "-succ" opts.succs "{ip:port} node to append to succ_list"
    ; addr_spec "-join" opts.known "{ip:port} node to join ring with"
    ; ( "-request-timeout"
      , Arg.Set_float opts.request_timeout
      , "minimum length of time to use for request timeouts"
      )
    ; ( "-tick-timeout"
      , Arg.Set_float opts.tick_timeout
      , "approximate time between ticks of the protocol"
      )
    ; ( "-keepalive-timeout"
      , Arg.Set_float opts.keepalive_timeout
      , "time between keepalive messages"
      )
    ; ( "-debug"
      , Arg.Set opts.debug
      , "run in debug mode"
      )
    ]
  in
  let anon_args_fun _ =
    let msg = sprintf "%s does not take position arguments" argv.(0) in
    raise (Arg.Bad msg)
  in
  try
    Arg.parse_argv argv spec anon_args_fun "Try -help for help or one of the following.";
    validate opts
  with
  | Invalid_argument msg ->
     Arg.usage spec msg;
     exit 1
  | Arg.Bad msg ->
     print_string msg;
     exit 1

let _ =
  let opts = mk_default_opts () in
  let cc, nm, knowns = parse Sys.argv opts in
  ChordArrangement.run cc nm knowns
