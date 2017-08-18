open Printf
open Str
open ChordUtil

type command_line_opts =
  { bind : (string * int) option ref
  ; ring : (string * int) list ref
  ; known : (string * int) option ref
  ; debug : bool ref
  ; request_timeout : float ref
  ; tick_timeout : float ref
  ; keepalive_timeout : float ref
  }

let mk_default_opts () : command_line_opts =
  { bind = ref None
  ; ring = ref []
  ; known = ref None
  ; debug = ref true
  ; request_timeout = ref 10.0
  ; tick_timeout = ref 3.0
  ; keepalive_timeout = ref 3.0
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
  match !(opts.bind), !(opts.ring), !(opts.known) with
  | Some b, s :: uccs, None -> b, s :: uccs
  | Some b, [], Some k -> b, [k]
  | Some b, [], None -> invalid_arg "please provide either -known or an intial ring using -ring"
  | Some b, s :: uccs, Some k -> invalid_arg "-known and -ring are mutually exclusive"
  | None, _, _ -> invalid_arg "please specify an address to bind to using -bind"

let validate (opts : command_line_opts) =
  let cc = mk_chord_config opts in
  let nm, knowns = validate_nm_knowns opts in
  cc, nm, knowns

let parse argv opts =
  let spec =
    [ addr_spec "-bind" opts.bind "{ip:port} address to listen for connections on"
    ; addrs_spec "-ring" opts.ring "{ip:port} node in initial ring"
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
