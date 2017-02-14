open Util

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


let raw_bytes_of_int (x : int) : bytes =
  let buf = Bytes.make 4 '\x00' in
  Bytes.set buf 0 (char_of_int (x land 0xff));
  Bytes.set buf 1 (char_of_int ((x lsr 8) land 0xff));
  Bytes.set buf 2 (char_of_int ((x lsr 16) land 0xff));
  Bytes.set buf 3 (char_of_int ((x lsr 24) land 0xff));
  buf

let int_of_raw_bytes (buf : bytes) : int =
  (int_of_char (Bytes.get buf 0)) lor
    ((int_of_char (Bytes.get buf 1)) lsl 8) lor
    ((int_of_char (Bytes.get buf 2)) lsl 16) lor
    ((int_of_char (Bytes.get buf 3)) lsl 24)

let char_list_of_string s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let string_of_char_list l =
  let res = String.create (List.length l) in
  let rec imp i = function
    | [] -> res
    | c :: l -> res.[i] <- c; imp (i + 1) l in
  imp 0 l

let mk_addr_inet (ip, port) =
  Unix.ADDR_INET (Unix.inet_addr_of_string ip, port)

let send_all sock buf =
  let rec send_chunk sock buf i l =
    let sent = Unix.send sock buf i l [] in
    if sent < l
    then send_chunk sock buf (i + sent) (l - sent)
    else () in
  send_chunk sock buf 0 (String.length buf)

let octets_to_ip o1 o2 o3 o4 =
  let so1 = Int32.shift_left o1 24 in
  let so2 = Int32.shift_left o2 16 in
  let so3 = Int32.shift_left o3 8 in
  Int32.logxor (Int32.logxor (Int32.logxor so1 so2) so3) o4

(* Matches four groups of at most three digits separated by dots *)
let weak_ip_regexp =
  Str.regexp "\\([0-9]?[0-9]?[0-9]\\)\\.\
              \\([0-9]?[0-9]?[0-9]\\)\\.\
              \\([0-9]?[0-9]?[0-9]\\)\\.\
              \\([0-9]?[0-9]?[0-9]\\)$"

(* Convert the string representation s of an ip, e.g., "10.14.122.04" to a
   32-bit integer.
   Throws Invalid_argument if s does not represent a valid IPv4 address. *)
let int_of_ip s =
  if Str.string_match weak_ip_regexp s 0
  then
    let int_of_kth_group k = Int32.of_string (Str.matched_group k s) in
    let numbers = List.map int_of_kth_group [1; 2; 3; 4] in
    match numbers with
    | [o1; o2; o3; o4] ->
       if List.for_all (fun x -> 0l <= x && x <= 255l) numbers
       then octets_to_ip o1 o2 o3 o4
       else invalid_arg s
    | _ -> invalid_arg s
  else invalid_arg s

(* Pull out the nth octet of the 32-bit integer i (where n = 0, 1, 2, or 3) *)

(* Convert a 32-bit integer to its dotted octet representation. *)
let ip_of_int i =
  let octet n =
    let n = 8 * n in
    let mask = Int32.shift_left 255l n in
    Int32.shift_right (Int32.logand mask i) n
  in
  let octets = List.map octet [0; 1; 2; 3] in
  String.concat "." (List.map Int32.to_string octets)

let parse_ip s =
  ip_of_int (int_of_ip s)

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
