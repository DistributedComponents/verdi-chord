Require Import Arith.
Require Import ExtrOcamlBasic.

Require Import Arith Even Div2 EqNat Euclid.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.

Require Import Chord.Chord.
Import Chord.Chord.Chord.

Extract Inlined Constant Chord.SUCC_LIST_LEN => "3".

(* We use the ocaml standard library implementation of MD5 to compute IDs. *)
Extract Constant Chord.hash => "Digest.of_string".
(* MD5 digests are 16 bytes. *)
Extract Inlined Constant Chord.N => "128".
(* Digest.compare returns -1 if a < b, 0 if a = b, and 1 if a > b *)
Extract Inlined Constant Chord.id_lt => "(fun a b -> Digest.compare a b < 0)".
(* id_eq_dec is axiomatized since the entire id type is *)
Extract Inlined Constant Chord.id_eq_dec => "(=)".

Definition handleNet : addr -> addr -> data -> payload -> res :=
  recv_handler.

Definition init : addr -> list addr -> data * list (addr * payload) * list timeout :=
  start_handler.

Definition handleTick : addr -> data -> res :=
  tick_handler.

Definition handleTimeout : addr -> data -> timeout -> res :=
  timeout_handler.

Extraction "extraction/chord/coq/ExtractedChord.ml" init handleNet handleTick handleTimeout is_request closes_request.
