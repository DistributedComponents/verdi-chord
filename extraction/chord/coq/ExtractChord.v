Require Import Arith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import Chord.Chord.
Import Chord.Chord.Chord.

Extract Inlined Constant Chord.SUCC_LIST_LEN => "3".
Extract Constant Chord.hash => "fun n -> n mod 256".

Definition handleNet : addr -> addr -> data -> payload -> res :=
  recv_handler.

Definition init : addr -> list addr -> data * list (addr * payload) * list timeout :=
  start_handler.

Definition handleTick : addr -> data -> res :=
  tick_handler.

Definition handleTimeout : addr -> data -> timeout -> res :=
  timeout_handler.

Extraction "extraction/chord/coq/ExtractedChord.ml" init handleNet handleTick handleTimeout is_request closes_request.
