Require Import Arith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import Chord.Chord.

Definition SUCC_LIST_LEN := 3.

Definition hash (a : addr) : id :=
  a mod 256.

Extract Constant Nat.modulo => "fun n m -> n mod m".

Definition handleNet : addr -> addr -> data -> payload -> res :=
  recv_handler SUCC_LIST_LEN hash.

Definition init : addr -> list addr -> data * list (addr * payload) * list timeout :=
  start_handler SUCC_LIST_LEN hash.

Definition handleTick : addr -> data -> res :=
  tick_handler hash.

Definition handleTimeout : addr -> data -> timeout -> res :=
  timeout_handler hash.

Extraction "extraction/chord/coq/ExtractedChord.ml" init handleNet handleTick handleTimeout is_request closes_request.
