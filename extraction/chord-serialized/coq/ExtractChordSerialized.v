Require Import Arith.
Require Import ExtrOcamlBasic.

Require Import Arith Even Div2 EqNat Euclid.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatInt.

Require Import Chord.Chord.
Require Import Chord.ChordSerialized.
Import ChordSerialized.

Require Import Cheerios.Cheerios.
Require Import Cheerios.ExtrOcamlCheeriosBasic.

Extract Inlined Constant Chord.SUCC_LIST_LEN => "3".

(* We use the ocaml standard library implementation of MD5 to compute IDs. Since
 * Coq extracts strings to the ocaml type char list, we have to wrap the hash in
 * a conversion function from verdi-runtime. *)
Extract Constant Chord.ocaml_hash =>
  "(fun s ->
     (Util.char_list_of_string
      (Digest.string
        (Util.string_of_char_list s))))".
(* MD5 digests are 16 bytes. *)
Extract Inlined Constant Chord.N => "16".

Extract Constant VectorEq.eqb => "(fun _ _ _ -> (=))".

Definition handleNet : addr -> addr -> data -> payload -> res :=
  ChordSerializedSystem.recv_handler.

Definition init : addr -> list addr -> data * list (addr * payload) * list timeout :=
  ChordSerializedSystem.start_handler.

Definition handleTimeout : addr -> data -> timeout -> res :=
  ChordSerializedSystem.timeout_handler.

(* for debugging *)
Definition deserializePayload w : option ChordSystem.payload :=
  deserialize_top deserialize w.

Extraction "extraction/chord-serialized/coq/ExtractedChordSerialized.ml"
           init
           handleNet
           handleTimeout
           deserializePayload

           is_request
           ascii_to_id
           id_to_ascii
           forge_pointer.