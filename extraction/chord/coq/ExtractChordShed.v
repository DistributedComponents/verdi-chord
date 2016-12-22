Require Import Arith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import Shed.ChordShed.

Definition SUCC_LIST_LEN := 3.

Definition hash (a : addr) : id :=
  a mod 256.

Extract Constant Nat.modulo => "fun n m -> n mod m".

Definition chord_net := net.
Definition chord_operation := operation.
Definition chord_run := run SUCC_LIST_LEN hash.
Definition chord_test_state := test_state SUCC_LIST_LEN hash.
Definition chord_advance_test := advance_test SUCC_LIST_LEN hash.
Definition chord_netpred := netpred.
Definition chord_tracepred := tracepred SUCC_LIST_LEN hash.
Definition chord_mk_init_state := mk_init_state SUCC_LIST_LEN hash.
Definition const_true_tracepred := tp_const_true SUCC_LIST_LEN hash.
Definition chord_plan_deliver_or_timeout := plan_deliver_or_timeout SUCC_LIST_LEN hash.

Extraction "extraction/chord/coq/ExtractedChordShed.ml" chord_net chord_operation chord_netpred chord_tracepred all_nodes_live_netpred const_true_tracepred chord_test_state chord_advance_test chord_mk_init_state chord_plan_deliver_or_timeout.