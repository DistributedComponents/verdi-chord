Require Import Arith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Require Import Chord.Chord.
Require Import Shed.ChordShed.

Import Chord.Chord.Chord.

Extract Inlined Constant Chord.SUCC_LIST_LEN => "3".
Extract Constant Chord.hash => "fun n -> n mod 256".

Definition chord_net := ChordShed.ChordShed.net.
Definition chord_operation := ChordShed.ChordShed.operation.
Definition chord_run := ChordShed.ChordShed.run.
Definition chord_test_state := ChordShed.ChordShed.test_state.
Definition chord_advance_test := ChordShed.ChordShed.advance_test.
Definition chord_netpred := ChordShed.ChordShed.netpred.
Definition chord_tracepred := ChordShed.ChordShed.tracepred.
Definition chord_mk_init_state := ChordShed.ChordShed.make_initial_state.
Definition const_true_tracepred := ChordShed.ChordShed.tp_const_true.
Definition chord_plan_deliver_or_timeout := ChordShedSemantics.plan_deliver_or_timeout.
Definition all_nodes_live_netpred := ChordShed.all_nodes_live_netpred.

Extraction "extraction/chord/coq/ExtractedChordShed.ml" chord_net chord_operation chord_netpred chord_tracepred all_nodes_live_netpred const_true_tracepred chord_test_state chord_advance_test chord_mk_init_state chord_plan_deliver_or_timeout.