Require Import List.
Import ListNotations.

Require Import InfSeqExt.infseq.
Require Import StructTact.StructTactics.

Require Import Chord.Chord.
Import ChordIDSpace.
Require Import Chord.ChordProof.
Import ChordSemantics.
Import ConstrainedChord.
Require Import Chord.ChordValidPointersInvariant.

Definition nodes_have_live_succs (gst : global_state) : Prop :=
  forall h st,
    live_node gst h ->
    sigma gst h = Some st ->
    exists s,
      live_node gst (addr_of s) /\
      In s (succ_list st).

Theorem nodes_always_have_live_succs :
  forall gst,
    reachable_st gst ->
    nodes_have_live_succs gst.
Proof.
(*
In Zave's paper, this is one half of the inductive invariant. The
other half of the invariant is SufficientPrincipals. So it's provable,
but it will require coming up with an inductive invariant that works
for verdi-chord.

DIFFICULTY: 5
USED: below to prove node successor lists are nonempty, which is used
in phase one.
 *)
Admitted.

Definition circular_wait : occurrence -> Prop.
(* This is Ryan's problem. *)
Admitted.

Definition successor_nodes_valid (gst : global_state) : Prop :=
  forall h p st,
    In p (succ_list st) ->
    sigma gst h = Some st ->
    In (addr_of p) (nodes gst) /\
    exists pst, sigma gst (addr_of p) = Some pst /\
           joined pst = true.

Lemma wf_ptr_succ_list_invariant :
  forall gst h st p rest,
    reachable_st gst ->
    sigma gst h = Some st ->
    succ_list st = p :: rest ->
    wf_ptr p.
Proof.
(*
This invariant says pointers in successor lists are well-formed. It
should be inductive if we tack on something about the contents of
GotPredAndSuccs/GotSuccList messages.

DIFFICULTY: 3
USED: In phase one.
*)
Admitted.

Lemma wf_ptr_pred_invariant :
  forall gst h st p,
    reachable_st gst ->
    sigma gst h = Some st ->
    pred st = Some p ->
    wf_ptr p.
Proof.
(* 
This lemma says the same thing as wf_ptr_succ_list_invariant, but for
predecessor pointers instead of successor pointers.

DIFFICULTY: 3
USED: Nowhere? I think I could use it in phase two to lift some assumptions.
 *)
Admitted.

Lemma successor_nodes_always_valid :
  forall gst,
    reachable_st gst ->
    successor_nodes_valid gst.
Proof.
(*
This invariant says every successor list pointer points to a node
that's both live and has joined st = true.  It will require some
strengthening before it's inductive.
- Need to add somethine about the contents of GotPredAndSuccs messages
- Need to say nodes only end up in a sucessor list if they've joined

DIFFICULTY: 3
USED: In phase one.
*)
Admitted.

Lemma ptr_correct :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    ptr st = make_pointer h.
Proof.
(*
This is a very good and easy invariant.  At a node h, ptr st is a copy
of a pointer to h. It's set when the node starts up and never changed
anywhere.

DIFFICULTY: 1
USED: In phase two.
*)
Admitted.

Definition nonempty_succ_lists (gst : global_state) : Prop :=
  forall h st,
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    sigma gst h = Some st ->
    joined st = true ->
    succ_list st <> [].

Lemma nodes_have_nonempty_succ_lists :
  forall gst,
    reachable_st gst ->
    nonempty_succ_lists gst.
Proof.
  unfold nonempty_succ_lists.
  intros.
  find_apply_lem_hyp nodes_always_have_live_succs;
    eauto using live_node_characterization.
  break_exists.
  intro.
  repeat find_rewrite.
  intuition.
Qed.

Theorem stabilize_only_with_first_succ :
  forall gst h st dst,
    reachable_st gst ->
    sigma gst h = Some st ->
    In (Request dst GetPredAndSuccs) (timeouts gst h) ->
    exists s,
      addr_of s = dst /\
      cur_request st = Some (s, Stabilize, GetPredAndSuccs) /\
      hd_error (succ_list st) = Some s.
Proof.
  intros. eexists. repeat split.
(*
This lemma says that if we have an appropriate Request timeout, we
have all the other trappings of a Stabilize request. It's going to be
some work to prove because we have to show that
- whenever we register timeouts we also set the other stuff
- when the timeout isn't removed, the other stuff doesn't change

DIFFICULTY: 3
USED: In phase one.
*)
Admitted.

Theorem nodes_not_joined_have_no_successors :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    joined st = false ->
    succ_list st = [].
Proof.
(*
Nodes do not set their successor lists until they finish joining. I don't really
know what invariants are needed here but they shouldn't be too complicated?

DIFFICULTY: 2
USED: In phase one
*)
Admitted.

Definition busy_if_live (h : addr) (occ : occurrence) :=
  forall st,
    live_node (occ_gst occ) h ->
    sigma (occ_gst occ) h = Some st ->
    cur_request st <> None.

Definition not_busy_if_live (h : addr) (occ : occurrence) :=
  forall st,
    live_node (occ_gst occ) h ->
    sigma (occ_gst occ) h = Some st ->
    cur_request st = None.

(** the big assumption for inf_often stabilization *)
Theorem queries_eventually_stop :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    busy_if_live h (hd ex) ->
    always (~_ (now circular_wait)) ex ->
    eventually (now (not_busy_if_live h)) ex.
Proof.
(*
This is tricky.

  If you have an open request, you're in the middle of some operation.
  Operations (stabilization, rectifying, etc) undertaken by joined nodes complete
  in finitely many request-response pairs.
  A request eventually gets a response if there are no circular waits...

DIFFICULTY: Ryan
USED: In phase one for the proof of eventual stabilization.
*)
Admitted.

Theorem first_succ_never_self :
  forall gst h s,
    reachable_st gst ->
    has_first_succ gst h s ->
    h <> (addr_of s).
Proof.
(*
Easy consequence of the (difficult) Zave invariant.

DIFFCULTY: 1
USED: In phase two.
*)
Admitted.

Theorem pred_never_self :
  forall gst h p,
    reachable_st gst ->
    has_pred gst h (Some p) ->
    h <> (addr_of p).
Proof.
(*
Easy consequence of the (difficult) Zave invariant.

DIFFCULTY: 1
USED: In phase two.
*)
Admitted.

Lemma live_node_has_Tick_in_timeouts :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    live_node (occ_gst (hd ex)) h ->
    In Tick (timeouts (occ_gst (hd ex)) h).
Proof.
(*
New nodes have no Tick.
A node with no Tick sets joined = true iff it also registers a Tick.
Having a Tick is preserved by the step.
DIFFICULTY: 3
USED: In phase one.
*)
Admitted.
