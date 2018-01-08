Require Import List.
Import ListNotations.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.

Lemma live_node_preserved_by_rectify :
  forall h,
    chord_rectify_invariant (fun gst => live_node gst h).
Proof.
  do 2 autounfold; intros.
  break_live_node.
  repeat handler_def;
    destruct (addr_eq_dec h h0);
    eapply live_node_characterization;
    repeat find_rewrite; rewrite_update; eauto; congruence.
Qed.
Hint Resolve live_node_preserved_by_rectify.

Lemma live_node_preserved_by_request :
  forall h,
    chord_request_invariant (fun gst => live_node gst h).
Proof.
  do 2 autounfold; intros.
  break_live_node.
  destruct (addr_eq_dec h h0);
    try solve [eapply live_node_characterization;
               repeat find_rewrite; rewrite_update; eauto; congruence].
  subst.
  eapply live_node_characterization;
    repeat find_rewrite; rewrite_update; simpl; eauto.
  find_injection.
  erewrite <- joined_preserved_by_request_timeout_handler; eauto.
Qed.
Hint Resolve live_node_preserved_by_request.

Lemma live_node_preserved_by_keepalive :
  forall h,
    chord_keepalive_invariant (fun gst => live_node gst h).
Proof.
  do 2 autounfold; intros.
  break_live_node.
  handler_def.
  destruct (addr_eq_dec h h0);
    eapply live_node_characterization;
    repeat find_rewrite; rewrite_update; eauto; congruence.
Qed.
Hint Resolve live_node_preserved_by_keepalive.

Lemma live_node_preserved_by_tick :
  forall h,
    chord_tick_invariant (fun gst => live_node gst h).
Proof.
  do 2 autounfold; intros.
  break_live_node.
  find_copy_apply_lem_hyp joined_preserved_by_tick_handler.
  destruct (addr_eq_dec h h0);
    eapply live_node_characterization;
    repeat find_rewrite; rewrite_update; eauto; congruence.
Qed.
Hint Resolve live_node_preserved_by_tick.

Lemma live_node_exists_after_simple_change :
  forall h src dst l succs gst gst' st st',
    live_node_in_msg_succ_lists gst ->
    (exists p, In (src, (dst, GotPredAndSuccs p succs)) l) \/ In (src, (dst, GotSuccList succs)) l ->
    (forall x, In x l -> In x (msgs gst)) ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst h = Some st ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st') ->
    joined st = joined st' ->
    length succs > 0 ->
    Exists (live_node gst') (map addr_of (chop_succs (make_pointer src :: succs))).
Proof.
  repeat (match goal with H: _ |- _ => clear H end).
  intros.
  assert (Exists (live_node gst) (map addr_of (chop_succs (make_pointer src :: succs))))
    by (repeat break_or_hyp; break_exists;
        eapply_prop live_node_in_msg_succ_lists; eauto).
  apply Exists_exists; find_apply_lem_hyp Exists_exists.
  break_exists_exists; split; break_and; auto.
  break_live_node.
  destruct (addr_eq_dec x h); subst;
    eapply live_node_characterization;
    repeat find_rewrite; rewrite_update; try find_injection; eauto.
  Unshelve. exact None.
Qed.

Lemma live_node_not_just_started :
  forall h gst gst' k st ms nts,
    ~ In h (nodes gst) ->
    In k (nodes gst) ->
    ~ In k (failed_nodes gst) ->
    start_handler h [k] = (st, ms, nts) ->
    nodes gst' = h :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' = update addr_eq_dec (timeouts gst) h nts ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st) ->
    msgs gst' = map (send h) ms ++ msgs gst ->
    trace gst' = trace gst ++ map e_send (map (send h) ms) ->
    forall l,
      live_node gst' l ->
      l <> h.
Proof.
  intros; intro; subst.
  assert (joined st = true).
  {
    inv_prop live_node; expand_def.
    repeat find_rewrite; rewrite_update; congruence.
  }
  assert (joined st = false) by
      eauto using joining_start_handler_st_joined.
  congruence.
Qed.

Lemma live_before_start_stays_live :
  forall h gst gst' k st ms nts,
    ~ In h (nodes gst) ->
    In k (nodes gst) ->
    ~ In k (failed_nodes gst) ->
    start_handler h [k] = (st, ms, nts) ->
    nodes gst' = h :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    timeouts gst' = update addr_eq_dec (timeouts gst) h nts ->
    sigma gst' = update addr_eq_dec (sigma gst) h (Some st) ->
    msgs gst' = map (send h) ms ++ msgs gst ->
    trace gst' = trace gst ++ map e_send (map (send h) ms) ->
    forall l,
      live_node gst l ->
      live_node gst' l.
Proof.
  intros.
  inv_prop live_node; expand_def.
  eapply live_node_characterization; eauto; repeat find_rewrite;
    solve [now rewrite_update | in_crush].
Qed.
