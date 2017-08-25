Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.
Require Import StructTact.Util.

Require Import InfSeqExt.infseq.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.

Set Bullet Behavior "Strict Subproofs".

Lemma live_node_fail_node :
  forall h h' gst,
    live_node (fail_node gst h) h' ->
    live_node gst h'.
Proof.
  intros.
  unfold live_node in *. simpl in *.
  intuition.
Qed.
  
Ltac simpler := repeat (repeat find_inversion; subst; simpl in *; repeat rewrite_update); auto.

Lemma live_node_has_Tick_in_timeouts' :
  forall gst h,
    reachable_st gst ->
    live_node gst h ->
    In Tick (timeouts gst h).
Proof.
  intros. induct_reachable_st.
  - intros. unfold live_node in *.
    intuition. break_exists. intuition.
    find_copy_apply_lem_hyp sigma_initial_st_start_handler.
    assert (In h initial_nodes) by admit.
    find_apply_lem_hyp timeouts_initial_st_start_handler.
    break_exists.
    repeat find_rewrite.
    simpl in *.
    subst. unfold start_handler in *.
    repeat break_match; simpl in *; try discriminate.
    + subst. unfold empty_start_res in *. find_inversion.
      simpl in *. discriminate.
    + subst. find_inversion. simpl in *. discriminate.
    + find_inversion. rewrite_update. in_crush.
  - intros.
    inversion H0.
    + subst. simpl in *.
      unfold live_node in *. simpl in *.
      intuition.
      * subst. exfalso. rewrite_update.
        break_exists. intuition.
        solve_by_inversion.
      * assert (h <> h0) by
            (intro;
             subst; rewrite_update;
             break_exists; intuition; solve_by_inversion).
        repeat rewrite_update. auto.
    + subst. simpl in *. eauto using live_node_fail_node.
    + subst. simpl in *.
      update_destruct; subst;
        unfold live_node in *; simpl in *; repeat rewrite_update; auto.
      intuition. break_exists. intuition. find_inversion.
      assert (joined st = true -> In Tick (timeouts gst h)) by
          (intros; apply IHreachable_st; intuition; eauto).
      unfold timeout_handler, timeout_handler_eff in *.
      break_match.
      * unfold tick_handler in *.
        repeat (break_match; simpler).
        concludes.
        unfold add_tick in *. repeat break_let.
        subst. find_inversion. in_crush.
      * unfold do_rectify in *.
        repeat (break_match; simpler);
          try solve [apply remove_preserve; simpler; congruence].
        unfold start_query in *.
        break_match; simpler;
          try solve [apply remove_preserve; simpler; congruence].
        break_let. find_inversion.
        simpl in *. right.
        apply in_remove_all_preserve; 
          [unfold timeouts_in; repeat break_match; in_crush; congruence|].
        apply remove_preserve; simpler; congruence.
      * unfold keepalive_handler in *. simpl in *.
        find_inversion. simpl in *.
        right. apply remove_preserve; simpler; congruence.
      * unfold request_timeout_handler in *.
        repeat (break_match; simpler);
          try solve [apply remove_preserve; simpler; congruence].
        unfold handle_query_timeout in *.
 (*
New nodes have no Tick.
A node with no Tick sets joined = true iff it also registers a Tick.
Having a Tick is preserved by the step.
DIFFICULTY: 3
USED: In phase one.
*)

Admitted.


Lemma live_node_has_Tick_in_timeouts :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    live_node (occ_gst (hd ex)) h ->
    In Tick (timeouts (occ_gst (hd ex)) h).
Proof.
  eauto using live_node_has_Tick_in_timeouts'.
Qed.
