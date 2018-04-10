Require Import List.
Import ListNotations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemPointers.
Require Import Chord.SuccessorNodesAlwaysValid.

Set Bullet Behavior "Strict Subproofs".

Theorem stabilize2_param_matches :
  forall gst,
    reachable_st gst ->
    forall h s s' st p,
      sigma gst h = Some st ->
      cur_request st = Some (s, Stabilize2 s', p) ->
      s = s'.
Proof.
  induction 1; intros.
  - unfold initial_st in *.
    find_apply_lem_hyp sigma_initial_st_start_handler; eauto.
    subst.
    unfold start_handler in *. repeat break_match; simpl in *; congruence.
  - inversion H0; subst; eauto.
    + subst. simpl in *.
      update_destruct; subst; rewrite_update; simpl in *; eauto.
      find_inversion. simpl in *. congruence.
    + simpl in *.
      update_destruct; subst; rewrite_update; simpl in *; eauto.
      repeat (handler_def || handler_simpl).
    + repeat (handler_def || handler_simpl;
              try (update_destruct; subst; rewrite_update);
              repeat find_rewrite;
              repeat find_inversion; simpl in *; eauto; try congruence).
Qed.

Theorem join2_param_matches :
  forall gst,
    reachable_st gst ->
    forall dst h st ns p,
      sigma gst h = Some st ->
      cur_request st = Some (dst, Join2 ns, p) ->
      dst = ns.
Proof.
  intros until 1. pattern gst.
  eapply chord_net_invariant; try assumption; clear H gst;
    do 2 autounfold; intros.
  - inv_prop initial_st; expand_def.
    destruct (In_dec addr_eq_dec h (nodes gst));
      [|find_apply_hyp_hyp; congruence].
    destruct (start_handler h (nodes gst)) as [[? ?] ?] eqn:?.
    copy_eapply_prop_hyp start_handler nodes; eauto; break_and.
    rewrite start_handler_init_state_preset in *;
      try (pose proof succ_list_len_lower_bound; omega).
    repeat (find_rewrite || find_injection).
    simpl in *; congruence.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      unfold start_handler in *; simpl in *; find_injection.
      simpl in *; congruence.
    + eauto.
  - repeat find_rewrite; eauto.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      repeat handler_def; simpl in *;
        solve [congruence
              |eauto
              |repeat find_rewrite; try find_injection; eauto].
    + eauto.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      repeat handler_def; simpl in *;
        solve [congruence
              |eauto
              |repeat find_rewrite; try find_injection; eauto].
    + eauto.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      repeat handler_def; simpl in *;
        solve [congruence
              |eauto
              |repeat find_rewrite; try find_injection; eauto].
    + eauto.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      repeat handler_def; simpl in *;
        solve [congruence
              |eauto
              |repeat find_rewrite; try find_injection; eauto].
    + eauto.
  - repeat find_rewrite; update_destruct; rewrite_update; subst.
    + find_injection.
      repeat handler_def;
        simpl in *;
        solve [congruence
              |eauto].
    + eauto.
  - repeat find_rewrite; eauto.
  - repeat find_rewrite; eauto.
Qed.

Lemma sigma_some_in_nodes :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    In h (nodes gst).
Proof.
  intros.
  induct_reachable_st; intros.
  - unfold initial_st in *.
    intuition.
    destruct (in_dec addr_eq_dec h (nodes gst)); auto.
    eapply_prop_hyp In In. congruence.
  - invcs H0; simpl in *; eauto;
      update_destruct; subst; rewrite_update; simpl in *; eauto.
Qed.

(*
Theorem succs_joined :
  forall gst,
    reachable_st gst ->
    forall h st s,
      sigma gst h = Some st ->
      In s (succ_list st) ->
      exists st__s,
        sigma gst (addr_of s) = Some st__s /\
        joined st__s = true.
Proof.
  induction 1; intros; simpl in *; eauto.
  - find_apply_lem_hyp initial_succ_list; auto; [|admit].
    repeat find_rewrite.
    admit.
  - inversion H0; subst; simpl in *; eauto.
    + update_destruct_hyp; subst; rewrite_update; simpl in *.
      * find_inversion. simpl in *. intuition.
      * update_destruct; subst; rewrite_update; simpl in *; eauto.
        exfalso. eapply_prop_hyp succ_list succ_list; eauto.
        break_exists. intuition.
        find_eapply_lem_hyp sigma_some_in_nodes; eauto.
    + repeat (handler_def || handler_simpl);
        try solve [eapply_prop_hyp succ_list succ_list; eauto; break_exists;
                   intuition; repeat find_rewrite; repeat find_inversion;
                   eexists; intuition eauto].
      * copy_eapply_prop_hyp sigma sigma; repeat find_rewrite; [|constructor 2; eauto].
        break_exists. intuition. repeat find_rewrite. find_inversion.
        eexists; intuition eauto.
      * copy_eapply_prop_hyp sigma sigma; repeat find_rewrite; [|constructor 2; eauto].
        break_exists. intuition. repeat find_rewrite.
        eexists; intuition eauto.
      * copy_eapply_prop_hyp sigma sigma; repeat find_rewrite; [|constructor 2; eauto].
        break_exists. intuition. repeat find_rewrite. find_inversion.
        eexists; intuition eauto.
      * copy_eapply_prop_hyp sigma sigma; repeat find_rewrite; [|constructor 2; eauto].
        break_exists. intuition. repeat find_rewrite.
        eexists; intuition eauto.
    + repeat (handler_def || handler_simpl);
        try solve [eapply_prop_hyp succ_list succ_list; eauto; break_exists;
                   intuition; repeat find_rewrite; repeat find_inversion;
                   eexists; intuition eauto].

Admitted.
*)

Theorem stabilize_target_joined :
  forall gst h st dst m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, Stabilize, m) ->
    exists st__d,
      sigma gst (addr_of dst) = Some st__d /\
      joined st__d = true.
Proof.
Admitted.

Theorem stabilize2_target_joined :
  forall gst h st dst sdst m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, Stabilize2 sdst, m) ->
    exists st__d,
      sigma gst (addr_of dst) = Some st__d /\
      joined st__d = true.
Proof.
Admitted.

Theorem join2_target_joined :
  forall gst h st dst jdst m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, Join2 jdst, m) ->
    exists st__d,
      sigma gst (addr_of dst) = Some st__d /\
      joined st__d = true.
Proof.
Admitted.

Theorem query_target_joined :
  forall gst h st dst q m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, q, m) ->
    exists st__d,
      sigma gst (addr_of dst) = Some st__d /\
      joined st__d = true.
Proof.
Admitted.

Theorem query_target_state_joined :
  forall gst h st dst q m,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dst, q, m) ->
    forall st__d,
      sigma gst (addr_of dst) = Some st__d ->
      joined st__d = true.
Proof.
  intros.
  eapply_lem_prop_hyp query_target_joined cur_request; eauto.
  break_exists; break_and; congruence.
Qed.

Lemma first_elem_in :
  forall A (P Q : A -> Prop) l,
    (forall y, In y l -> P y \/ Q y) ->
    (forall y, In y l -> Q y -> ~ P y) ->
    (forall y, In y l -> P y -> ~ Q y) ->
    forall x,
    In x l ->
    P x ->
    exists y xs ys,
      l = xs ++ y :: ys /\
      (forall z, In z xs -> Q z) /\
      P y.
Proof.
  induction l; intros; try solve_by_inversion.
  in_crush.
  - exists x. exists []. exists l. intuition.
    solve_by_inversion.
  - assert (P a \/ Q a); intuition.
    + exists a. exists []. exists l. intuition. solve_by_inversion.
    + repeat conclude_using in_crush.
      forward IHl; [firstorder|]. concludes.
      forward IHl; [firstorder|]. concludes.
      specialize (IHl x). intuition.
      break_exists_name y. exists y.
      break_exists_name xs. exists (a :: xs).
      break_exists_exists.
      intuition; simpl; try congruence.
      in_crush.
Qed.

Lemma live_node_not_dead_node :
  forall gst x,
    live_node gst x -> ~ dead_node gst x.
Proof.
  unfold live_node, dead_node. intuition.
Qed.

Lemma dead_node_not_live_node :
  forall gst x,
    dead_node gst x -> ~ live_node gst x.
Proof.
  unfold live_node, dead_node. intuition.
Qed.

Theorem live_node_in_succs_best_succ :
  forall gst h st l,
    reachable_st gst ->
    sigma gst h = Some st ->
    live_node gst l ->
    live_node gst h ->
    In l (map addr_of (succ_list st)) ->
    exists s, best_succ gst h s.
Proof.
  intros.
  pose proof (first_elem_in _ (live_node gst) (dead_node gst) (map addr_of (succ_list st))).
  forwards.
  {
    intros. 
    find_apply_lem_hyp in_map_iff.
    break_exists. intuition. subst.
    find_apply_lem_hyp successor_nodes_always_valid.
    eapply_prop_hyp successor_nodes_valid In; conclude_using eauto.
    intuition.
    unfold live_node, dead_node.
    destruct (in_dec addr_eq_dec (addr_of x) (failed_nodes gst)); intuition.
    right. intuition. 
    break_exists_exists. intuition.
  } repeat conclude_using ltac:(eauto using live_node_not_dead_node, dead_node_not_live_node).
  clear H5. eapply_prop_hyp In In; eauto.
  break_exists_exists.
  unfold best_succ. exists st. break_exists_exists.
  intuition.
Qed.
