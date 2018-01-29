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

Theorem live_node_in_succs_best_succ :
  forall gst h st l,
    reachable_st gst ->
    sigma gst h = Some st ->
    live_node gst l ->
    In l (map addr_of (succ_list st)) ->
    exists s, best_succ gst h s.
Proof.
  
  intros.
Admitted.
