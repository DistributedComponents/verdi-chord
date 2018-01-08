Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import StructTact.Update.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.
Require Import Chord.HandlerLemmas.
Require Import Chord.SystemLemmas.
Require Import Chord.QueryInvariant.

Set Bullet Behavior "Strict Subproofs".

Lemma timeouts_in_clear_rectify_with :
  forall st,
    timeouts_in (clear_rectify_with st) = timeouts_in st.
Proof.
  intuition.
Qed.

Theorem stabilize_only_with_first_succ :
  forall gst,
    reachable_st gst ->
    forall h st dst,
      sigma gst h = Some st ->
      In (Request dst GetPredAndSuccs) (timeouts gst h) ->
      exists s,
        addr_of s = dst /\
        cur_request st = Some (s, Stabilize, GetPredAndSuccs) /\
        hd_error (succ_list st) = Some s.
Proof.
  induction 1; intros.
  - exfalso.
    unfold initial_st in *. break_and.
    destruct (in_dec addr_eq_dec h (nodes gst)); intuition; [|find_apply_hyp_hyp; congruence].
    destruct (start_handler h (nodes gst)) as [[?st ?ms] ?nts] eqn:?.
    copy_eapply_prop_hyp start_handler start_handler; eauto; break_and.
    unfold start_handler in *.
    repeat break_match; simpl in *; repeat find_inversion; subst;
      try solve [repeat find_reverse_rewrite; in_crush; congruence].
    unfold empty_start_res in *. find_inversion. repeat find_reverse_rewrite; in_crush.
  - invcs H0; simpl in *; eauto.
    + update_destruct; subst; rewrite_update; simpl in *; eauto.
      find_inversion. intuition. congruence.
    + update_destruct; subst; rewrite_update; simpl in *; eauto.
      find_inversion.
      repeat (handler_def || handler_simpl);
        intuition; subst; try congruence;
          try solve [find_inversion; repeat find_rewrite; simpl in *; congruence];
          try solve [find_apply_lem_hyp in_remove; eauto];
          try solve [unfold hd_error in *; break_match; simpl in *; try solve_by_inversion;
                     repeat find_inversion; eauto];
          try solve [find_apply_lem_hyp in_remove_all_was_in;
                     find_apply_lem_hyp in_remove;
                     eapply_prop_hyp sigma sigma; eauto; break_exists; intuition; congruence];
          try solve [exfalso; find_apply_lem_hyp in_remove_all_was_in;
                     eapply at_most_one_request_timeout'_remove_drops_all; [| |eauto]; eauto;
                     find_eapply_lem_hyp at_most_one_request_timeout_invariant; eauto].
    + update_destruct; subst; rewrite_update; simpl in *; eauto.
      find_inversion.
      repeat (handler_def || handler_simpl);
        intuition; subst; try congruence; eauto;
        try solve [find_inversion; repeat find_rewrite; simpl in *; congruence];
          try solve [find_apply_lem_hyp in_remove; eauto];
          try solve [unfold hd_error in *; break_match; simpl in *; try solve_by_inversion;
                     repeat find_inversion; eauto];
          try solve [find_apply_lem_hyp in_remove_all_was_in;
                     find_apply_lem_hyp in_remove;
                     eapply_prop_hyp sigma sigma; eauto; break_exists; intuition; congruence];
          try solve [exfalso; find_apply_lem_hyp in_remove_all_was_in;
                     eapply at_most_one_request_timeout'_remove_drops_all; [| |eauto]; eauto;
                     find_eapply_lem_hyp at_most_one_request_timeout_invariant; eauto].
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
