Require Import Arith.
Require FunctionalExtensionality.
Require Import List.
Import List.ListNotations.

Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Set Bullet Behavior "Strict Subproofs".

Require Import StructTact.StructTactics.
Require Import StructTact.Util.

Require Import Chord.Chord.
Require Import Chord.HandlerLemmas.

Definition live_node_bool (gst : global_state) (h : addr) : bool :=
  if sigma gst h is Some st then
    joined st && in_dec addr_eq_dec h (nodes gst) && ~~ in_dec addr_eq_dec h (failed_nodes gst)
  else false.

Ltac break_live_node_name var :=
  match goal with
  | H : live_node _ _ |- _ =>
    unfold live_node in H; repeat break_and; break_exists_name var; repeat break_and
  end.

Ltac break_live_node_exists_exists :=
  match goal with
  | H : live_node _ _ |- _ =>
    unfold live_node in H; repeat break_and; break_exists_exists; repeat break_and
  end.

Ltac break_dead_node :=
  match goal with
  | H : dead_node _ _ |- _ =>
    unfold dead_node in H; repeat break_and; break_exists; repeat break_and
  end.

Ltac break_dead_node_name var :=
  match goal with
  | H : dead_node _ _ |- _ =>
    unfold dead_node in H; repeat break_and; break_exists_name var; repeat break_and
  end.

Ltac break_dead_node_exists_exists :=
  match goal with
  | H : dead_node _ _ |- _ =>
    unfold dead_node in H; repeat break_and; break_exists_exists; repeat break_and
  end.

Ltac break_live_node :=
  match goal with
  | H : live_node _ _ |- _ =>
    unfold live_node in H; repeat break_and; break_exists; repeat break_and
  end.

Theorem live_node_characterization :
  forall gst h st,
    sigma gst h = Some st ->
    joined st = true ->
    In h (nodes gst) ->
    ~ In h (failed_nodes gst) ->
    live_node gst h.
Proof using.
  unfold live_node.
  intuition.
  match goal with
  | x : data |- exists _ : data, _ => exists x
  end.
  intuition.
Qed.

Definition live_addrs (gst : global_state) : list addr :=
  filter (live_node_bool gst) (nodes gst).

Definition live_ptrs (gst : global_state) : list pointer :=
  map make_pointer (live_addrs gst).

Definition live_ptrs_with_states (gst : global_state) : list (pointer * data) :=
  FilterMap.filterMap (fun p =>
                         match sigma gst (addr_of p) with
                         | Some st => Some (p, st)
                         | None => None
                         end)
                      (live_ptrs gst).

Theorem live_node_equiv_live_node_bool :
  forall gst h,
    live_node gst h <-> live_node_bool gst h = true.
Proof using.
  unfold live_node_bool.
  intuition.
  - repeat break_match; break_live_node; last by congruence.
    find_rewrite.
    find_injection.
    apply/andP; split; first by apply/andP; split => //; case in_dec.
    by case in_dec.
  - repeat break_match; last by congruence.
    move/andP: H => [H H_f]; move/andP: H => [H H_n].
    apply: live_node_characterization; eauto.
    * by move: H_n; case in_dec.
    * by move: H_f; case in_dec.
Qed.

Lemma live_addr_In_live_addrs :
  forall gst h,
    live_node gst h ->
    In h (live_addrs gst).
Proof.
  unfold live_addrs.
  intros.
  apply filter_In; split.
  - unfold live_node in *; break_and; auto.
  - apply live_node_equiv_live_node_bool; auto.
Qed.

Lemma In_live_addrs_live :
  forall gst h,
    In h (live_addrs gst) ->
    live_node gst h.
Proof.
  unfold live_addrs.
  intros.
  find_apply_lem_hyp filter_In; break_and.
  apply live_node_equiv_live_node_bool; auto.
Qed.

Lemma In_live_ptrs_live :
  forall gst h,
    In h (live_ptrs gst) ->
    live_node gst (addr_of h).
Proof.
  unfold live_ptrs.
  intros.
  apply In_live_addrs_live.
  now find_apply_lem_hyp in_map_iff; expand_def.
Qed.

Lemma when_apply_handler_result_preserves_live_node :
  forall h h0 st st' gst gst' e ms cts nts,
    live_node gst h ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    joined st' = true ->
    gst' = apply_handler_result h0 (st', ms, cts, nts) e gst ->
    live_node gst' h.
Proof using.
  intuition.
  eapply live_node_characterization.
  - eauto.
  - break_live_node.
    repeat find_rewrite.
    find_inversion; eauto.
  - find_apply_lem_hyp apply_handler_result_preserves_nodes.
    find_inversion.
    break_live_node; auto.
  - find_apply_lem_hyp apply_handler_result_preserves_failed_nodes.
    find_inversion.
    break_live_node; auto.
Qed.

Theorem live_node_preserved_by_recv_step :
  forall gst h src st msg gst' e st' ms nts cts,
    live_node gst h ->
    Some st = sigma gst h ->
    recv_handler src h st msg = (st', ms, nts, cts) ->
    gst' = apply_handler_result h (st', ms, nts, cts) e gst ->
    live_node gst' h.
Proof using.
  intuition.
  eapply when_apply_handler_result_preserves_live_node; eauto.
  - eauto using apply_handler_result_updates_sigma.
  - eapply joined_preserved_by_recv_handler.
    * eauto.
    * break_live_node.
      find_rewrite.
      find_injection.
      auto.
Qed.

Theorem live_node_preserved_by_timeout_step :
  forall gst h st st' t ms nts cts e gst',
    live_node gst h ->
    sigma gst h = Some st ->
    timeout_handler h st t = (st', ms, nts, cts) ->
    gst' = apply_handler_result h (st', ms, nts, t :: cts) e gst ->
    live_node gst' h.
Proof using.
  intuition.
  eapply when_apply_handler_result_preserves_live_node; eauto.
  - eauto using apply_handler_result_updates_sigma.
  - break_live_node.
    unfold timeout_handler, fst in *; break_let.
    repeat find_rewrite.
    find_apply_lem_hyp joined_preserved_by_timeout_handler_eff.
    repeat find_rewrite.
    find_injection.
    eauto.
Qed.

Definition best_succ_of (gst : global_state) (h : addr) : option addr :=
  match (sigma gst) h with
  | Some st => head (filter (live_node_bool gst) (map addr_of (succ_list st)))
  | None => None
  end.

Definition live_nodes_have_state (gst : global_state) : Prop :=
  forall h,
    In h (nodes gst) ->
    exists st,
      sigma gst h = Some st.

Theorem nodes_have_state :
  forall gst gst',
    live_nodes_have_state gst ->
    step_dynamic gst gst' ->
    live_nodes_have_state gst'.
Proof using.
  unfold live_nodes_have_state.
  move => gst gst' H_st H_step n H_in.
  break_step.
  - destruct (addr_eq_dec h n).
    + subst_max.
      apply update_for_start_sigma_h_exists.
    + find_rewrite_lem update_for_start_nodes_eq.
      find_apply_lem_hyp in_inv.
      break_or_hyp; try (exfalso; eauto; fail).
      find_apply_lem_hyp H_st.
      break_exists_exists.
      eapply update_for_start_sigma_h_n; eauto.
  - eauto.
  - destruct (addr_eq_dec h n).
    * eexists.
      now apply update_eq.
    * find_apply_lem_hyp H_st.
      break_exists_exists.
      find_reverse_rewrite.
      now apply update_diff.
  - (*simpl in *.*)
    destruct (addr_eq_dec (fst (snd m)) n).
    * eexists.
      now apply update_eq.
    * simpl.
      find_apply_lem_hyp H_st.
      break_exists_exists.
      repeat find_reverse_rewrite.
      now apply update_diff.
  - admit.
  - admit.
Admitted.

Lemma live_node_specificity :
  forall gst gst',
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst = sigma gst' ->
    live_node gst = live_node gst'.
Proof using.
  intuition.
  unfold live_node.
  repeat find_rewrite.
  auto.
Qed.

Lemma live_node_joined :
  forall gst h,
    live_node gst h ->
    exists st,
      sigma gst h = Some st /\
      joined st = true.
Proof using.
  intuition.
    by break_live_node_exists_exists.
Qed.

Lemma live_node_in_nodes :
  forall gst h,
    live_node gst h ->
    In h (nodes gst).
Proof using.
  intuition.
    by break_live_node.
Qed.

Lemma live_node_not_in_failed_nodes :
  forall gst h,
    live_node gst h ->
    ~ In h (failed_nodes gst).
Proof using.
  intuition.
    by break_live_node.
Qed.

Lemma live_node_equivalence :
  forall gst gst' h st st',
    live_node gst h ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    joined st = joined st' ->
    live_node gst' h.
Proof using.
  intuition.
  break_live_node.
  eapply live_node_characterization.
  * eauto.
  * repeat find_rewrite.
    find_injection.
    eauto.
  * repeat find_rewrite; auto.
  * repeat find_rewrite; auto.
Qed.

Lemma live_node_means_state_exists :
  forall gst h,
    live_node gst h ->
    exists st, sigma gst h = Some st.
Proof using.
  intuition.
  find_apply_lem_hyp live_node_joined.
  break_exists_exists.
    by break_and.
Qed.

Lemma coarse_live_node_characterization :
  forall gst gst' h,
    live_node gst h ->
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    sigma gst = sigma gst' ->
    live_node gst' h.
Proof using.
  intuition.
  find_copy_apply_lem_hyp live_node_means_state_exists.
  break_exists.
  eapply live_node_equivalence.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
  * repeat find_rewrite; eauto.
Qed.

Lemma adding_nodes_does_not_affect_live_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n (Some st) ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    live_node gst h ->
    live_node gst' h.
Proof using.
  intuition.
  break_live_node_name d.
  repeat split.
  * repeat find_rewrite.
    now apply in_cons.
  * by find_rewrite.
  * exists d.
    split => //.
    repeat find_reverse_rewrite.
    find_rewrite.
    find_rewrite.
    apply update_diff.
    congruence.
Qed.

(* reverse of the above, with additional hypothesis that h <> n. *)
Lemma adding_nodes_did_not_affect_live_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n st ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    live_node gst' h ->
    h <> n ->
    live_node gst h.
Proof using.
  intuition.
  unfold live_node.
  break_live_node_name d.
  repeat split.
  * repeat find_rewrite.
    find_apply_lem_hyp in_inv.
    break_or_hyp; congruence.
  * repeat find_rewrite.
    auto.
  * exists d.
    split => //.
    repeat find_reverse_rewrite.
    find_rewrite.
    find_rewrite.
    find_rewrite.
    find_rewrite.
    symmetry.
    apply update_diff; auto.
Qed.

Lemma adding_nodes_does_not_affect_dead_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n st ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    dead_node gst h ->
    dead_node gst' h.
Proof using.
  intuition.
  break_dead_node_name d.
  repeat split.
  - find_rewrite.
    eauto using in_cons.
  - find_rewrite; auto.
  - exists d.
    repeat find_reverse_rewrite.
    find_rewrite.
    find_rewrite.
    eapply update_diff.
    congruence.
Qed.


(* use lemma from Update.v instead *)
Lemma update_determined_by_f :
  forall A (f : addr -> A) x d d' y,
    y <> x ->
    update addr_eq_dec f x d y = d' ->
    f y = d'.
Proof using.
  intuition.
  symmetry.
  repeat find_reverse_rewrite.
  apply update_diff.
  now apply not_eq_sym.
Qed.

Lemma adding_nodes_did_not_affect_dead_node :
  forall gst gst' h n st,
    ~ In n (nodes gst) ->
    In h (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n st ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    dead_node gst' h ->
    dead_node gst h.
Proof using.
  intuition.
  break_dead_node_name d.
  unfold dead_node.
  repeat split.
  - find_rewrite.
    eauto using in_cons.
  - now repeat find_rewrite.
  - eexists.
    eapply update_determined_by_f.
    * instantiate (1 := n).
      eauto using In_notIn_implies_neq.
    * repeat find_rewrite; eauto.
Qed.

Lemma coarse_dead_node_characterization :
  forall gst gst' h,
    dead_node gst h ->
    sigma gst' = sigma gst ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    dead_node gst' h.
Proof using.
  intuition.
  break_dead_node_name d.
  repeat split; try (find_rewrite; auto).
  now exists d.
Qed.

Lemma coarse_best_succ_characterization :
  forall gst gst' h s,
    best_succ gst h s ->
    sigma gst' = sigma gst ->
    nodes gst' = nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    best_succ gst' h s.
Proof using.
  unfold best_succ in *.
  intuition.
  break_exists_exists.
  break_and.
  repeat break_and_goal.
  - eapply live_node_equivalence; eauto.
    now repeat find_rewrite.
  - now repeat find_rewrite.
  - easy.
  - move => o H_in.
    find_apply_hyp_hyp.
    eapply coarse_dead_node_characterization; eauto.
  - eapply coarse_live_node_characterization; eauto.
Qed.

Lemma adding_nodes_does_not_affect_best_succ :
  forall gst gst' h s n st,
    best_succ gst h s ->
    ~ In n (nodes gst) ->
    sigma gst' = update addr_eq_dec (sigma gst) n (Some st) ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    best_succ gst' h s.
Proof using.
  unfold best_succ.
  intuition.
  break_exists_exists.
  break_and.
  repeat break_and_goal;
    eauto using adding_nodes_does_not_affect_live_node.
  - repeat break_live_node.
    repeat find_rewrite.
    match goal with
    | H: sigma gst h = Some _ |- _ = Some _ => rewrite <- H
    end.
    eapply update_diff.
    congruence.
  - intuition.
    find_copy_apply_hyp_hyp.
    break_dead_node.
    eauto using adding_nodes_does_not_affect_dead_node.
Qed.

(*
Lemma in_half_means_in_whole :
  forall A (x : A) (xs ys : list A),
    In x xs -> In x (xs ++ ys).
Proof using.
  intuition.
Qed.

Lemma in_middle_means_in_whole :
  forall A (x : A) (xs ys : list A),
    In x (xs ++ x :: ys).
Proof using.
  intuition.
Qed.
*)

Lemma adding_nodes_did_not_affect_best_succ :
  forall gst gst' h s n st,
    best_succ gst' h s ->
    In h (nodes gst) ->
    ~ In n (nodes gst) ->
    sigma gst' h = Some st ->
    ~ In n (map addr_of (succ_list st)) ->
    sigma gst' = update addr_eq_dec (sigma gst) n (Some st) ->
    nodes gst' = n :: nodes gst ->
    failed_nodes gst' = failed_nodes gst ->
    best_succ gst h s.
Proof using.
  intuition.
  unfold best_succ in *.
  break_exists_exists.
  break_and.
  repeat break_and_goal.
  - break_live_node.
    break_live_node.
    unfold live_node.
    repeat find_rewrite.
    repeat break_and_goal; eauto.
    eexists; split; eauto.
Admitted.
(*

      break_exists.
      break_and.
      match goal with
        | H : sigma gst' ?h = Some ?st |- exists _, sigma gst ?h = _ /\ _ => exists st
      end.
      repeat find_rewrite.
      repeat find_injection.
      repeat split.
      * match goal with
        | H: sigma _ = update _ _ _ (Some ?st) |- sigma _ _ = Some ?st => symmetry in H
        end.
        eapply update_determined_by_f.
        + eapply In_notIn_implies_neq; eauto.
        + eauto.
      * eauto.
      * eauto.
      * eauto.
    - repeat find_reverse_rewrite.
      eapply update_determined_by_f;
        [eapply In_notIn_implies_neq; now eauto|]; now repeat find_rewrite.
    - eauto.
    - intuition.
      eapply adding_nodes_did_not_affect_dead_node; eauto.
      find_copy_apply_hyp_hyp.
      unfold dead_node in *.
      break_exists.
      break_and.
      repeat find_rewrite.
      find_injection.
      eapply In_cons_neq.
      * eauto.
      * intuition; subst.
        find_false.
        repeat find_rewrite.
        auto using in_half_means_in_whole.
    - eapply adding_nodes_did_not_affect_live_node; eauto.
      * intuition; subst.
        find_false.
        repeat (find_rewrite; try find_injection).
        auto using in_middle_means_in_whole.
  Qed.
 *)

Lemma global_state_eq_ext :
  forall gst gst',
    nodes gst = nodes gst' ->
    failed_nodes gst = failed_nodes gst' ->
    timeouts gst = timeouts gst' ->
    sigma gst = sigma gst' ->
    msgs gst = msgs gst' ->
    trace gst = trace gst' ->
    gst = gst'.
Proof using.
  intros.
  destruct gst, gst'.
  simpl in *.
  subst_max.
  tauto.
Qed.

Definition channel (gst : global_state) (src dst : addr) : list payload :=
  filterMap
    (fun m =>
       if (addr_eq_dec (fst m) src) && (addr_eq_dec (fst (snd m)) dst)
       then Some (snd (snd m))
       else None)
    (msgs gst).

(* note: this doesn't really tell you anything about repeated messages *)
Lemma channel_contents :
  forall gst src dst p,
    In (src, (dst, p)) (msgs gst) <-> In p (channel gst src dst).
Proof using.
  unfold channel.
  intuition.
  - eapply filterMap_In; eauto.
    by case addr_eq_dec, addr_eq_dec.
  - find_eapply_lem_hyp In_filterMap; eauto.
    break_exists.
    break_and.
    assert (x = (src, (dst, p))).
    { break_if; try discriminate.
      find_apply_lem_hyp Bool.andb_true_iff; break_and.
      repeat find_apply_lem_hyp addr_eqb_true.
      find_injection.
      move: H1 H2.
      case addr_eq_dec, addr_eq_dec => H_a H_a' //=.
      by destruct x, p; subst. }
    now find_reverse_rewrite.
Qed.
