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

Definition pointers_in_payload (sender : addr) (m : payload) :=
  match m with
  | GotPredAndSuccs (Some s) succs =>
    make_pointer sender :: s :: succs
  | GotPredAndSuccs None succs => make_pointer sender :: succs
  | GotSuccList succs => make_pointer sender :: succs
  | GotBestPredecessor s => [make_pointer sender; s]
  | _ => []
  end.

Definition pointers_in_network gst :=
  flat_map (fun m => pointers_in_payload (fst m) (snd (snd m))) (msgs gst).

Definition option_to_list {A} (x : option A) :=
  match x with
  | None => []
  | Some a => [a]
  end.


Definition pointers_in_node_state st :=
  (option_to_list (pred st)) ++ (option_to_list (rectify_with st)) ++ succ_list st.

Definition pointers_in_state gst :=
  concat (filterMap (fun h => option_map pointers_in_node_state (sigma gst h)) (nodes gst))
         ++ pointers_in_network gst.

Definition concat_in :
  forall A (l : list A) l' a,
    In a l ->
    In l l' ->
    In a (concat l').
Proof.
  induction l'; in_crush.
Qed.

Definition in_succ_list_in_pointers_in_node_state :
  forall st p,
    In p (succ_list st) ->
    In p (pointers_in_node_state st).
Proof.
  intros. unfold pointers_in_node_state.
  in_crush.
Qed.

Lemma in_succ_list_in_pointers_in_state :
  forall gst h st p,
    In h (nodes gst) ->
    sigma gst h = Some st ->
    In p (succ_list st) ->
    In p (pointers_in_state gst).
Proof.
  intros. unfold pointers_in_state.
  find_apply_lem_hyp in_succ_list_in_pointers_in_node_state.
  in_crush. left.
  eapply concat_in; eauto.
  eapply filterMap_In; eauto.
  find_rewrite. reflexivity.
Qed.

Hint Resolve in_succ_list_in_pointers_in_state.

Definition pred_in_pointers_in_node_state :
  forall st p,
    pred st = Some p ->
    In p (pointers_in_node_state st).
Proof.
  intros. unfold pointers_in_node_state.
  find_rewrite.
  in_crush.
Qed.

Lemma pred_in_pointers_in_state :
  forall gst h st p,
    In h (nodes gst) ->
    sigma gst h = Some st ->
    pred st = Some p ->
    In p (pointers_in_state gst).
Proof.
  intros. unfold pointers_in_state.
  find_apply_lem_hyp pred_in_pointers_in_node_state.
  in_crush. left.
  eapply concat_in; eauto.
  eapply filterMap_In; eauto.
  find_rewrite. reflexivity.
Qed.

Hint Resolve pred_in_pointers_in_state.

Definition rectify_with_in_pointers_in_node_state :
  forall st p,
    rectify_with st = Some p ->
    In p (pointers_in_node_state st).
Proof.
  intros. unfold pointers_in_node_state.
  find_rewrite.
  in_crush.
Qed.

Lemma rectify_with_in_pointers_in_state :
  forall gst h st p,
    In h (nodes gst) ->
    sigma gst h = Some st ->
    rectify_with st = Some p ->
    In p (pointers_in_state gst).
Proof.
  intros. unfold pointers_in_state.
  find_apply_lem_hyp rectify_with_in_pointers_in_node_state.
  in_crush. left.
  eapply concat_in; eauto.
  eapply filterMap_In; eauto.
  find_rewrite. reflexivity.
Qed.

Hint Resolve rectify_with_in_pointers_in_state.

Lemma in_network_in_pointers_in_state :
  forall gst m p,
    In m (msgs gst) ->
    In p (pointers_in_payload (fst m) (snd (snd m))) ->
    In p (pointers_in_state gst).
Proof.
  intros. unfold pointers_in_state.
  in_crush. right. unfold pointers_in_network.
  apply in_flat_map. eauto.
Qed.

Hint Resolve in_network_in_pointers_in_state.

Lemma in_got_succ_list_in_pointers_in_state :
  forall gst m p l,
    In m (msgs gst) ->
    snd (snd m) = GotSuccList l ->
    In p l ->
    In p (pointers_in_state gst).
Proof.
  intros. unfold pointers_in_state. in_crush.
  right. unfold pointers_in_network. apply in_flat_map.
  exists m. intuition; repeat find_rewrite; simpl; auto.
Qed.

Hint Resolve in_got_succ_list_in_pointers_in_state.


Lemma sender_got_succ_list_in_pointers_in_state :
  forall gst m l,
    In m (msgs gst) ->
    snd (snd m) = GotSuccList l ->
    In (make_pointer (fst m)) (pointers_in_state gst).
Proof.
  intros. unfold pointers_in_state. in_crush.
  right. unfold pointers_in_network. apply in_flat_map.
  exists m. intuition; repeat find_rewrite; simpl; auto.
Qed.

Hint Resolve sender_got_succ_list_in_pointers_in_state.


Lemma in_got_best_pred_in_pointers_in_state :
  forall gst m p,
    In m (msgs gst) ->
    snd (snd m) = GotBestPredecessor p ->
    In p (pointers_in_state gst).
Proof.
  intros. unfold pointers_in_state. in_crush.
  right. unfold pointers_in_network. apply in_flat_map.
  exists m. intuition; repeat find_rewrite; simpl; auto.
Qed.

Hint Resolve in_got_best_pred_in_pointers_in_state.


Lemma sender_got_best_pred_in_pointers_in_state :
  forall gst m p,
    In m (msgs gst) ->
    snd (snd m) = GotBestPredecessor p ->
    In (make_pointer (fst m)) (pointers_in_state gst).
Proof.
  intros. unfold pointers_in_state. in_crush.
  right. unfold pointers_in_network. apply in_flat_map.
  exists m. intuition; repeat find_rewrite; simpl; auto.
Qed.

Hint Resolve sender_got_best_pred_in_pointers_in_state.


Lemma filterMap_in :
  forall A B (f : A -> option B) l x,
    In x (filterMap f l) ->
    exists y,
      In y l /\
      f y = Some x.
Proof.
  induction l; intros; in_crush.
  break_match; in_crush; eauto;
    eapply_prop_hyp @filterMap @filterMap;
    break_exists_exists; intuition.
Qed.

Lemma in_option_to_list :
  forall A (o : option A) x,
    In x (option_to_list o) ->
    o = Some x.
Proof.
  intros. unfold option_to_list in *.
  break_match; in_crush.
Qed.

Lemma pointers_in_state_elim :
  forall p gst,
    In p (pointers_in_state gst) ->
    (exists h st, In h (nodes gst) /\ sigma gst h = Some st /\ In p (succ_list st)) \/
    (exists h st, In h (nodes gst) /\ sigma gst h = Some st /\ pred st = Some p) \/
    (exists h st, In h (nodes gst) /\ sigma gst h = Some st /\ rectify_with st = Some p) \/
    (exists m, In m (msgs gst) /\ In p (pointers_in_payload (fst m) (snd (snd m)))).
Proof.
  intros. unfold pointers_in_state in *.
  in_crush.
  - find_apply_lem_hyp in_concat.
    break_exists. intuition.
    find_apply_lem_hyp filterMap_in.
    break_exists. intuition.
    find_apply_lem_hyp option_map_Some.
    break_exists.
    intuition.
    unfold pointers_in_node_state in *.
    subst. in_crush.
    + right. left. find_apply_lem_hyp in_option_to_list. eauto.
    + right. right. left. find_apply_lem_hyp in_option_to_list. eauto.
    + left. eauto.
  - repeat right.
    unfold pointers_in_network in *.
    find_apply_lem_hyp in_flat_map.
    eauto.
Qed.

Lemma check :
  forall gst p,
    In p (pointers_in_state gst) ->
    In p (pointers_in_state gst).
Proof.
  intros. find_apply_lem_hyp pointers_in_state_elim.
  intuition; break_exists; intuition eauto.
Qed.

Definition pointer_joined gst p :=
  In (addr_of p) (nodes gst) /\
  exists st,
    sigma gst (addr_of p) = Some st /\
    joined st = true.

Lemma pointer_joined_stable :
  forall gst gst' p,
    reachable_st gst ->
    step_dynamic gst gst' ->
    pointer_joined gst p ->
    pointer_joined gst' p.
Proof.
  intros. unfold pointer_joined in *. inv_prop step_dynamic; intuition.
  - unfold update_for_start. simpl. intuition.
  - unfold update_for_start. simpl. update_destruct; subst; rewrite_update; intuition.
  - break_exists. intuition.
    find_apply_lem_hyp timeout_handler_definition.
    break_exists.
    find_apply_lem_hyp joined_preserved_by_timeout_handler_eff.
    unfold apply_handler_result. simpl.
    update_destruct; subst; rewrite_update; intuition eauto.
    eexists; intuition eauto. congruence.
  - break_exists. intuition.
    unfold apply_handler_result. simpl.
    update_destruct; subst; rewrite_update; intuition eauto.
    find_apply_lem_hyp joined_preserved_by_recv_handler; eauto.
    congruence.
Qed.

Lemma find_pred_in :
  forall h p l,
    find_pred h l = Some p ->
    In p l.
Proof.
  induction l using List.rev_ind.
  - unfold find_pred. simpl. intuition. congruence.
  - unfold find_pred. simpl.
    rewrite rev_unit. simpl.
    in_crush. find_inversion. auto.
Qed.


Lemma in_make_succs :
  forall p s l,
    In p (make_succs s l) ->
    p = s \/ In p l.
Proof.
  unfold make_succs. intros.
  find_apply_lem_hyp in_firstn.
  in_crush.
Qed.

Lemma in_partition :
  forall A (l : list A) xs a ys,
    l = xs ++ a :: ys ->
    In a l.
Proof.
  intros. in_crush.
Qed.

Hint Resolve in_partition.

Theorem big_joined_invariant :
  forall gst p,
    reachable_st gst ->
    In p (pointers_in_state gst) ->
    pointer_joined gst p.
Proof.
  intros. induction H.
  - find_apply_lem_hyp pointers_in_state_elim;
    intuition; break_exists; intuition.
    + find_copy_apply_lem_hyp sigma_initial_st_start_handler; eauto.
      subst. unfold start_handler in *.
      repeat break_match; simpl in *; intuition.
      cut (In (addr_of p) (nodes gst)).
      { intros. find_apply_lem_hyp initial_nodes_live; eauto.
        unfold live_node in *. intuition. unfold pointer_joined; eauto.
      }
      cut (In p (sort_by_between x (map make_pointer (nodes gst)))).
      {
        intros.
        find_apply_lem_hyp in_sort_by_between.
        in_crush.
      }
      repeat find_rewrite.
      find_apply_lem_hyp in_firstn.
      in_crush.
    + find_copy_apply_lem_hyp sigma_initial_st_start_handler; eauto.
      subst. unfold start_handler in *.
      repeat break_match; simpl in *; intuition; try congruence.
      find_apply_lem_hyp find_pred_in.
      cut (In (addr_of p) (nodes gst)).
      { intros. find_apply_lem_hyp initial_nodes_live; eauto.
        unfold live_node in *. intuition. unfold pointer_joined; eauto.
      }
      cut (In p (sort_by_between x (map make_pointer (nodes gst)))).
      {
        intros.
        find_apply_lem_hyp in_sort_by_between.
        in_crush.
      }
      repeat find_rewrite. auto.
    + find_copy_apply_lem_hyp sigma_initial_st_start_handler; eauto.
      subst. unfold start_handler in *.
      repeat break_match; simpl in *; intuition; congruence.
    + unfold initial_st in *. intuition. repeat find_rewrite. in_crush.
  - assert (In p (pointers_in_state gst) -> pointer_joined gst' p) by
        eauto using pointer_joined_stable.
    inv_prop step_dynamic.
    + find_apply_lem_hyp pointers_in_state_elim.
      intuition; break_exists; intuition; simpl in *; eauto.
      * update_destruct; subst; rewrite_update; intuition; subst; eauto.
        find_inversion. simpl in *. intuition; congruence.
      * update_destruct; subst; rewrite_update; intuition; subst; eauto.
        find_inversion. simpl in *. intuition; congruence.
      * update_destruct; subst; rewrite_update; intuition; subst; eauto.
        find_inversion. simpl in *. intuition; congruence.
      * intuition; eauto.
        subst. simpl in *. intuition.
    + find_apply_lem_hyp pointers_in_state_elim.
      intuition; break_exists; intuition; simpl in *; eauto.
    + find_apply_lem_hyp pointers_in_state_elim.
      intuition; break_exists; intuition; simpl in *; eauto.
      * repeat (handler_def || handler_simpl);
          try solve [assert (In p (succ_list st)) by (repeat find_rewrite; in_crush); eauto].
      * repeat (handler_def || handler_simpl).
        admit (* need to add timeouts *).
      * repeat (handler_def || handler_simpl).
      * repeat (handler_def || handler_simpl);
          try solve [find_apply_lem_hyp option_map_Some; break_exists;
                     intuition; repeat find_inversion; eauto; subst; simpl in *; intuition];
          try solve [in_crush; eauto; unfold send_keepalives in *; in_crush].
        all:admit. (* sorry *)
    + find_apply_lem_hyp pointers_in_state_elim.
      intuition; break_exists; intuition; simpl in *; eauto.
      * repeat (handler_def || (try find_apply_lem_hyp in_make_succs; intuition) || handler_simpl);
          try solve [assert (In p (succ_list st)) by (repeat find_rewrite; in_crush); eauto];
          try solve [
                repeat find_rewrite; 
                in_crush; eauto;
                apply H2;
                eapply in_network_in_pointers_in_state with (m := m); eauto;
                repeat find_rewrite; in_crush].
        -- 
Admitted.
        
      
        (*
Theorem big_joined_invariant :
  forall gst,
    reachable_st gst ->
    all_payload_pointers_joined gst /\
    succs_joined gst /\
    pred_joined gst.
Proof.
  intros.
  induction H.
  - intuition.
    + unfold initial_st in *.
      unfold all_payload_pointers_joined. intuition.
      repeat find_rewrite. in_crush.
    + unfold succs_joined. intuition.
      find_copy_eapply_lem_hyp sigma_some_in_nodes; try solve [constructor; auto].
      find_copy_apply_lem_hyp sigma_initial_st_start_handler; auto.
      subst. unfold start_handler in *.
      repeat break_match; simpl in *; intuition.
      cut (In (addr_of p) (nodes gst)).
      { intros. find_apply_lem_hyp initial_nodes_live; eauto.
        unfold live_node in *. intuition.
      }
      cut (In p (sort_by_between h (map make_pointer (nodes gst)))).
      {
        intros.
        find_apply_lem_hyp in_sort_by_between.
        in_crush.
      }
      repeat find_rewrite.
      find_apply_lem_hyp in_firstn.
      in_crush.
    + unfold pred_joined. intuition.
      find_copy_eapply_lem_hyp sigma_some_in_nodes; try solve [constructor; auto].
      find_copy_apply_lem_hyp sigma_initial_st_start_handler; auto.
      subst. unfold start_handler in *.
      repeat break_match; simpl in *; intuition; try congruence.
      cut (In (addr_of p) (nodes gst)).
      { intros. find_apply_lem_hyp initial_nodes_live; eauto.
        unfold live_node in *. intuition.
      }
      cut (In p (sort_by_between h (map make_pointer (nodes gst)))).
      {
        intros.
        find_apply_lem_hyp in_sort_by_between.
        in_crush.
      }
      repeat find_rewrite.
      eauto using find_pred_in.
  - inv_prop step_dynamic; simpl in *; eauto.
    + intuition.
      * unfold all_payload_pointers_joined. simpl.
        intros. intuition; subst; simpl in *; intuition.
        update_destruct; subst; rewrite_update; eauto.
        exfalso.
        eapply_prop_hyp all_payload_pointers_joined pointers_in_payload; auto.
        break_exists. intuition.
        find_eapply_lem_hyp sigma_some_in_nodes; eauto.
      * unfold succs_joined. simpl. intuition.
        repeat (update_destruct; subst; rewrite_update; eauto).
        -- find_inversion. simpl in *. intuition.
        -- exfalso.
           eapply_prop_hyp succs_joined succ_list; eauto.
           break_exists. intuition.
           find_eapply_lem_hyp sigma_some_in_nodes; eauto.
        -- exfalso. find_inversion. simpl in *. intuition.
      * unfold pred_joined. simpl. intuition.
        repeat (update_destruct; subst; rewrite_update; eauto).
        -- find_inversion. simpl in *. congruence.
        -- exfalso.
           eapply_prop_hyp pred_joined pred; eauto.
           break_exists. intuition.
           find_eapply_lem_hyp sigma_some_in_nodes; eauto.
        -- exfalso. find_inversion. simpl in *. congruence.
    + intuition.
      * unfold all_payload_pointers_joined. intuition.
        simpl in *.
        repeat (handler_def || (handler_simpl; in_crush));
          try find_apply_lem_hyp option_map_Some;
          try solve
              [intuition; eauto;
               break_exists; intuition; find_inversion; simpl in *; intuition];
          try solve [unfold send_keepalives in *; in_crush];
          try solve [
                eapply_prop_hyp all_payload_pointers_joined pointers_in_payload; eauto;
                repeat find_rewrite; break_exists; intuition; repeat find_inversion; eauto].
      * unfold succs_joined. intuition. simpl in *.
        repeat (handler_def || (handler_simpl; in_crush));
          try find_apply_lem_hyp option_map_Some;
          try assert (In p (succ_list st)) by (repeat find_rewrite; in_crush);
          try solve [
                eapply_prop_hyp succs_joined succ_list; eauto;
                repeat find_rewrite; eauto; break_exists; intuition; repeat find_inversion; eauto].
      * unfold pred_joined. intuition. simpl in *.
        repeat (handler_def || (handler_simpl; in_crush));
          try find_apply_lem_hyp option_map_Some;
          try solve [
                eapply_prop_hyp pred_joined pred; eauto;
                repeat find_rewrite; eauto; break_exists; intuition; repeat find_inversion; eauto].
        assert (In p (succ_list st)) by (repeat find_rewrite; in_crush).
        -- eapply_prop_hyp succs_joined succ_list; eauto.
           repeat find_rewrite; eauto; break_exists; intuition; repeat find_inversion; eauto.
        -- eapply_prop_hyp all_payload_pointers_joined pointers_in_payload; eauto.
           repeat find_rewrite. break_exists. intuition; repeat find_inversion; eauto.
           eexists; intuition; simpl; eauto.
        eauto.
        eexists; intuition; eauto.
        eauto.
        eexists; intuition; eauto. simpl.
        eapply_prop_hyp all_payload_pointers_joined msgs; eauto.
        
        -- unfold send_keepalives in *. in_crush.
        
        -- eapply_prop all_payload_pointers_joined; eauto. in_crush.
*)        
(*
Theorem big_joined_invariant :
  forall gst,
    reachable_st gst ->
    all_payload_pointers_joined gst /\
    succs_joined gst.
Proof.
  intros.
  induction H.
  - intuition.
    + unfold initial_st in *.
      unfold all_payload_pointers_joined. intuition.
      repeat find_rewrite. in_crush.
    + unfold succs_joined. intuition.
      find_copy_eapply_lem_hyp sigma_some_in_nodes; try solve [constructor; auto].
      find_copy_apply_lem_hyp sigma_initial_st_start_handler; auto.
      subst. unfold start_handler in *.
      repeat break_match; simpl in *; intuition.
      cut (In (addr_of p) (nodes gst)).
      { intros. find_apply_lem_hyp initial_nodes_live; eauto.
        unfold live_node in *. intuition.
      }
      cut (In p (sort_by_between h (map make_pointer (nodes gst)))).
      {
        intros.
        find_apply_lem_hyp in_sort_by_between.
        in_crush.
      }
      repeat find_rewrite.
      find_apply_lem_hyp in_firstn.
      in_crush.
  - inv_prop step_dynamic; simpl in *; eauto.
    + intuition.
      * unfold all_payload_pointers_joined. simpl.
        intros. intuition; subst; simpl in *; intuition.
        update_destruct; subst; rewrite_update; eauto.
        exfalso.
        eapply_prop_hyp all_payload_pointers_joined pointers_in_payload; auto.
        break_exists. intuition.
        find_eapply_lem_hyp sigma_some_in_nodes; eauto.
      * unfold succs_joined. simpl. intuition.
        repeat (update_destruct; subst; rewrite_update; eauto).
        -- find_inversion. simpl in *. intuition.
        -- exfalso.
           eapply_prop_hyp succs_joined succ_list; eauto.
           break_exists. intuition.
           find_eapply_lem_hyp sigma_some_in_nodes; eauto.
        -- exfalso. find_inversion. simpl in *. intuition.
    + intuition.
      * unfold all_payload_pointers_joined. intuition.
        simpl in *.
        repeat (handler_def || (handler_simpl; in_crush));
          try find_apply_lem_hyp option_map_Some;
          try solve
              [intuition; eauto;
               break_exists; intuition; find_inversion; simpl in *; intuition];
          try solve [unfold send_keepalives in *; in_crush];
          try solve [
                eapply_prop_hyp all_payload_pointers_joined pointers_in_payload; eauto;
                repeat find_rewrite; break_exists; intuition; repeat find_inversion; eauto].
      * unfold succs_joined. intuition. simpl in *.
        repeat (handler_def || (handler_simpl; in_crush));
          try find_apply_lem_hyp option_map_Some;
          try assert (In p (succ_list st)) by (repeat find_rewrite; in_crush);
          try solve [
                eapply_prop_hyp succs_joined succ_list; eauto;
                repeat find_rewrite; eauto; break_exists; intuition; repeat find_inversion; eauto].
    + intuition.
      * unfold all_payload_pointers_joined. intuition. simpl in *.
        repeat (handler_def || (handler_simpl; in_crush)).
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
