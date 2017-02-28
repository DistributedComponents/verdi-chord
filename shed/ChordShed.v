Require Import List.
Require Import mathcomp.ssreflect.ssreflect.
Require Import StructTact.StructTactics.
Require Import StructTact.Before.

Require Import Chord.Chord.
Import Chord.
Import Chord.ChordIDSpace.
Require Import Chord.ChordSemantics.
Import ConstrainedChord.
Require Import Chord.ChordLocalProps.
Require Import Chord.ChordProof.
Require Import Verdi.DynamicNet.
Require Import Shed.Shed.
Require Import Shed.DynamicShed.

Set Bullet Behavior "Strict Subproofs".

Module DecidableChord <: DecidableDynamicSystem.
  Include ConstrainedChord.

  Definition net := global_state.

  Definition request_response_pair_dec : forall p m,
      {request_response_pair p m} + {~ request_response_pair p m}.
  Proof using.
    intuition.
    destruct p;
      destruct m;
      try now (auto using pair_GetBestPredecessor, pair_GetSuccList, pair_GetPredAndSuccs, pair_Ping) ||
          (right; intro H_p; now inv H_p).
  Qed.

  Definition constraint_dec_helper :
    forall (l : list (addr * (addr * payload))) dst h p,
      (* parens here to avoid clashing w/ some ssreflect notation *)
      {(forall m, request_response_pair p m -> ~ In (dst, (h, m)) l)} +
      {~ (forall m, request_response_pair p m -> ~ In (dst, (h, m)) l)}.
  Proof using.
    intros.
    induction l.
    - left.
      easy.
    - destruct IHl.
      + destruct a as [from [to m]].
        destruct (request_response_pair_dec p m);
          destruct (addr_eq_dec dst from);
          destruct (addr_eq_dec h to);
          subst_max.
        { right.
          intro H_f.
          apply H_f in r.
          auto with datatypes. }
        { left.
          intuition.
          find_apply_lem_hyp in_inv.
          break_or_hyp.
          -- repeat tuple_inversion.
             auto.
          -- eapply n; eauto. }
        all: (left;
               intuition;
               find_apply_lem_hyp in_inv;
               break_or_hyp;
               try now (repeat tuple_inversion; auto);
               eapply n; eauto).
      + destruct a as [from [to m]].
        destruct (request_response_pair_dec p m);
          destruct (addr_eq_dec dst from);
          destruct (addr_eq_dec h to);
          subst_max.
        { right.
          intro H.
          eapply H; eauto with datatypes. }
        all: (right;
               intro H;
               apply n;
               intros m0 H_pair H_in;
               eapply H; eauto with datatypes).
  Defined.

  Definition timeout_constraint_dec : forall gst h t,
      {timeout_constraint gst h t} + {~ timeout_constraint gst h t}.
  Proof using.
    intros.
    destruct t.
    - left.
      apply Tick_unconstrained.
    - left.
      apply KeepaliveTick_unconstrained.
    - destruct (In_dec addr_eq_dec a (failed_nodes gst)).
      * assert ({(forall m, request_response_pair p m -> ~ In (a, (h, m)) (msgs gst))} + {~ (forall m, request_response_pair p m -> ~ In (a, (h, m)) (msgs gst))}) by apply constraint_dec_helper.
        destruct H.
        + left.
          eapply Request_needs_dst_dead_and_no_msgs; eauto.
        + right.
          intro H_t.
          inv H_t.
          easy.
      * right.
        intro H_t.
        inv H_t.
        easy.
  Defined.

  Definition all_nodes_live (gst : global_state) : Prop :=
    Forall (live_node gst) (nodes gst).

  Definition all_nodes_live_dec :
    forall gst,
      {all_nodes_live gst} + {~ all_nodes_live gst}.
  Proof using.
    move => gst.
    apply Forall_dec.
    exact: live_node_dec.
  Qed.

  Definition live_succ_exists_dec :
    forall gst l,
      {  (exists s xs ys, live_node gst s /\ l = xs ++ s :: ys /\ (forall o, In o xs -> dead_node gst o))} +
      {~ (exists s xs ys, live_node gst s /\ l = xs ++ s :: ys /\ (forall o, In o xs -> dead_node gst o))}.
  Admitted.

  Definition failure_constraint_helper :
    forall gst h st,
      sigma gst h = Some st ->
      {(exists s, best_succ gst h s)} + {~ exists s, best_succ gst h s}.
  Proof using.
    intros.
    unfold best_succ.
    set (addrs := map addr_of (succ_list st)).
    destruct (live_succ_exists_dec gst addrs);
      destruct (live_node_dec gst h).
    - left.
      break_exists_exists.
      exists st.
      break_exists_exists.
      intuition.
    - right.
      move => H_bs.
      break_exists.
      break_and.
      auto.
    - right.
      move => H_bs.
      apply n.
      break_exists_exists.
      break_exists_name st'.
      break_exists_exists.
      intuition.
      assert (st' = st).
        by (find_rewrite; find_inversion).
      subst.
      easy.
    - right.
      move => H_bs.
      break_exists.
      break_and.
      auto.
  Defined.

  Definition has_state (gst : global_state) (h : addr) : Prop :=
    exists st, sigma gst h = Some st.

  Definition has_state_dec :
    forall gst h,
      {has_state gst h} + {~has_state gst h}.
  Proof using.
    intuition.
    destruct (sigma gst h) as [st|] eqn:H_st.
    - left.
      now exists st.
    - right.
      move => H_hs.
      destruct H_hs.
      congruence.
  Defined.

  Definition live_node_in_succ_lists_dec : forall gst,
      {live_node_in_succ_lists gst} + {~ live_node_in_succ_lists gst}.
  Proof using.
    unfold live_node_in_succ_lists.
    move => gst.
    destruct (Forall_dec (live_node gst) (live_node_dec gst) (nodes gst)) as [H_st | H_st].
    - rewrite -> Forall_forall in H_st.
      assert (forall h, In h (nodes gst) -> {(exists s, best_succ gst h s)} + {~ exists s, best_succ gst h s}).
      { move => h H_node.
        set H_hl := H_st h H_node.
        apply live_node_means_state_exists in H_hl.
        destruct (sigma gst h) eqn:H_sig.
        + eapply failure_constraint_helper.
          repeat find_rewrite.
          eauto.
        + exfalso.
          break_exists.
          congruence. }
  Admitted.

End DecidableChord.

Module ChordShedSemantics := DynamicShedSemantics(DecidableChord).

Module ChordShed.
  Module ShedWithChord := Shed(ChordShedSemantics).
  Include ShedWithChord.
  Definition all_nodes_live_netpred : netpred :=
    {| np_prop := DecidableChord.all_nodes_live;
        np_dec := DecidableChord.all_nodes_live_dec;
        np_name := "all_nodes_live" |}.
End ChordShed.
