Require Import List.
Import ListNotations.
Require Import Relations.
Require Import Omega.

Require Import StructTact.StructTactics.
Require Import StructTact.Update.
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.
Require Import Chord.InfSeqTactics.

Require Import Chord.Chord.

Require Import Chord.HandlerLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.
Require Import Chord.LabeledLemmas.
Require Import Chord.LiveNodesNotClients.
Require Import Chord.QueryInvariant.

Set Bullet Behavior "Strict Subproofs".

(* The (blocked_by s h) relation relates a live node h to a node s when
   a message from h is stored in the delayed_queries list at s. *)
Definition blocked_by (gst : global_state) (s h : addr) : Prop :=
  In h (nodes gst) /\
  In s (nodes gst) /\
  exists st__h st__s dstp q m,
    sigma gst h = Some st__h /\
    sigma gst s = Some st__s /\
    cur_request st__h = Some (dstp, q, m) /\
    addr_of dstp = s /\
    In (h, m) (delayed_queries st__s).

(* There is a cycle in a relation iff there's an element related to
   itself by the transitive closure of the relation. *)
Definition has_cycle {A : Type} (R : A -> A -> Prop) : Prop :=
  exists x,
    clos_trans_1n A R x x.

(* A circular wait (in a given state) is a cycle in the blocked_by
   relation (for that state). *)
Definition circular_wait (occ : occurrence) : Prop :=
  has_cycle (blocked_by (occ_gst occ)).

Inductive fin_chain {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
| FinChainNil : fin_chain R []
| FinChainOne : forall x, fin_chain R [x]
| FinChainCons : forall x y l,
    R x y ->
    fin_chain R (y :: l) ->
    fin_chain R (x :: y :: l).
Hint Constructors fin_chain.

Theorem pigeon_cycle :
  forall A (R : A -> A -> Prop) l,
    (forall a b, R a b -> In a l /\ In b l) ->
    forall c,
    fin_chain R c ->
    length c > length l ->
    has_cycle R.
Proof.
(* not sure I need this machinery yet *)
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

Lemma now_const :
  forall T (P : T -> Prop),
    (forall t, P t) ->
    forall ex,
      (now P) ex.
Proof.
  destruct ex.
  simpl; auto.
Qed.
Hint Resolve now_const.

Lemma always_const :
  forall T (P : infseq T -> Prop),
    (forall s, P s) ->
    forall ex,
      always P ex.
Proof.
  intros.
  eapply always_monotonic; [|eapply always_true].
  auto.
Qed.
Hint Resolve always_const.

Theorem joined_nodes_never_run_join :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    joined st = true ->
    forall dst q m k,
      cur_request st = Some (dst, q, m) ->
      q <> Join k.
Proof.
Admitted.

Lemma continuously_false_false :
  forall T (s : infseq T),
    continuously (fun _ => False) s ->
    False.
Proof.
  intros.
  induction 0 as [[o s] ?|o s];
    now inv_prop always.
Qed.

Theorem never_stuck_on_non_stabilize_with_res_on_wire :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall dstp q m res,
      q <> Stabilize ->
      query_response q res ->
      In res (channel (occ_gst (hd ex)) (addr_of dstp) h) ->
      always (now
                (fun o =>
                   forall st,
                     sigma (occ_gst o) h = Some st ->
                     cur_request st = Some (dstp, q, m)))
             ex ->
      False.
Proof.
  intros.
  cut (continuously (fun _ => False) ex);
    [eauto using continuously_false_false|].
  find_copy_apply_lem_hyp live_node_means_state_exists;
    break_exists_name st__h.
  find_apply_lem_hyp in_channel_in_msgs.
  find_eapply_lem_hyp RecvMsg_eventually_occurred;
    eauto using strong_local_fairness_weak.
  match goal with
  | H: In _ (msgs _) |- _ => clear H
  end.
  induction 0.
  - destruct s as [o [o' [o'' s]]]; simpl in *.
    break_and; do 2 invcs_prop lb_execution.
    assert (exists st, sigma (occ_gst o') h = Some st /\ cur_request st = None).
    {
      unfold occurred in *; repeat find_reverse_rewrite.
      inv_prop (labeled_step_dynamic (occ_gst o)); clean_up_labeled_step_cases.
      recover_msg_from_recv_step_equality.
      subst; simpl in *.
      find_apply_lem_hyp always_now'; simpl in * |-.
      repeat find_rewrite; simpl in *.
      eexists; rewrite_update; split; eauto.
      eapply recv_handler_response_clears_cur_request_q_single;
        try eapply recv_handler_labeling; eauto.
      intros.
      eapply joined_nodes_never_run_join; invar_eauto.
      inv_prop live_node; expand_def; congruence.
    }
    break_exists; expand_def.
    find_apply_lem_hyp always_invar; find_apply_lem_hyp always_now'; simpl in *.
    repeat find_rewrite.
    assert (cur_request x = Some (dstp, q, m)) by eauto.
    congruence.
  - eapply E_next, IHeventually; invar_eauto.
Qed.

Theorem stuck_on_a_single_query_means_blocked :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall dstp q m,
      always (now
                (fun o =>
                   forall st,
                     sigma (occ_gst o) h = Some st ->
                     cur_request st = Some (dstp, q, m)))
             ex ->
      continuously (now (fun o => blocked_by (occ_gst o) (addr_of dstp) h)) ex.
Proof.
Admitted.

Lemma blocking_node_continuously_also_blocked :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    forall h s,
      always (now (fun o => blocked_by (occ_gst o) s h)) ex ->
      exists w,
        continuously (now (fun o => blocked_by (occ_gst o) w s)) ex.
Proof.
Admitted.

Lemma now_and_tl_comm :
  forall T (P Q : T -> Prop) s,
    (now P /\_ now Q) s = now (fun o => P o /\ Q o) s.
Proof.
  intros.
  destruct s.
  reflexivity.
Qed.
Hint Rewrite now_and_tl_comm.

Theorem query_always_stuck_gives_chain :
  forall k ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    always (~_ (now circular_wait)) ex ->
    forall dstp q m,
      always (now (fun o => forall st,
                       sigma (occ_gst o) h = Some st ->
                       cur_request st = Some (dstp, q, m)))
           ex ->
      k >= 1 ->
      exists c,
        length c = k /\
        In h c /\
        continuously
          (now (fun occ => fin_chain (blocked_by (occ_gst occ)) c)) ex.
Proof.
  induction k as [|[|?]]; intros.
  - omega.
  - exists [h]; intuition.
    constructor; eauto.
  - find_copy_eapply_lem_hyp IHk; eauto; [|omega].
    break_exists_name c; intuition.
    induction H9; intros; subst.
    + destruct c as [|w [|w' c]];
        [simpl in * |-; tauto| |].
      * assert (w = h) by (simpl in *; tauto); subst.
        exists [addr_of dstp; h]; intuition.
        simpl in *; congruence.
        find_copy_eapply_lem_hyp stuck_on_a_single_query_means_blocked; eauto.
        find_apply_lem_hyp always_continuously.
        find_continuously_and_tl.
        eapply continuously_monotonic; try eassumption.
        intro s0; rewrite now_and_tl_comm.
        apply now_monotonic; intuition eauto.
      * assert (always (now (fun o => blocked_by (occ_gst o) w w')) s).
        {
          eapply always_monotonic;
            [eapply now_monotonic|eassumption].
          intros; now inv_prop @fin_chain.
        }
        find_eapply_lem_hyp blocking_node_continuously_also_blocked; eauto.
        break_exists_name w0.
        exists (w0 :: w :: w' :: c).
        intuition; simpl in *; try omega.
        find_apply_lem_hyp always_continuously.
        find_continuously_and_tl.
        eapply continuously_monotonic; try eassumption.
        intro s0; rewrite now_and_tl_comm.
        apply now_monotonic; intuition eauto.
    + assert (exists c : list addr,
                 length c = S (S n) /\
                 In h c /\
                 continuously (now (fun occ => fin_chain (blocked_by (occ_gst occ)) c)) s)
        by (eapply IHeventually; invar_eauto).
      break_exists_exists; intuition.
      constructor; now auto.
Qed.

Theorem never_stopping_means_stuck_on_a_single_query :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall st dstp q m,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      always (~_ (now circular_wait)) ex ->
      always (now (fun o => forall st',
                           sigma (occ_gst o) h = Some st' ->
                           cur_request st' <> None)) ex ->
      exists dstp' q' m',
        continuously (now (fun o =>
                             forall st',
                               sigma (occ_gst o) h = Some st' ->
                               cur_request st' = Some (dstp', q', m')))
                     ex.
Proof.
Admitted.

Theorem queries_dont_always_not_stop :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall st dstp q m,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      always (~_ (now circular_wait)) ex ->
      ~ always (now (fun o => forall st',
                         sigma (occ_gst o) h = Some st' ->
                         cur_request st' <> None)) ex.
Proof.
  intuition.
  cut (eventually (now circular_wait) ex).
  {
    intros.
    clear H3.
    induction H7.
    -  repeat find_apply_lem_hyp always_now'.
       unfold not_tl in *.
       destruct s; auto.
    - apply IHeventually; invar_eauto.
  }
  find_eapply_lem_hyp never_stopping_means_stuck_on_a_single_query; eauto; break_exists.
  match goal with
  | H: sigma _ h = Some _ |- _ => clear H
  end.
  match goal with
  | H: continuously _ _ |- _ => induction H
  end.
  - remember (length (nodes (occ_gst (hd s)))) as k.
    find_eapply_lem_hyp (query_always_stuck_gives_chain (S k)); omega || eauto.
    break_exists; break_and.
    match goal with
    | H: continuously _ _ |- _ => induction H
    end.
    + destruct s; apply E0.
      find_apply_lem_hyp always_now'; simpl in *.
      eapply pigeon_cycle with (l := nodes (occ_gst o));
        [|eassumption|omega].
      intros; inv_prop blocked_by; tauto.
    + eapply E_next, IHeventually; invar_eauto.
      inv_prop lb_execution.
      inv_prop labeled_step_dynamic;
        simpl;
        repeat (find_rewrite || find_injection);
        auto using apply_handler_result_nodes.
  - eapply E_next, IHeventually; invar_eauto.
Qed.

Theorem queries_eventually_stop' :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    strong_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall st dstp q m,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      always (~_ (now circular_wait)) ex ->
      eventually (now (fun o => forall st',
                           sigma (occ_gst o) h = Some st' ->
                           cur_request st' = None)) ex.
Proof.
  intros.
  find_eapply_lem_hyp queries_dont_always_not_stop; eauto.
  eapply not_always_eventually_not in H5.
  eapply eventually_monotonic_simple; [|eassumption].
  unfold not_tl; destruct s; simpl.
  intros.
  apply Classical_Prop.NNPP.
  firstorder.
Qed.

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
  intros.
  inv_prop live_node; repeat (break_exists || break_and).
  copy_eapply_prop_hyp busy_if_live live_node;
    forwards; eauto; concludes; eauto.
  destruct (cur_request x) as [[[? ?] ?]|] eqn:?; try congruence.
  find_eapply_lem_hyp queries_eventually_stop'; eauto.
  eapply eventually_monotonic_simple; try eassumption.
  destruct s; unfold not_busy_if_live.
  simpl; firstorder.
(*
This is tricky.

  If you have an open request, you're in the middle of some operation.
  Operations (stabilization, rectifying, etc) undertaken by joined nodes complete
  in finitely many request-response pairs.
  A request eventually gets a response if there are no circular waits...

DIFFICULTY: Ryan
USED: In phase one for the proof of eventual stabilization.
*)
Qed.
