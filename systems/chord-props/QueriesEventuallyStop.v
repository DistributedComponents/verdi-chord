Require Import Classical.
Require Import List.
Import ListNotations.
Require Import Relations.
Require Import Omega.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Require Import StructTact.StructTactics.
Require Import StructTact.Update.
Require Import InfSeqExt.infseq.
Require Import InfSeqExt.classical.
Require Import Chord.InfSeqTactics.
Require Import Chord.LabeledWF.

Require Import Chord.Chord.

Require Import Chord.HandlerLemmas.
Require Import Chord.SystemReachable.
Require Import Chord.SystemLemmas.
Require Import Chord.SystemPointers.
Require Import Chord.LabeledLemmas.
Require Import Chord.LiveNodesNotClients.
Require Import Chord.QueryInvariant.
Require Import Chord.QueryTargetsJoined.
Require Import Chord.NodesHaveState.
Require Import Chord.ValidPointersInvariant.

Set Bullet Behavior "Strict Subproofs".

(* The (blocked_by s h) relation relates a live node h to a node s when
   a message from h is stored in the delayed_queries list at s. *)
Definition blocked_by (gst : global_state) (s h : addr) : Prop :=
  live_node gst h /\
  live_node gst s /\
  exists st__h st__s dstp q m,
    sigma gst h = Some st__h /\
    sigma gst s = Some st__s /\
    cur_request st__h = Some (dstp, q, m) /\
    cur_request st__s <> None /\
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

Lemma continuously_false_false :
  forall T (s : infseq T),
    continuously (fun _ => False) s ->
    False.
Proof.
  intros.
  induction 0 as [[o s] ?|o s];
    now inv_prop always.
Qed.

Theorem l_enabled_RecvMsg_means_in_msgs :
  forall src dst m occ,
    l_enabled (RecvMsg src dst m) occ ->
    In (src, (dst, m)) (msgs (occ_gst occ)).
Proof.
  intros.
  inv_prop l_enabled.
  inv_labeled_step.
  handler_def.
  repeat find_rewrite; destruct m0 as [? [? ?]];
    repeat find_rewrite || find_injection;
    eauto with datatypes.
Qed.
Hint Resolve l_enabled_RecvMsg_means_in_msgs.

Theorem cur_request_constant_when_req_on_wire :
  forall gst l gst' h st st' dstp q m,
    reachable_st gst ->
    labeled_step_dynamic gst l gst' ->
    sigma gst h = Some st ->
    sigma gst' h = Some st' ->
    cur_request st = Some (dstp, q, m) ->
    query_request q m ->
    In (h, (addr_of dstp, m)) (msgs gst) ->
    ~ In (addr_of dstp) (failed_nodes gst) -> 
    cur_request st' = Some (dstp, q, m).
Proof.
  intros; invcs_prop labeled_step_dynamic.
  - repeat (handler_def || handler_simpl);
      repeat find_rewrite || find_injection;
      try solve [inv_prop timeout_constraint; tauto].
  - destruct m0 as [src [dst p]]; simpl in *.
    destruct (addr_eq_dec dst h); subst;
      [|rewrite_update; congruence].
    destruct (addr_eq_dec src (addr_of dstp));
      [|repeat (handler_def || handler_simpl; try congruence)].
    assert (no_responses (channel gst src h)).
    {
      find_copy_eapply_lem_hyp (sent_message_means_in_nodes_or_client gst src h);
        repeat find_rewrite; auto with datatypes.
      repeat match goal with
             | H: _ \/ _ |- _ => destruct H
             | H: _ /\ _ |- _ => destruct H
             end.
      - assert (exists st, sigma gst src = Some st) by (subst; eauto).
        break_exists_name st__src.
        assert (query_message_ok h src
                                 (cur_request d) (delayed_queries st__src)
                                 (channel gst h src) (channel gst src h))
          by (subst; eauto).
        subst; inv_prop query_message_ok; eauto.
        repeat find_rewrite || find_injection.
        exfalso; eapply_prop no_requests.
        + eapply in_msgs_in_channel.
          repeat find_rewrite; eauto.
        + eauto.
      - intro; intros.
        find_apply_lem_hyp in_channel_in_msgs.
        find_apply_lem_hyp sent_message_means_in_nodes_or_client; auto.
        break_or_hyp.
        + exfalso; eapply nodes_not_clients; eauto.
        + break_and; invcs_prop client_payload;
            intro; inv_prop response_payload.
    }
    assert (~ response_payload p).
    {
      intro.
      eapply_prop no_responses; eauto.
      eapply in_msgs_in_channel.
      repeat find_rewrite.
      eauto with datatypes.
    }
    repeat (handler_def; handler_simpl);
      try solve [exfalso; find_eapply_prop response_payload; constructor];
      try congruence.
    repeat (handler_def || handler_simpl).
  - inv_prop client_payload.
    repeat (handler_def; handler_simpl);
      try solve [exfalso; find_eapply_prop response_payload; constructor];
      try congruence.
    repeat (handler_def || handler_simpl).
  - congruence.
Qed.

Lemma occurred_execution_enabled :
  forall l o o' ex,
    lb_execution (Cons o (Cons o' ex)) ->
    occurred l o ->
    l_enabled l o.
Proof.
  unfold l_enabled, enabled, occurred; intros.
  inv_prop lb_execution; eauto.
Qed.
Hint Resolve occurred_execution_enabled.

Theorem req_on_wire_until_response :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall dstp q m st,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      query_request q m ->
      In m (channel (occ_gst (hd ex)) h (addr_of dstp)) ->
      live_node (occ_gst (hd ex)) (addr_of dstp) ->
      until (and_tl
               (now (fun o =>
                    In m (channel (occ_gst o) h (addr_of dstp))))
               (next 
                  (now (fun o =>
                          In m (channel (occ_gst o) h (addr_of dstp))))))
            (and_tl
               (now (fun o =>
                       In m (channel (occ_gst o) h (addr_of dstp))))
               (next (now (fun o =>
                             (exists st,
                                 sigma (occ_gst o) (addr_of dstp) = Some st /\
                                 In (h, m) (delayed_queries st) /\
                                 blocked_by (occ_gst o) (addr_of dstp) h) \/
                             exists res,
                               request_response_pair m res /\
                               In res (channel (occ_gst o) (addr_of dstp) h)))))
            ex.
Proof.
  intros.
  assert (until (now (l_enabled (RecvMsg h (addr_of dstp) m)))
                (now (occurred (RecvMsg h (addr_of dstp) m))) ex).
  {
    find_apply_lem_hyp in_channel_in_msgs.
    inv_prop live_node; expand_def; eauto.
    eapply RecvMsg_strong_until_occurred;
      eauto using strong_local_fairness_weak.
  }
  assert (forall st, sigma (occ_gst (hd ex)) h = Some st -> cur_request st = Some (dstp, q, m))
    by (intros; congruence).
  repeat match goal with
         | H: In _ (channel _ _ _) |- _ => clear H
         | H: sigma _ _ = _ |- _ => clear H
         | H: cur_request st = _ |- _ => clear H
         end.
  match goal with
  | H: until _ _ _ |- _ => induction H
  end.
  - destruct s as [o [o' s]].
    eapply U0; simpl in *.
    unfold occurred in *;
      inv_lb_execution;
      inv_labeled_step;
      clean_up_labeled_step_cases.
    handler_def.
    destruct m0 as [? [? ?]]; repeat find_rewrite || find_injection.
    simpl (fst _) in *; simpl (snd _) in *.
    find_copy_apply_lem_hyp requests_get_response_or_queued; eauto.
    break_or_hyp; break_and; split.
    + admit.
    + left.
      unfold blocked_by.
      repeat (split; invar_eauto).
      assert (live_node (occ_gst o') a) by invar_eauto.
      assert (live_node (occ_gst o') (addr_of dstp)) by invar_eauto.
      assert (live_node (occ_gst o) a) by invar_eauto.
      assert (live_node (occ_gst o) (addr_of dstp)) by invar_eauto.
      do 4 invcs_prop live_node; expand_def.
      pose proof (query_message_ok_invariant (occ_gst o') ltac:(invar_eauto) a (addr_of dstp)) as Qi'.
      do 2 insterU Qi'.
      forwards; eauto. concludes.
      forwards; eauto. concludes.
      forwards; eauto. concludes.
      pose proof (query_message_ok_invariant (occ_gst o) ltac:(invar_eauto) a (addr_of dstp)) as Qi.
      do 2 insterU Qi.
      forwards; eauto. concludes.
      forwards; eauto. concludes.
      forwards; eauto. concludes.

      assert (cur_request x1 = Some (dstp, q, p)) by eauto.
      assert (cur_request st0 = cur_request d).
      {
        destruct (cur_request x2) as [[[? ?] ?]|] eqn:?.
        - repeat find_rewrite || find_injection.
          simpl in *.
          do 4 find_inversion.
          repeat find_reverse_rewrite.
          eapply recv_msg_not_right_response_preserves_cur_request; eauto.
        - congruence.
      }
      admit.
    + admit.
    + right.
      break_exists_exists; intuition eauto.
      apply in_msgs_in_channel; simpl.
      repeat find_rewrite; simpl.
      apply in_or_app; left.
      apply in_map_iff; eauto.
  - destruct s as [o [o' s]]; simpl in *.
    apply U_next; try split; simpl; eauto.
    + inv_prop until; invar_eauto.
    + apply IHuntil; invar_eauto.
      intros.
      inv_prop lb_execution.
      repeat invcs_prop live_node; expand_def.
      eapply cur_request_constant_when_req_on_wire; eauto.
Admitted.

Inductive cr_order (h : addr) : relation global_state :=
| CRNone :
    forall gst gst' st st' dstp q m,
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      cur_request st = Some (dstp, q, m) ->
      cur_request st' = None ->
      cr_order h gst' gst
| CRStabilizeStabilize2 :
    forall gst gst' st st' dstp m dstp' ns m',
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      cur_request st = Some (dstp, Stabilize, m) ->
      cur_request st' = Some (dstp', Stabilize2 ns, m') ->
      cr_order h gst' gst
| CRStabilizeStabilize :
    forall gst gst' st st' dstp m dstp' m' s rest,
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      cur_request st = Some (dstp, Stabilize, m) ->
      succ_list st = s :: rest ->
      cur_request st' = Some (dstp', Stabilize, m') ->
      succ_list st' = rest ->
      cr_order h gst' gst.

Lemma none_best_cur_request :
  forall h gst,
    stuck (cr_order h) gst ->
    forall st,
      sigma gst h = Some st ->
      cur_request st = None.
Proof.
  intros.
  destruct (cur_request st) as [[[dstp q] m]|] eqn:?; auto.
  set (st' := clear_query st).
  set (gst' := {| nodes := nodes gst;
                  failed_nodes := failed_nodes gst;
                  timeouts := timeouts gst;
                  sigma := update addr_eq_dec (sigma gst) h (Some st');
                  msgs := msgs gst;
                  trace := trace gst |}).
  find_eapply_lem_hyp (CRNone h gst gst'); simpl; rewrite_update; eauto.
  firstorder.
Qed.
Hint Resolve none_best_cur_request.

Lemma stuck_if_cr_none :
  forall h gst st,
    sigma gst h = Some st ->
    cur_request st = None ->
    stuck (cr_order h) gst.
Proof.
  unfold stuck; intros.
  inv_prop cr_order; congruence.
Qed.
Hint Resolve stuck_if_cr_none.

Lemma cr_order_stabilize2_acc :
  forall h gst st dstp ns m,
    sigma gst h = Some st ->
    cur_request st = Some (dstp, Stabilize2 ns, m)  ->
    Acc (cr_order h) gst.
Proof.
  intros.
  constructor; intros;
    inv_prop cr_order;
    congruence || eauto.
Qed.
Hint Resolve cr_order_stabilize2_acc.

Lemma cr_order_stabilize_acc :
  forall h gst st dstp m,
    sigma gst h = Some st ->
    cur_request st = Some (dstp, Stabilize, m) ->
    Acc (cr_order h) gst.
Proof.
  intros.
  remember (succ_list st) as succs.
  generalizeEverythingElse succs.
  induction succs;
    constructor; intros.
  - inv_prop cr_order;
      solve [eauto | congruence].
  - inv_prop cr_order; eauto.
    eapply IHsuccs;
      solve [eauto | congruence].
Qed.
Hint Resolve cr_order_stabilize_acc.

Theorem cr_order_wf :
  forall h,
    well_founded (cr_order h).
Proof.
  unfold well_founded.
  constructor.
  intros; inv_prop cr_order; eauto.
Qed.
Hint Resolve cr_order_wf.

Definition channel_delayed_query gst src dstp st st__dst q m :=
  ~ In (addr_of dstp) (failed_nodes gst) /\
  sigma gst src = Some st /\
  cur_request st = Some (dstp, q, m) /\
  query_request q m /\
  sigma gst (addr_of dstp) = Some st__dst /\
  In (src, m) (delayed_queries st__dst) /\
  no_requests (channel gst src (addr_of dstp)) /\
  no_responses (channel gst (addr_of dstp) src).

Definition channel_request gst src dstp st st__dst q m req xs ys :=
  ~ In (addr_of dstp) (failed_nodes gst) /\
  sigma gst src = Some st /\
  cur_request st = Some (dstp, q, m) /\
  query_request q req /\
  channel gst src (addr_of dstp) = xs ++ req :: ys /\
  no_requests (xs ++ ys) /\
  no_responses (channel gst (addr_of dstp) src) /\
  sigma gst (addr_of dstp) = Some st__dst /\
  (forall r, ~ In (src, r) (delayed_queries st__dst)).

Definition channel_response gst src dstp st st__dst q m res xs ys :=
  sigma gst src = Some st /\
  cur_request st = Some (dstp, q, m) /\
  no_requests (channel gst src (addr_of dstp)) /\
  query_response q res /\
  channel gst (addr_of dstp) src = xs ++ res :: ys /\
  no_responses (xs ++ ys) /\
  sigma gst (addr_of dstp) = Some st__dst /\
  (forall r, ~ In (src, r) (delayed_queries st__dst)).

Definition channel_dead gst src dstp st q m :=
  In (addr_of dstp) (failed_nodes gst) /\
  sigma gst src = Some st /\
  cur_request st = Some (dstp, q, m) /\
  no_responses (channel gst (addr_of dstp) src).
Hint Unfold channel_request channel_delayed_query channel_response channel_dead.

Inductive channel_order (src : addr) : global_state -> global_state -> Prop :=
  COReqRes :
    forall dstp q m st st' st__dst st__dst' gst gst' req res xs ys xs' ys',
      channel_request gst src dstp st st__dst q m req xs ys ->
      channel_response gst' src dstp st' st__dst' q m res xs' ys' ->
      request_response_pair req res ->
      channel_order src gst' gst
| COReqDelayed :
    forall dstp q m gst gst' req st st' xs ys st__dst st__dst',
      channel_request gst src dstp st st__dst q m req xs ys ->
      channel_delayed_query gst' src dstp st' st__dst' q m ->
      channel_order src gst' gst
| CODelayedRes :
    forall dstp q m gst gst' req res st st__dst st' st__dst' xs' ys',
      channel_delayed_query gst src dstp st st__dst q m ->
      channel_response gst' src dstp st' st__dst' q m res xs' ys' ->
      request_response_pair req res ->
      channel_order src gst' gst
| CODelayedDead :
    forall dstp q m gst gst' req res st st__dst st',
      channel_delayed_query gst src dstp st st__dst q m ->
      channel_dead gst' src dstp st' q m ->
      request_response_pair req res ->
      channel_order src gst' gst
| COReqDead :
    forall dstp q m gst gst' req res st st__dst st' xs ys,
      channel_request gst src dstp st st__dst q m req xs ys ->
      channel_dead gst' src dstp st' q m ->
      request_response_pair req res ->
      channel_order src gst' gst.

Inductive channel_preequiv (src : addr) : relation global_state :=
| CERes :
    forall gst gst' dstp st st' st__dst st__dst' q m res xs ys xs' ys',
      channel_response gst src dstp st st__dst q m res xs ys ->
      channel_response gst' src dstp st' st__dst' q m res xs' ys' ->
      channel_preequiv src gst gst'
| CEReq :
    forall gst gst' dstp st st' st__dst st__dst' q m req xs ys xs' ys',
      channel_request gst src dstp st st__dst q m req xs ys ->
      channel_request gst' src dstp st' st__dst' q m req xs' ys' ->
      channel_preequiv src gst gst'
| CEDelayed :
    forall dstp q m gst gst' st st__dst st' st__dst',
      channel_delayed_query gst src dstp st st__dst q m ->
      channel_delayed_query gst' src dstp st' st__dst' q m ->
      channel_preequiv src gst gst'
| CEDead :
    forall gst gst' dstp st st' q m,
      channel_dead gst src dstp st q m ->
      channel_dead gst' src dstp st' q m ->
      channel_preequiv src gst gst'
| CEInactive :
    forall gst gst' st st',
      sigma gst src = Some st ->
      sigma gst' src = Some st' ->
      cur_request st = None ->
      cur_request st' = None ->
      channel_preequiv src gst gst'
| CENothing :
    forall gst gst',
      sigma gst src = None ->
      sigma gst' src = None ->
      channel_preequiv src gst gst'.

Lemma response_to_query_request_query_response :
  forall q req res,
    request_response_pair req res ->
    query_request q req ->
    query_response q res.
Proof.
  intros.
  inv_prop request_response_pair;
    inv_prop query_request;
    constructor.
Qed.
Hint Resolve response_to_query_request_query_response.

Lemma channel_preequiv_refl :
  forall src gst,
    reachable_st gst ->
    channel_preequiv src gst gst.
Proof.
  intros.
  destruct (sigma gst src) eqn:?;
    try now constructor.
  destruct (cur_request d) as [[[dstp q] m]|] eqn:?;
    try now econstructor; eauto.
  find_copy_eapply_lem_hyp query_target_joined; eauto.
  break_exists; break_and.
  assert (query_message_ok' src (addr_of dstp) (cur_request d) (delayed_queries x) (failed_nodes gst)
                             (channel gst src (addr_of dstp)) (channel gst (addr_of dstp) src))
    by eauto.
  inv_prop query_message_ok'.
  - inv_prop query_message_ok;
      try congruence.
    + repeat find_eapply_lem_hyp in_split; expand_def.
      repeat find_rewrite || find_injection.
      eapply CEReq; autounfold; intuition eauto.
    + repeat find_eapply_lem_hyp in_split; expand_def.
      repeat find_rewrite || find_injection.
      eapply CERes; autounfold; intuition eauto.
    + repeat find_eapply_lem_hyp in_split; expand_def.
      repeat find_rewrite || find_injection.
      eapply CEDelayed; autounfold; intuition eauto.
      repeat find_rewrite; eauto with datatypes.
      repeat find_rewrite; eauto with datatypes.
  - repeat find_eapply_lem_hyp in_split; expand_def.
    repeat find_rewrite || find_injection.
    eapply CERes; autounfold; intuition eauto.
  - eapply CEDead; eauto.
Qed.

(* Make channel_preequiv reflexive on the nose *)
Definition channel_equiv (src : addr) : relation global_state :=
  fun gst gst' =>
    channel_preequiv src gst gst' \/
    ~ reachable_st gst /\
    ~ reachable_st gst'.

Lemma reachable_classic :
  forall gst,
    reachable_st gst \/ ~ reachable_st gst.
Proof.
  auto using classic.
Qed.

Instance channel_equiv_equivalence (src : addr) :
  Equivalence (channel_equiv src).
Proof.
  split; intros.
  - repeat intro.
    unfold channel_equiv.
    destruct (reachable_classic x);
      eauto using channel_preequiv_refl.
  - repeat intro.
    unfold channel_equiv.
    inv_prop channel_equiv.
    + invcs_prop channel_preequiv; solve [left; econstructor; eauto].
    + tauto.
  - repeat intro.
    unfold channel_equiv.
    repeat invcs_prop channel_equiv.
    + admit.
    + admit.
    + admit.
    + tauto.
Admitted.

Instance channel_order_proper (src : addr) :
  Proper (channel_equiv src ==> channel_equiv src ==> iff) (channel_order src).
Proof.
  repeat intro || split.
  - invcs_prop channel_order.
    + repeat invcs_prop channel_equiv;
      repeat invcs_prop channel_preequiv;
      repeat match goal with
             | H: In ?a (failed_nodes ?gst),
               H': ~ In ?a (failed_nodes ?gst) |- _ =>
               tauto
             | Hnores: no_responses ?l |- _ =>
               exfalso; eapply Hnores; now eauto with datatypes
             | Hnoreq: no_requests ?l |- _ =>
               exfalso; eapply Hnoreq; now eauto with datatypes
             | H: context[channel_response ?gst],
               H': context[channel_request ?gst] |- _ =>
               invcs H; invcs H'; break_and; repeat find_rewrite || find_injection
             | H: context[channel_response ?gst],
               H': context[channel_delayed_query ?gst] |- _ =>
               invcs H; invcs H'; break_and; repeat find_rewrite || find_injection
             | H: context[channel_response ?gst],
               H': context[channel_dead ?gst] |- _ =>
               invcs H; invcs H'; break_and; repeat find_rewrite || find_injection
             | H: context[channel_request ?gst],
               H': context[channel_delayed_query ?gst] |- _ =>
               invcs H; invcs H'; break_and; repeat find_rewrite || find_injection
             | H: context[channel_request ?gst],
               H': context[channel_dead ?gst] |- _ =>
               invcs H; invcs H'; break_and; repeat find_rewrite || find_injection
             | H: _ = None |- _ =>
               repeat (invcs_prop channel_response ||
                       invcs_prop channel_request ||
                       invcs_prop channel_delayed_query);
                 break_and;
                 congruence
             end.
      admit.
      admit.
      admit.
      admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - admit.
Admitted.

Lemma res_exists_for_req :
  forall req,
    request_payload req ->
    exists res,
      request_response_pair req res.
Proof.
  intros.
  inv_prop request_payload; eexists; constructor.
  Unshelve.
  all:auto using nil, None.
Qed.
Hint Resolve res_exists_for_req.

Lemma res_best_channel_config :
  forall src gst st dstp q m,
    reachable_st gst ->
    stuck (channel_order src) gst ->
    sigma gst src = Some st ->
    cur_request st = Some (dstp, q, m) ->
    no_requests (channel gst src (addr_of dstp)) /\
    (forall st__dstp req,
        sigma gst (addr_of dstp) = Some st__dstp ->
        ~ In (src, req) (delayed_queries st__dstp)) \/
    no_responses (channel gst (addr_of dstp) src) /\
    In (addr_of dstp) (failed_nodes gst).
Proof.
  unfold stuck; intros.
  find_copy_eapply_lem_hyp cur_request_valid; eauto.
  inv_prop valid_ptr.
  find_apply_lem_hyp nodes_have_state; eauto.
  break_exists_name st__dstp.
  find_copy_eapply_lem_hyp (query_message_ok'_invariant gst ltac:(auto) src (addr_of dstp));
    eauto.
  inv_prop query_message_ok'; try inv_prop query_message_ok.
  - congruence.
  - congruence.
  - left.
    simpl in *.
    assert (request_payload req) by eauto.
    find_copy_apply_lem_hyp (res_exists_for_req req).
    break_exists_name r.
    set (gst' := {| nodes := nodes gst;
                    failed_nodes := failed_nodes gst;
                    timeouts := timeouts gst;
                    sigma := sigma gst;
                    msgs := [((addr_of dstp), (src, r))];
                    trace := trace gst |}).
    assert (no_requests (channel gst' src (addr_of dstp))).
    {
      unfold no_requests.
      intros.
      find_apply_lem_hyp in_channel_in_msgs.
      simpl in *; intuition; find_injection; eauto.
    }
    assert (channel gst' (addr_of dstp) src = [r]).
    {
      unfold channel, ssrbool.is_left; simpl.
      destruct (addr_eq_dec (addr_of dstp) (addr_of dstp)); try congruence.
      destruct (addr_eq_dec src src); try congruence.
      reflexivity.
    }
    replace dstp0 with dstp in * by congruence; clear dstp0.
    find_apply_lem_hyp in_split; break_exists.
    exfalso; find_eapply_prop False.
    instantiate (1:=gst').
    repeat find_rewrite || find_injection.
    econstructor 1; autounfold; repeat split; eauto.
    + repeat find_rewrite.
      change [r] with ([] ++ r :: []); eauto.
    + unfold no_responses; tauto.
  - left.
    split; auto.
    intros.
    replace st__dstp0 with st__dstp by congruence.
    eauto.
  - left.
    assert (request_payload req) by eauto.
    find_copy_apply_lem_hyp (res_exists_for_req req).
    break_exists_name r.
    set (st' := clear_delayed_queries st).
    set (gst' := {| nodes := nodes gst;
                    failed_nodes := failed_nodes gst;
                    timeouts := timeouts gst;
                    sigma := update addr_eq_dec (sigma gst) (addr_of dstp) (Some st');
                    msgs := [((addr_of dstp), (src, r))];
                    trace := trace gst |}).
    assert (no_requests (channel gst' src (addr_of dstp))).
    {
      unfold no_requests.
      intros.
      find_apply_lem_hyp in_channel_in_msgs.
      simpl in *; intuition; find_injection; eauto.
    }
    assert (channel gst' (addr_of dstp) src = [] ++ [r]).
    {
      unfold channel, ssrbool.is_left; simpl.
      destruct (addr_eq_dec (addr_of dstp) (addr_of dstp)); try congruence.
      destruct (addr_eq_dec src src); try congruence.
      reflexivity.
    }
    replace dstp0 with dstp in * by congruence; clear dstp0.
    find_apply_lem_hyp in_split; break_exists.
    exfalso; find_eapply_prop False.
    instantiate (1:=gst').
    destruct (addr_eq_dec (addr_of dstp) src).
    + econstructor 3; autounfold; repeat split;
        simpl; rewrite_update; eauto.
      * congruence.
      * repeat find_rewrite || find_injection; auto with datatypes.
      * repeat find_rewrite || find_injection; eauto.
      * unfold no_responses; tauto.
    + econstructor 3; autounfold; repeat split;
        simpl; rewrite_update; eauto.
      * congruence.
      * repeat find_rewrite || find_injection; auto with datatypes.
      * repeat find_rewrite || find_injection; eauto.
      * unfold no_responses; tauto.
  - left.
    intuition.
    repeat find_rewrite || find_injection.
    eauto.
  - tauto.
Qed.

Lemma co_res_acc :
  forall src gst dstp xs ys res st q m,
    sigma gst src = Some st ->
    cur_request st = Some (dstp, q, m) ->
    response_payload res ->
    channel gst (addr_of dstp) src = xs ++ res :: ys ->
    no_responses (xs ++ ys) ->
    Acc (channel_order src) gst.
Proof.
  intros.
  assert (In res0 (channel gst (addr_of dstp) src))
    by (find_rewrite; auto with datatypes).
  constructor; intros; inv_prop channel_order;
    autounfold in *; break_and;
    assert (dstp0 = dstp) by congruence; subst;
      exfalso;
      find_eapply_prop (no_responses (channel gst (addr_of dstp) src));
      eauto.
Qed.
Hint Resolve co_res_acc.

Lemma co_dead_acc :
  forall src gst dstp st q m,
    sigma gst src = Some st ->
    cur_request st = Some (dstp, q, m) ->
    In (addr_of dstp) (failed_nodes gst) ->
    no_responses (channel gst (addr_of dstp) src) ->
    Acc (channel_order src) gst.
Proof.
  intros.
  constructor; intros; inv_prop channel_order;
    autounfold in *; break_and;
      assert (dstp0 = dstp) by congruence; subst;
        tauto.
Qed.
Hint Resolve co_dead_acc.

Lemma co_delayed_acc :
  forall src gst dstp req st q m st__dstp,
    sigma gst src = Some st ->
    cur_request st = Some (dstp, q, m) ->
    sigma gst (addr_of dstp) = Some st__dstp ->
    In (src, req) (delayed_queries st__dstp) ->
    request_payload req ->
    Acc (channel_order src) gst.
Proof.
  intros.
  constructor; intros; inv_prop channel_order;
    autounfold in *; break_and;
    assert (dstp0 = dstp) by congruence; subst.
  - replace st__dst with st__dstp in * by congruence.
    exfalso; eauto.
  - replace st__dst with st__dstp in * by congruence.
    exfalso; eauto.
  - eauto.
  - eauto.
  - eauto.
Qed.
Hint Resolve co_delayed_acc.

Lemma co_req_acc :
  forall gst src st dstp q m req xs ys st__dstp,
    sigma gst src = Some st ->
    cur_request st = Some (dstp, q, m) ->
    sigma gst (addr_of dstp) = Some st__dstp ->
    query_request q req ->
    channel gst src (addr_of dstp) = xs ++ req :: ys ->
    no_requests (xs ++ ys) ->
    no_responses (channel gst (addr_of dstp) src) ->
    (forall r, ~ In (src, r) (delayed_queries st__dstp)) ->
    Acc (channel_order src) gst.
Proof.
  intros.
  constructor; intros; inv_prop channel_order;
    autounfold in *; intuition eauto.
Qed.
Hint Resolve co_req_acc.

Lemma channel_order_wf :
  forall src,
    well_founded (channel_order src).
Proof.
  unfold well_founded; intros.
  constructor; intros; inv_prop channel_order;
    autounfold in *; intuition eauto.
Qed.
Hint Resolve channel_order_wf.

Definition occ_order (R : relation global_state) : relation occurrence :=
  fun o o' => R (occ_gst o) (occ_gst o').

Lemma occ_order_wf :
  forall R,
    well_founded R ->
    well_founded (occ_order R).
Proof.
  unfold well_founded, occ_order.
  intros.
  remember (occ_gst a) as o.
  assert (Hacc: Acc R o) by auto.
  generalizeEverythingElse Hacc.
  induction Hacc; intros.
  constructor; intros; subst.
  eauto.
Qed.
Hint Resolve occ_order_wf.

Lemma occ_order_stuck :
  forall R o,
    stuck (occ_order R) o ->
    stuck R (occ_gst o).
Proof.
  unfold stuck, occ_order; intros.
  (* bogus *)
  set (o':={| occ_gst := t';
              occ_label := Timeout (String.EmptyString) Tick Ineffective|}).
  change (R t' (occ_gst o)) with (R (occ_gst o') (occ_gst o)) in *.
  eauto.
Qed.
Hint Resolve occ_order_stuck.

Inductive cr_equiv (h : addr) : relation global_state :=
| cr_equiv_not_stabilize :
    forall gst gst' st st' dstp q m,
      q <> Stabilize ->
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      cur_request st = Some (dstp, q, m) ->
      cur_request st' = Some (dstp, q, m) ->
      q <> Stabilize ->
      cr_equiv h gst gst'
| cr_equiv_succs :
    forall gst gst' st st',
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      cur_request st = cur_request st' ->
      succ_list st = succ_list st' ->
      cr_equiv h gst gst'
| cr_equiv_none :
    forall gst gst' st st',
      sigma gst h = Some st ->
      sigma gst' h = Some st' ->
      cur_request st = None ->
      cur_request st' = None ->
      cr_equiv h gst gst'
| cr_equiv_invalid :
    forall gst gst',
      sigma gst h = None ->
      sigma gst' h = None ->
      cr_equiv h gst gst'.

Instance cr_equiv_Equivalence (h : addr) : Equivalence (cr_equiv h).
Proof.
  split; repeat intro.
  - destruct (sigma x h) eqn:?.
    + econstructor 2; eauto.
    + econstructor 4; eauto.
  - inv_prop cr_equiv; 
      solve [econstructor; eauto].
  - repeat invcs_prop cr_equiv;
      repeat find_rewrite || find_injection;
      solve [congruence | econstructor; eauto].
Defined.

Instance cr_order_cr_equiv_proper (h : addr) :
  Proper (cr_equiv h ==> cr_equiv h ==> iff) (cr_order h).
Proof.
  repeat intro || split.
  - admit.
  - admit.
Admitted.

Definition query_order (h : addr) :=
  occ_order (lex_diag (cr_equiv h) (cr_order h) (channel_order h)).

Theorem query_order_wf :
  forall h,
    well_founded (query_order h).
Proof.
  unfold query_order; eauto with typeclass_instances.
Qed.
Hint Resolve query_order_wf.

Lemma stuck_query_order_cr_order :
  forall h o,
    stuck (query_order h) o ->
    stuck (cr_order h) (occ_gst o).
Proof.
  eauto.
Qed.
Hint Resolve stuck_query_order_cr_order.

Theorem stuck_query_order_done :
  forall h o st,
    stuck (query_order h) o ->
    sigma (occ_gst o) h = Some st ->
    cur_request st = None.
Proof.
  eauto.
Qed.
Hint Resolve stuck_query_order_done.

Definition query_order_stuck_dec :
  forall h o,
    {stuck (query_order h) o} + {~ stuck (query_order h) o}.
Proof.
Admitted.

Definition query_equiv (h : addr) : relation occurrence :=
  occ_order (equiv_both (cr_equiv h) (channel_equiv h)).

Instance query_equiv_Equiv (h : addr) :
  Equivalence (query_equiv h).
Proof.
Admitted.

Lemma occ_order_proper :
  forall R S ord,
    Equivalence R ->
    Equivalence S ->
    Proper (R ==> S ==> iff) ord ->
    Proper (occ_order R ==> occ_order S ==> iff) (occ_order ord).
Proof.
  unfold occ_order.
  repeat intro || split;
    repeat match goal with
           | o : occurrence |- _ => destruct o
           | |- _ => simpl in *
           end;
    find_eapply_prop @Proper;
    eauto; auto with relations.
Qed.

Instance query_order_proper (h : addr) :
  Proper (query_equiv h ==> query_equiv h ==> iff) (query_order h).
Proof.
  eapply occ_order_proper.
  - eapply Eq_both; typeclasses eauto.
  - eapply Eq_both; typeclasses eauto.
  - eapply lex_diag_proper; eauto with relations typeclass_instances.
Qed.

Theorem cur_request_is_query_request :
  forall gst h dstp q m st,
    reachable_st gst ->
    sigma gst h = Some st ->
    cur_request st = Some (dstp, q, m) ->
    query_request q m.
Proof.
  intros.
  find_apply_lem_hyp cur_request_timeouts_related_invariant_elim;
    eauto.
  repeat find_rewrite.
  find_apply_lem_hyp cur_request_timeouts_ok'_complete.
  now invcs_prop cur_request_timeouts_ok'.
Qed.
Hint Resolve cur_request_is_query_request.

Lemma request_still_on_wire_means_query_equiv :
  forall o o' req src dst,
    In req (channel (occ_gst o) src dst) ->
    In req (channel (occ_gst o') src dst) ->
    query_equiv src o o'.
Proof.
Admitted.

Theorem req_on_wire_eventually_improved_or_stuck :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall st dstp q req,
      sigma (occ_gst (hd ex)) h = Some st ->
      live_node (occ_gst (hd ex)) (addr_of dstp) ->
      cur_request st = Some (dstp, q, req) ->
      In req (channel (occ_gst (hd ex)) h (addr_of dstp)) ->
      eventually (now (fun t => query_order h t (hd ex))) ex.
Proof.
  intros.
  find_copy_eapply_lem_hyp req_on_wire_until_response; eauto.
           assert (query_request q req) by eauto;
             remember (addr_of dstp) as adst;
             clear Heqadst;
             clear H5 dstp.
  repeat match goal with
         | H: cur_request _ = Some (?dstp, ?q, ?m) |- _ =>
           let Heq := fresh "Heq" in
           assert (query_request q m) by eauto;
             remember (addr_of dstp) as adst eqn:Heq;
             clear H Heq dstp
         | H: In _ (channel _ _ _) |- _ => clear H
         | H: sigma _ _ = Some ?st |- _ => clear H; clear st
         | H: until _ _ ?ex |- eventually _ ?ex => induction H
         end.
  - destruct s as [o [o' ex]].
    eapply E_next, E0; simpl.
    assert (live_node (occ_gst o') adst) by eauto with invar.
    assert (live_node (occ_gst o') h) by eauto with invar.
    find_copy_eapply_lem_hyp (live_node_means_state_exists (occ_gst o) h).
    find_copy_eapply_lem_hyp (live_node_means_state_exists (occ_gst o) adst).
    find_copy_eapply_lem_hyp (live_node_means_state_exists (occ_gst o') h).
    find_copy_eapply_lem_hyp (live_node_means_state_exists (occ_gst o') adst).
    repeat break_exists.
    find_copy_eapply_lem_hyp (query_message_ok_invariant
                                (occ_gst o) ltac:(eauto with invar)
                                                   h adst); eauto.
    find_copy_eapply_lem_hyp (query_message_ok_invariant
                                (occ_gst o') ltac:(eauto with invar)
                                                    h adst); eauto.
    assert (sigma (occ_gst o) h = sigma (occ_gst o') h).
    {
      simpl in *.
      repeat match goal with
             | H: (?P /\_ ?Q) ?s |- _ =>
               let HP := fresh "P" in
               let HQ := fresh "Q" in
               destruct H as [HP HQ];
                 simpl in HP, HQ
             end;
        expand_def.
      - admit.
      - admit.
    }
    
    repeat match goal with
           | H: (?P /\_ ?Q) ?s |- _ =>
             let HP := fresh "P" in
             let HQ := fresh "Q" in
             destruct H as [HP HQ];
               simpl in HP, HQ
           | |- context[(hd (Cons _ _))] =>
             simpl
           | H: context[(hd (Cons _ _))] |- _ =>
             simpl in H
           | H: exists _, _ |- _ =>
             destruct H
           | H: _ /\ _ |- _ =>
             destruct H
           | H: _ \/ _ |- _ =>
             destruct H
           | Hdone: ?st = ?st',
             H: sigma (occ_gst o) h = Some ?st,
             H': sigma (occ_gst o') h = Some ?st' |- _ =>
             idtac
           | H: sigma (occ_gst o) h = Some ?st,
             H': sigma (occ_gst o') h = Some ?st' |- _ =>
             let Heq := fresh "H" in
             assert (Heq: st = st') by congruence; subst
           end;
      repeat match goal with
             | H: addr_of ?a = addr_of ?b |- _ =>
               rewrite -> H in *
             | Hnoreq: no_requests ?c,
               Hreq: In ?req ?c |- _ =>
               solve [exfalso; eapply Hnoreq; eauto]
             | Hnores: no_responses ?c,
               Hres: In ?req ?c |- _ =>
               solve [exfalso; eapply Hnores; eauto]
             | Hnodel: forall m, ~ In (?h, m) (delayed_queries ?st),
               Hdel: blocked_by ?gst ?s ?h
               |- _ => invcs Hdel; expand_def
             | Hnodel: forall m, ~ In (?h, m) (delayed_queries ?st),
               Hdel: In (?h, ?m) (delayed_queries ?st')
               |- _ => assert (st = st') by congruence;
                       subst; specialize (Hnodel m); tauto
             | H: query_message_ok _ _ _ _ _ _ |- _ =>
               invcs H
             end;
    right; eauto using cr_equiv_succs; try congruence;
        try find_apply_lem_hyp (in_split req1);
        try find_apply_lem_hyp (in_split res0);
        expand_def;
        [eapply COReqDelayed|eapply COReqRes];
        autounfold; repeat split;
          repeat match goal with
                 | H: live_node ?gst ?h |- In ?h (failed_nodes ?gst) -> False =>
                   eapply live_node_not_in_failed_nodes; eauto
                 | H: query_request ?q ?req,
                   H': request_response_pair ?req ?res |-
                   query_response ?q' ?res =>
                   eapply response_to_query_request_query_response; [eauto | congruence]
                 | |- sigma _ _ = _ => solve [eauto]
                 | |- request_payload _ =>
                   solve [eapply query_request_request; eauto]
                 | H: Some _ = cur_request _ |- _ =>
                   symmetry in H
                 | H: cur_request ?x = Some (?dst, _, _),
                      H': cur_request ?x' = Some (?dst', _, _),
                          Heq: ?dst = ?dst' |- _ =>
                   idtac
                 | H: addr_of ?a = addr_of ?b |- _ =>
                   rewrite -> H in *
                 | H: cur_request ?x = Some (?dst, _, _),
                      H': cur_request ?x' = Some (?dst', _, _) |- _ =>
                   assert (dst = dst') by congruence; subst
                 end; eauto; try congruence.
    eapply response_to_query_request_query_response; [eauto | congruence].
  - destruct s.
    repeat match goal with
           | H: (_ /\_ _) _ |- _ => destruct H
           | _ => simpl in *
           end.
    assert (eventually (now (fun t : occurrence => query_order h t o)) (Cons x (Cons o s)))
      by (constructor; eapply IHuntil; invar_eauto).
    assert (query_equiv h x o)
      by eauto using request_still_on_wire_means_query_equiv.
    eapply eventually_monotonic_simple; try eassumption.
    intros [o'' s''] ?; simpl in *.
    eapply query_order_proper;
      eauto; eauto with relations.
Admitted.

Theorem eventually_done_or_always_blocked_via_relation :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    always
      (fun s =>
         ~ stuck (query_order h) (hd s) ->
         eventually
           (or_tl (now (fun t => query_order h t (hd s)))
                  (fun s' => exists dstp,
                       always (now (fun o => blocked_by (occ_gst o)
                                                     (addr_of dstp)
                                                     h)) s'))
           s)
      ex.
Proof.
  cofix c.
  intros; constructor; intros;
    [clear c|destruct ex; apply c; invar_eauto].
  assert (H_cr: exists st, sigma (occ_gst (hd ex)) h = Some st /\
                      exists dstp q m,
                        cur_request st = Some (dstp, q, m)).
  {
    inv_prop live_node; break_and.
    break_exists_exists; expand_def.
    split; simpl in *; auto.
    destruct (cur_request x) as [[[? ?] ?]|]; try eauto.
    exfalso.
    find_eapply_prop stuck.
    admit.
  }
  break_exists_name st; break_and;
    break_exists_name dstp;
    break_exists_name q;
    break_exists_name m.
  assert (H_dl: live_node (occ_gst (hd ex)) (addr_of dstp))
    by admit.
  assert (H_dst: exists st, sigma (occ_gst (hd ex)) (addr_of dstp) = Some st)
    by eauto.
  break_exists_name st__dstp.
  assert (query_message_ok h (addr_of dstp) (cur_request st)
                           (delayed_queries st__dstp)
                           (channel (occ_gst (hd ex)) h (addr_of dstp))
                           (channel (occ_gst (hd ex)) (addr_of dstp) h))
         by eauto.
  invcs_prop query_message_ok; intros.
  - congruence.
  - congruence.
  - find_eapply_lem_hyp req_on_wire_eventually_improved_or_stuck; eauto; try congruence.
    eapply eventually_monotonic_simple;
      [left|]; eassumption.
  - admit.
  - admit.
Admitted.

Lemma exists_eventually_comm :
  forall T U (P : U -> infseq T -> Prop) ex,
    eventually (fun s => exists x, P x s) ex ->
    exists x, eventually (fun s => P x s) ex.
Proof.
  induction 1.
  - break_exists_exists.
    now constructor.
  - break_exists_exists.
    now constructor.
Qed.

Lemma gross_always_lemma :
  forall (T U : Type) P Q R (ex : infseq T),
    always (fun s => P s ->
                  eventually ((Q s) \/_ (fun s => exists x: U, always (R x) s)) s) ex ->
    always (fun s => P s -> eventually (Q s) s) ex \/
    exists x, eventually (always (R x)) ex.
Proof.
  intros.
  destruct (classic (exists x, eventually (always (R x)) ex)).
  - tauto. 
  - left.
    generalize dependent ex.
    cofix c.
    destruct ex; intros; constructor.
    + intros.
      find_apply_lem_hyp always_now'.
      concludes.
      find_apply_lem_hyp eventually_or_tl_or.
      break_or_hyp; try tauto.
      find_eapply_lem_hyp exists_eventually_comm.
      tauto.
    + simpl; eapply c; invar_eauto.
      intro.
      eapply_prop not.
      break_exists_exists.
      constructor; now auto.
Qed.

Theorem eventually_done_or_always_blocked :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    forall st dstp q m,
      sigma (occ_gst (hd ex)) h = Some st ->
      cur_request st = Some (dstp, q, m) ->
      eventually ((now (fun o => forall st, sigma (occ_gst o) h = Some st -> cur_request st = None))) ex \/
      exists dstp',
        continuously (now (fun o => blocked_by (occ_gst o) (addr_of dstp') h)) ex.
Proof.
  intros.
  find_eapply_lem_hyp eventually_done_or_always_blocked_via_relation; eauto.
  find_eapply_lem_hyp gross_always_lemma.
  break_or_hyp.
  - left.
    find_eapply_lem_hyp eventual_drop_means_eventually_stuck;
      eauto using query_order_stuck_dec.
    eapply eventually_monotonic_simple; try eassumption.
    destruct s; simpl in *; eauto.
  - eauto.
Qed.

Ltac fold_continuously :=
  match goal with
  | H: context[eventually (always ?P)] |- _ =>
    change (eventually (always P))
      with (continuously P) in H
  end.

Lemma now_and_tl_comm :
  forall T (P Q : T -> Prop) s,
    (now P /\_ now Q) s = now (fun o => P o /\ Q o) s.
Proof.
  intros.
  destruct s.
  reflexivity.
Qed.
Hint Rewrite now_and_tl_comm.

Lemma eventually_now_const :
  forall T (s : infseq T) P,
    eventually (now (fun _ => P)) s ->
    P.
Proof.
  induction 1; destruct s; simpl in *; tauto.
Qed.

Lemma blocking_node_continuously_also_blocked :
  forall ex,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
    forall h s,
      always (now (fun o => blocked_by (occ_gst o) s h)) ex ->
      exists w,
        continuously (now (fun o => blocked_by (occ_gst o) w s)) ex.
Proof.
  intros.
  destruct ex.
  find_copy_apply_lem_hyp always_now.
  simpl in *.
  inv_prop blocked_by; break_and.
  break_exists_name st__h.
  break_exists_name st__dst; expand_def.
  assert (exists dstp q m, cur_request st__dst = Some (dstp, q, m))
    by (destruct (cur_request st__dst) as [[[dstp q] m]|] eqn:Heq;
        intuition eauto).
  expand_def.
  change o with (hd (Cons o ex)) in *;
    find_eapply_lem_hyp eventually_done_or_always_blocked;
    try find_eapply_prop (addr_of x1);
    eauto.
  break_or_hyp.
  - exfalso.
    find_eapply_lem_hyp cumul_eventually_always; eauto.
    cut (eventually (fun _ => False) (Cons o ex)).
    {
      repeat match goal with H:_ |- _ => clear H end.
      induction 1; destruct ex; simpl in *; tauto.
    }
    eapply eventually_monotonic_simple; [|eassumption].
    intros.
    unfold and_tl in *; destruct s; break_and; simpl in *.
    firstorder congruence.
  - simpl.
    break_exists.
    firstorder.
Qed.

Theorem query_always_stuck_gives_chain :
  forall k ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
    live_node (occ_gst (hd ex)) h ->
    always (now (fun o => forall st,
                     sigma (occ_gst o) h = Some st ->
                     cur_request st <> None))
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
    match goal with
    | H: continuously _ _ |- _ =>
      induction H; intros; subst
    end.
    + destruct c as [|w [|w' c]];
        [simpl in * |-; tauto| |].
      * assert (w = h) by (simpl in *; tauto); subst.
        find_copy_apply_lem_hyp live_node_means_state_exists;
          break_exists_name h__st.
        destruct (cur_request h__st) as [[[dstp q] m]|] eqn:?;
            [|destruct s; repeat find_apply_lem_hyp always_now';
              simpl in *; exfalso; eauto].
        find_copy_eapply_lem_hyp eventually_done_or_always_blocked; invar_eauto.
        break_or_hyp.
        -- exfalso.
           eapply_lem_prop_hyp cumul_eventually_always False; eauto.
           repeat match goal with
                  | H: eventually (now _) _ |- _ => clear H
                  | H: context[h__st] |- _ => clear H
                  end.
           induction H3.
           ++ destruct s; firstorder eauto.
           ++ eapply IHeventually; invar_eauto.
        -- find_apply_lem_hyp always_continuously.
           break_exists_name dstp'.
           exists [addr_of dstp'; h].
           simpl; intuition eauto.
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

Theorem queries_dont_always_not_stop :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
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
  remember (length (nodes (occ_gst (hd ex)))) as k.
  find_copy_eapply_lem_hyp (query_always_stuck_gives_chain (S k)); omega || eauto.
  break_exists; break_and.
  repeat match goal with
         | H: sigma _ h = Some _ |- _ => clear H
         end.
  match goal with
  | H: continuously _ _ |- _ => induction H
  end.
  + destruct s; apply E0.
    find_apply_lem_hyp always_now'; simpl in *.
    eapply pigeon_cycle with (l := nodes (occ_gst o));
      [firstorder|eassumption|omega].
  + eapply E_next, IHeventually; invar_eauto.
    inv_prop lb_execution.
    inv_prop labeled_step_dynamic;
      simpl;
      repeat (find_rewrite || find_injection);
      auto using apply_handler_result_nodes.
Qed.

Theorem queries_eventually_stop' :
  forall ex h,
    lb_execution ex ->
    reachable_st (occ_gst (hd ex)) ->
    weak_local_fairness ex ->
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
    weak_local_fairness ex ->
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
