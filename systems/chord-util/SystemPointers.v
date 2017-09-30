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
Require Import Chord.SystemLemmas.

Notation hash := Chord.hash.

Definition wf_ptr (p : pointer) : Prop :=
  id_of p = hash (addr_of p).

Definition wf_ptr_dec :
  forall p,
    {wf_ptr p} + {~ wf_ptr p}.
Proof.
  unfold wf_ptr; intros.
  exact (id_eq_dec (id_of p) (hash (addr_of p))).
Defined.

Lemma wf_ptr_eq :
  forall p,
    wf_ptr p ->
    p = make_pointer (addr_of p).
Proof.
  unfold wf_ptr, make_pointer, id_of, addr_of.
  intros; destruct p.
  simpl in *; subst.
  reflexivity.
Qed.

Definition valid_ptr (gst : global_state) (p : pointer) : Prop :=
  wf_ptr p /\
  In (addr_of p) (nodes gst).

Lemma valid_ptr_intro :
  forall gst p,
    id_of p = hash (addr_of p) ->
    In (addr_of p) (nodes gst) ->
    valid_ptr gst p.
Proof using.
  easy.
Qed.

Lemma valid_ptr_elim :
  forall gst p,
    valid_ptr gst p ->
    id_of p = hash (addr_of p) /\
    In (addr_of p) (nodes gst).
Proof using.
  unfold valid_ptr.
  easy.
Qed.

Lemma valid_ptr_elim_hash :
  forall gst p,
    valid_ptr gst p ->
    id_of p = hash (addr_of p).
Proof using.
  unfold valid_ptr.
  easy.
Qed.

Lemma valid_ptr_elim_nodes :
  forall gst p,
    valid_ptr gst p ->
    In (addr_of p) (nodes gst).
Proof using.
  unfold valid_ptr.
  easy.
Qed.

Lemma valid_ptr_nodes_subset :
  forall gst gst' p,
    valid_ptr gst p ->
    (forall n, In n (nodes gst) -> In n (nodes gst')) ->
    valid_ptr gst' p.
Proof using.
  unfold valid_ptr.
  intuition.
Qed.

Lemma valid_ptr_nodes :
  forall gst gst' p,
    nodes gst = nodes gst' ->
    valid_ptr gst p ->
    valid_ptr gst' p.
Proof using.
  intros.
  eapply valid_ptr_nodes_subset; eauto.
  now find_rewrite.
Qed.

Lemma make_pointer_valid :
  forall a,
    id_of (make_pointer a) = hash (addr_of (make_pointer a)).
Proof using.
  now unfold make_pointer.
Qed.

Definition valid_ptr_list (gst : global_state) (ps : list pointer) :=
  Forall (valid_ptr gst) ps.

Lemma valid_ptr_list_nodes_subset :
  forall gst gst' ps,
    valid_ptr_list gst ps ->
    (forall n, In n (nodes gst) -> In n (nodes gst')) ->
    valid_ptr_list gst' ps.
Proof using.
  intros.
  apply Forall_forall.
  intros.
  eapply valid_ptr_nodes_subset; eauto.
  find_eapply_lem_hyp Forall_forall; eauto.
Qed.

Lemma valid_ptr_list_nodes :
  forall gst gst' ps,
    nodes gst = nodes gst' ->
    valid_ptr_list gst ps ->
    valid_ptr_list gst' ps.
Proof using.
  intros.
  eapply valid_ptr_list_nodes_subset; eauto.
  now find_rewrite.
Qed.

Inductive lift_pred_opt {A} (P : A -> Prop) : option A -> Prop :=
| LiftPredOptSome : forall a, P a -> lift_pred_opt P (Some a)
| LiftPredOptNone : lift_pred_opt P None.

Ltac inv_lift_pred_opt :=
  match goal with
  | [ H: lift_pred_opt _ _ |- _ ] => inv H
  end.

Lemma lift_pred_opt_elim :
  forall A (P : A -> Prop) o,
    lift_pred_opt P o ->
    (exists a, o = Some a /\ P a) \/
    o = None.
Proof using.
  intros.
  inv H; [left | right]; eexists; eauto.
Qed.

Definition valid_opt_ptr (gst : global_state) : option pointer -> Prop :=
  lift_pred_opt (valid_ptr gst).

Lemma valid_opt_ptr_elim :
  forall gst o,
    valid_opt_ptr gst o ->
    (exists p, o = Some p /\ valid_ptr gst p) \/
    o = None.
Proof using.
  eauto using lift_pred_opt_elim.
Qed.

Inductive valid_ptr_payload (gst : global_state) : payload -> Prop :=
| VPBusy : valid_ptr_payload gst Busy
| VPGetBestPredecessor : forall p,
    valid_ptr gst p ->
    valid_ptr_payload gst (GetBestPredecessor p)
| VPGotBestPredecessor : forall p,
    valid_ptr gst p ->
    valid_ptr_payload gst (GotBestPredecessor p)
| VPGetSuccList : valid_ptr_payload gst GetSuccList
| VPGotSuccList : forall ps,
    valid_ptr_list gst ps ->
    valid_ptr_payload gst (GotSuccList ps)
| VPGetPredAndSuccs : valid_ptr_payload gst GetPredAndSuccs
| VPGotPredAndSuccs : forall p ps,
    valid_opt_ptr gst p ->
    valid_ptr_list gst ps ->
    valid_ptr_payload gst (GotPredAndSuccs p ps)
| VPNotify : valid_ptr_payload gst Notify
| VPPing : valid_ptr_payload gst Ping
| VPPong : valid_ptr_payload gst Pong.

Ltac inv_vpp :=
  match goal with
  | [ H: valid_ptr_payload _ _ |- _ ] => inv H
  end.

Inductive valid_ptr_query (gst : global_state) : query -> Prop :=
| VPQRectify : forall p, valid_ptr gst p -> valid_ptr_query gst (Rectify p)
| VPQStabilize : valid_ptr_query gst Stabilize
| VPQStabilize2 : forall p, valid_ptr gst p -> valid_ptr_query gst (Stabilize2 p)
| VPQJoin : forall p, valid_ptr gst p -> valid_ptr_query gst (Join p)
| VPQJoin2 : forall p, valid_ptr gst p -> valid_ptr_query gst (Join2 p).

Definition valid_ptrs_some_cur_request (gst : global_state) (t : pointer * query * payload) : Prop :=
  let '(p, q, m) := t in
  valid_ptr gst p /\
  valid_ptr_query gst q /\
  valid_ptr_payload gst m.

Lemma valid_ptrs_some_cur_request_intro :
  forall gst p q m,
    valid_ptr gst p ->
    valid_ptr_query gst q ->
    valid_ptr_payload gst m ->
    valid_ptrs_some_cur_request gst (p, q, m).
Proof using.
  easy.
Qed.

Lemma valid_ptrs_some_cur_request_elim :
  forall gst p q m,
    valid_ptrs_some_cur_request gst (p, q, m) ->
    valid_ptr gst p /\
    valid_ptr_query gst q /\
    valid_ptr_payload gst m.
Proof using.
  easy.
Qed.

Lemma valid_ptrs_some_cur_request_elim_p :
  forall gst p q m,
    valid_ptrs_some_cur_request gst (p, q, m) ->
    valid_ptr gst p.
Proof using.
  unfold valid_ptrs_some_cur_request.
  easy.
Qed.

Lemma valid_ptrs_some_cur_request_elim_q :
  forall gst p q m,
    valid_ptrs_some_cur_request gst (p, q, m) ->
    valid_ptr_query gst q.
Proof using.
  unfold valid_ptrs_some_cur_request.
  easy.
Qed.

Lemma valid_ptrs_some_cur_request_elim_m :
  forall gst p q m,
    valid_ptrs_some_cur_request gst (p, q, m) ->
    valid_ptr_payload gst m.
Proof using.
  unfold valid_ptrs_some_cur_request.
  easy.
Qed.

Definition valid_ptrs_cur_request (gst : global_state) : option (pointer * query * payload) -> Prop :=
  lift_pred_opt (valid_ptrs_some_cur_request gst).

Definition valid_ptrs_state (gst : global_state) (d : data) :=
  valid_ptr gst (ptr d) /\
  valid_opt_ptr gst (pred d) /\
  Forall (valid_ptr gst) (succ_list d) /\
  valid_ptr gst (known d) /\
  valid_opt_ptr gst (rectify_with d) /\
  valid_ptrs_cur_request gst (cur_request d).

Lemma valid_ptrs_state_elim :
  forall gst d,
    valid_ptrs_state gst d ->
    valid_ptr gst (ptr d) /\
    valid_opt_ptr gst (pred d) /\
    Forall (valid_ptr gst) (succ_list d) /\
    valid_ptr gst (known d) /\
    valid_opt_ptr gst (rectify_with d) /\
    valid_ptrs_cur_request gst (cur_request d).
Proof using.
  unfold valid_ptrs_state.
  tauto.
Qed.

Lemma valid_ptrs_state_intro :
  forall gst d,
    valid_ptr gst (ptr d) ->
    valid_opt_ptr gst (pred d) ->
    Forall (valid_ptr gst) (succ_list d) ->
    valid_ptr gst (known d) ->
    valid_opt_ptr gst (rectify_with d) ->
    valid_ptrs_cur_request gst (cur_request d) ->
    valid_ptrs_state gst d.
Proof.
  unfold valid_ptrs_state.
  tauto.
Qed.

Definition valid_ptrs_net (gst : global_state) : Prop :=
  forall src dst p,
    In (src, (dst, p)) (msgs gst) ->
    valid_ptr_payload gst p.

Lemma valid_ptrs_net_elim_snd_snd :
  forall gst m,
    valid_ptrs_net gst ->
    In m (msgs gst) ->
    valid_ptr_payload gst (snd (snd m)).
Proof using.
  unfold valid_ptrs_net.
  intros.
  destruct m.
  destruct p.
  eauto.
Qed.

Inductive valid_ptr_timeout (gst : global_state) : timeout -> Prop :=
| VPTRequest : forall h p, valid_ptr_payload gst p -> valid_ptr_timeout gst (Request h p)
| VPTick : valid_ptr_timeout gst Tick
| VPTKeepaliveTick : valid_ptr_timeout gst KeepaliveTick.

Ltac inv_vpt :=
  match goal with
  | [ H: valid_ptr_timeout _ _ |- _ ] => inv H
  end.

Definition valid_ptrs_timeouts (gst : global_state) (ts : list timeout) : Prop :=
  Forall (valid_ptr_timeout gst) ts.

Lemma valid_ptrs_timeouts_intro :
  forall gst h,
    (forall t, In t (timeouts gst h) -> valid_ptr_timeout gst t) ->
    valid_ptrs_timeouts gst (timeouts gst h).
Proof using.
  intros.
  now apply Forall_forall.
Qed.

Lemma valid_ptrs_timeouts_elim :
  forall gst h,
    valid_ptrs_timeouts gst (timeouts gst h) ->
    forall t,
      In t (timeouts gst h) ->
      valid_ptr_timeout gst t.
Proof using.
  unfold valid_ptrs_timeouts.
  intros until 1.
  now apply Forall_forall.
Qed.

Inductive valid_ptr_event (gst : global_state) : event -> Prop :=
| VPEsend : forall src dst p, valid_ptr_payload gst p -> valid_ptr_event gst (e_send (src, (dst, p)))
| VPErecv : forall src dst p, valid_ptr_payload gst p -> valid_ptr_event gst (e_recv (src, (dst, p)))
| VPEtimeout : forall h t, valid_ptr_timeout gst t -> valid_ptr_event gst (e_timeout h t)
| VPEfail : forall h, valid_ptr_event gst (e_fail h).

Definition valid_ptrs_trace (gst : global_state) : Prop :=
  Forall (valid_ptr_event gst) (trace gst).

Lemma valid_ptrs_trace_intro :
  forall gst,
    (forall e, In e (trace gst) -> valid_ptr_event gst e) ->
    valid_ptrs_trace gst.
Proof using.
  intros.
  now apply Forall_forall.
Qed.

Definition valid_ptrs_global (gst : global_state) : Prop :=
  (forall h, valid_ptrs_timeouts gst (timeouts gst h)) /\
  (forall h, lift_pred_opt (valid_ptrs_state gst) (sigma gst h)) /\
  valid_ptrs_net gst /\
  valid_ptrs_trace gst.

Lemma valid_ptrs_global_elim :
  forall gst,
    valid_ptrs_global gst ->
    (forall h, valid_ptrs_timeouts gst (timeouts gst h)) /\
    (forall h, lift_pred_opt (valid_ptrs_state gst) (sigma gst h)) /\
    valid_ptrs_net gst /\
    valid_ptrs_trace gst.
Proof using.
  auto.
Qed.

Lemma valid_ptrs_global_intro :
  forall gst,
    (forall h, valid_ptrs_timeouts gst (timeouts gst h)) ->
    (forall h, lift_pred_opt (valid_ptrs_state gst) (sigma gst h)) ->
    valid_ptrs_net gst ->
    valid_ptrs_trace gst ->
    valid_ptrs_global gst.
Proof using.
  unfold valid_ptrs_global.
  tauto.
Qed.

Ltac copy_elim_valid_ptrs_global :=
  match goal with
  | [ H : valid_ptrs_global _ |- _ ] =>
    copy_apply valid_ptrs_global_elim H;
    break_and
  end.

Lemma valid_opt_ptr_nodes_subset :
  forall gst gst' o,
    valid_opt_ptr gst o ->
    (forall n, In n (nodes gst) -> In n (nodes gst')) ->
    valid_opt_ptr gst' o.
Proof using.
  intros.
  find_eapply_lem_hyp valid_opt_ptr_elim.
  break_or_hyp; try constructor.
  break_exists; break_and; subst_max.
  constructor.
  eauto using valid_ptr_nodes_subset.
Qed.

Lemma valid_opt_ptr_nodes :
  forall gst gst' o,
    nodes gst = nodes gst' ->
    valid_opt_ptr gst o ->
    valid_opt_ptr gst' o.
Proof using.
  intros.
  eapply valid_opt_ptr_nodes_subset; eauto.
  now find_rewrite.
Qed.

Lemma valid_ptr_payload_nodes_subset :
  forall gst gst' p,
    valid_ptr_payload gst p ->
    (forall n, In n (nodes gst) -> In n (nodes gst')) ->
    valid_ptr_payload gst' p.
Proof using.
  intros.
  inv_vpp; constructor;
    eauto using valid_ptr_nodes_subset, valid_ptr_list_nodes_subset, valid_opt_ptr_nodes_subset.
Qed.

Lemma valid_ptr_payload_nodes :
  forall gst gst' p,
    nodes gst = nodes gst' ->
    valid_ptr_payload gst p ->
    valid_ptr_payload gst' p.
Proof using.
  intros.
  eapply valid_ptr_payload_nodes_subset; eauto.
  now find_rewrite.
Qed.

Lemma valid_ptr_timeout_nodes :
  forall gst gst' t,
    valid_ptr_timeout gst t ->
    nodes gst = nodes gst' ->
    valid_ptr_timeout gst' t.
Proof using.
  intros.
  inv_vpt.
  - constructor.
    eauto using valid_ptr_payload_nodes.
  - constructor.
  - constructor.
Qed.

Lemma valid_ptrs_timeouts_nodes_subset_timeouts :
  forall gst gst' h,
    valid_ptrs_timeouts gst (timeouts gst h) ->
    timeouts gst = timeouts gst' ->
    nodes gst = nodes gst' ->
    valid_ptrs_timeouts gst' (timeouts gst' h).
Abort.

Lemma valid_ptrs_timeouts_nodes_timeouts :
  forall gst gst' h,
    valid_ptrs_timeouts gst (timeouts gst h) ->
    timeouts gst = timeouts gst' ->
    nodes gst = nodes gst' ->
    valid_ptrs_timeouts gst' (timeouts gst' h).
Proof using.
  intros.
  apply valid_ptrs_timeouts_intro; intros.
  eapply valid_ptr_timeout_nodes; eauto.
  eapply valid_ptrs_timeouts_elim; eauto.
  now repeat find_rewrite.
Qed.

Lemma valid_ptr_timeout_preserved :
  forall gst gst' t,
    valid_ptr_timeout gst t ->
    (forall n,
        In n (nodes gst) ->
        In n (nodes gst)) ->
    (forall t h,
        In t (timeouts gst' h) ->
        In t (timeouts gst h) \/
        valid_ptr_timeout gst' t) ->
    valid_ptr_timeout gst' t.
Abort.

Lemma valid_ptrs_timeouts_preserved :
  forall gst gst' h,
    valid_ptrs_timeouts gst (timeouts gst h) ->
    (forall t,
        In t (timeouts gst' h) ->
        In t (timeouts gst h) \/
        valid_ptr_timeout gst' t) ->
    (forall n,
        In n (nodes gst) ->
        In n (nodes gst')) ->
    valid_ptrs_timeouts gst' (timeouts gst' h).
Proof using.
  intros.
  apply valid_ptrs_timeouts_intro; intros.
  find_apply_hyp_hyp; break_or_hyp.
  - find_copy_eapply_lem_hyp valid_ptrs_timeouts_elim; eauto.
    match goal with
    | [ H: valid_ptr_timeout _ _ |- _ ] => inv H
    end; constructor.
    eapply valid_ptr_payload_nodes_subset; eauto.
  - easy.
Qed.

Lemma valid_ptrs_global_timeout_handler :
  forall gst h st t st' ms nts cts t0,
    valid_ptrs_global gst ->
    timeout_handler h st t = (st', ms, nts, cts) ->
    In t0 nts ->
    valid_ptr_timeout gst t0.
Proof using.
  intros.
  destruct t0; try constructor.
  - Fail constructor. (* missing RectifyTick case in valid_ptr_timeout *)
    admit.
  - (* need to dissect timeout_handler here *)
    admit.
(*
This proof is a grind through the definition of timeout_handler. It might not go
through until definition of valid_ptr_timeout gets fixed. (It's missing a case
for RectifyTick.)

DIFFICULTY: 2
USED: In ValidPointersInvariant.v for an invariant.
*)
Admitted.

Lemma lift_pred_opt_Some_elim :
  forall A x (P : A -> Prop) a,
    lift_pred_opt P x ->
    x = Some a ->
    P a.
Proof using.
  intros.
  match type of H with
  | lift_pred_opt _ _ => inv H
  end; congruence.
Qed.

Lemma valid_ptrs_global_recv_handler :
  forall gst xs m ys d st ms newts clearedts,
    valid_ptrs_global gst ->
    msgs gst = xs ++ m :: ys ->
    In (fst (snd m)) (nodes gst) ->
    ~ In (fst (snd m)) (failed_nodes gst) ->
    sigma gst (fst (snd m)) = Some d ->
    recv_handler (fst m) (fst (snd m)) d (snd (snd m)) = (st, ms, newts, clearedts) ->
    forall t, In t newts ->
         valid_ptr_timeout gst t.
Proof using.
(*
This proof is a grind through the definition of recv_handler.

DIFFICULTY: 2
USED: In valid_ptrs_global_timeouts below.
*)
Admitted.

Lemma apply_handler_result_In_timeouts :
  forall t h0 h st ms nts cts e gst,
    In t (timeouts (apply_handler_result h0 (st, ms, nts, cts) e gst) h) ->
    In t nts \/
    In t (timeouts gst h) /\ (~ In t cts \/ h <> h0).
Proof using.
(*
This is a simple spec lemma for apply_handler_result. The proof should be very
simple.

DIFFICULTY: 1
USED: In valid_ptrs_global_timeouts below
*)
Admitted.

Lemma valid_ptrs_global_timeouts :
  forall gst gst',
    valid_ptrs_global gst ->
    step_dynamic gst gst' ->
    forall h,
      valid_ptrs_timeouts gst' (timeouts gst' h).
Proof using.
  intros.
  copy_elim_valid_ptrs_global.
  break_step.
  - apply valid_ptrs_timeouts_intro; intros.
    unfold update_for_start in *.
    repeat break_let.
    simpl in *.
    admit.
    (*
    tuple_inversion.
    simpl in *.
    destruct t; constructor.
    destruct (addr_eq_dec h h0).
    + find_erewrite_lem update_eq.
      find_apply_lem_hyp in_inv.
      break_or_hyp.
      * find_inversion.
        constructor.
        (* question: can I make this eauto not work? *)
        apply valid_ptr_intro; simpl; eauto.
      * exfalso; auto using in_nil.
    + find_erewrite_lem update_diff.
      find_apply_lem_hyp valid_ptrs_global_elim.
      break_and.
      find_apply_lem_hyp valid_ptrs_timeouts_elim; eauto.
      match goal with
      | [H: valid_ptr_timeout _ (Request _ _) |- _] =>
        inv H; subst_max
      end.
      eapply valid_ptr_payload_nodes_subset; simpl; eauto.
    *)
  - eauto using valid_ptrs_timeouts_nodes_timeouts.
  - apply valid_ptrs_timeouts_intro; intros.
    eapply valid_ptr_timeout_nodes;
      try eapply apply_handler_result_preserves_nodes; eauto.
    find_apply_lem_hyp apply_handler_result_In_timeouts;
      repeat (break_and || break_or_hyp);
      eauto using valid_ptrs_global_timeout_handler,
      valid_ptr_timeout_nodes,
      valid_ptrs_timeouts_elim.
  - apply valid_ptrs_timeouts_intro; intros.
    eapply valid_ptr_timeout_nodes;
      try eapply apply_handler_result_preserves_nodes; eauto.
    find_apply_lem_hyp apply_handler_result_In_timeouts;
      repeat (break_and || break_or_hyp);
      eauto using valid_ptrs_global_recv_handler,
      valid_ptr_timeout_nodes,
      valid_ptrs_timeouts_elim.
  - admit.
  - admit.
(*
I need to clean this up.

DIFFICULTY: Ryan.
USED: In ValidPointersInvariant.v for one case of an inductive invariant proof.
*)
Admitted.

Lemma valid_ptrs_global_sigma :
  forall gst gst',
    valid_ptrs_global gst ->
    step_dynamic gst gst' ->
    forall h d,
      sigma gst' h = Some d ->
      valid_ptrs_state gst' d.
Proof using.
  intros.
  break_step.
  - admit.
  - admit.
  - admit.
  - admit.
(*
I need to break this out into smaller admits.

DIFFICULTY: Ryan.
USED: In ValidPointersInvariant.v for one case of an inductive invariant proof.
*)
Admitted.

Lemma valid_ptrs_global_net :
  forall gst gst',
    valid_ptrs_global gst ->
    step_dynamic gst gst' ->
    valid_ptrs_net gst'.
Proof using.
  intros.
  break_step.
  - admit.
  - admit.
  - admit.
  - admit.
(*
I need to break this out into smaller admits.

DIFFICULTY: Ryan.
USED: In ValidPointersInvariant.v for one case of an inductive invariant proof.
*)
Admitted.

Lemma valid_ptrs_global_trace :
  forall gst gst',
    valid_ptrs_global gst ->
    step_dynamic gst gst' ->
    valid_ptrs_trace gst'.
Proof using.
  intros.
  break_step.
  - admit.
  - admit.
  - admit.
  - admit.
(*
I need to break this out into smaller admits.

DIFFICULTY: Ryan.
USED: In ValidPointersInvariant.v for one case of an inductive invariant proof.
*)
Admitted.

Lemma valid_ptrs_state_nodes_subset :
  forall gst gst' d,
    valid_ptrs_state gst d ->
    (forall n, In n (nodes gst) -> In n (nodes gst')) ->
    valid_ptrs_state gst' d.
Proof.
  intros.
  apply valid_ptrs_state_intro;
    find_apply_lem_hyp valid_ptrs_state_elim;
    break_and.
(*
This follows from valid_ptr_nodes_subset.

DIFFICULTY: 2
USED: In ValidPointersInvariant.v
*)
Admitted.

Lemma start_handler_valid_ptrs_state :
  forall gst gst' h k st ms nts,
    start_handler h [k] = (st, ms, nts) ->
    In k (nodes gst) ->
    In h (nodes gst') ->
    (forall n, In n (nodes gst) -> In n (nodes gst')) ->
    valid_ptrs_state gst' st.
Proof.
  intros.
(*
This follows from valid_ptr_nodes_subset.

DIFFICULTY: 2
USED: In ValidPointersInvariant.v
*)
Admitted.
(*
  find_apply_lem_hyp start_handler_definition; expand_def.
  assert (valid_ptr gst' (make_pointer k)) by (split; auto).
  find_apply_lem_hyp start_query_definition; expand_def; simpl in *.
  - find_inversion.
    apply valid_ptrs_state_intro;
      repeat (try constructor; try split; simpl; auto).
  - find_inversion.
    discriminate.
Qed.
*)

Lemma live_In_live_ptrs :
  forall gst h,
    live_node gst (addr_of h) ->
    wf_ptr h ->
    In h (live_ptrs gst).
Proof.
  unfold live_ptrs, live_node.
  intros.
  destruct (start_handler _ _) as [[?st ?ms] ?newts] eqn:?H; subst res0.
  find_eapply_lem_hyp update_for_start_definition; expand_def.
  find_copy_eapply_lem_hyp valid_ptrs_global_elim; break_and.
  apply valid_ptrs_global_intro; try intro h'; intros; subst_max.
  - eapply valid_ptrs_timeouts_preserved; eauto.
    + intros.
      simpl in *.
      admit.
      (*
      match goal with
      | [H: context[Request ?k ?m] |- _] =>
        destruct (addr_eq_dec h h'), (timeout_eq_dec t (Request k m)); subst
      end.
      * right.
        do 2 constructor.
        apply valid_ptr_intro.
        -- apply make_pointer_valid.
        -- repeat find_rewrite.
           simpl; tauto.
      * exfalso.
        tuple_inversion.
        repeat find_rewrite.
        find_rewrite_lem update_same.
        find_eapply_lem_hyp in_inv.
        break_or_hyp; auto.
      * repeat find_rewrite.
        find_erewrite_lem update_diff.
        tauto.
      * repeat find_rewrite.
        find_erewrite_lem update_diff.
        tauto.
      *)
    + intros.
      repeat find_rewrite.
      auto with datatypes.
  - destruct (addr_eq_dec h h'); subst.
    + destruct (sigma _ _) as [a |] eqn:?H; constructor.
      * repeat find_rewrite.
        find_rewrite_lem update_same.
        find_injection.
        eapply start_handler_valid_ptrs_state; eauto;
        repeat find_rewrite; intuition.
    + repeat find_rewrite.
      rewrite update_diff; auto.
      match goal with
      | [H: context[lift_pred_opt] |- _] =>
        pose proof (H h')
      end.
      find_apply_lem_hyp lift_pred_opt_elim;
        break_or_hyp; try break_exists; break_and.
      * repeat find_rewrite.
        constructor.
        eapply valid_ptrs_state_nodes_subset; eauto.
        find_rewrite.
        intros; auto with datatypes.
      * admit.
  - admit. (* net case *)
  - admit. (* trace case *)
Admitted.

Lemma wf_ptr_hash_eq :
  forall p,
    wf_ptr p ->
    hash (addr_of p) = id_of p.
Proof.
  auto.
Qed.

Lemma make_pointer_wf :
  forall h,
    wf_ptr (make_pointer h).
Proof.
  constructor.
Qed.
