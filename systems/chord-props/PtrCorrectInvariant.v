Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.Update.

Require Import Chord.Chord.

Require Import Chord.SystemReachable.

Set Bullet Behavior "Strict Subproofs".


Lemma sigma_apply_handler_result_same :
  forall h res es gst,
    sigma (apply_handler_result h res es gst) h =
    Some (fst (fst (fst res))).
Proof.
  intros. unfold apply_handler_result.
  repeat break_match. subst. simpl.
  now rewrite_update.
Qed.

Lemma sigma_apply_handler_result_diff :
  forall h h' res es gst,
    h <> h' ->
    sigma (apply_handler_result h res es gst) h' =
    sigma gst h'.
Proof.
  intros. unfold apply_handler_result.
  repeat break_match. subst. simpl.
  now rewrite_update.
Qed.

Lemma initial_nodes_ptr_correct:
  forall l h init,
    sigma (fold_left run_init_for l init) h = sigma (run_init_for init h) h \/
    sigma (fold_left run_init_for l init) h = sigma init h.
Proof.
  induction l; intros; simpl in *; auto.
  specialize (IHl h (run_init_for init a)).
  intuition.
  - repeat find_rewrite.
    unfold run_init_for.
    repeat rewrite sigma_apply_handler_result_same. auto.
  - repeat find_rewrite. unfold run_init_for.
    destruct (addr_eq_dec a h); subst.
    + repeat rewrite sigma_apply_handler_result_same. auto.
    + rewrite sigma_apply_handler_result_diff; auto.
Qed.

Lemma initial_nodes_ptr_correct_Some :
  forall (h : addr) (st : data) l init,
    sigma (fold_left run_init_for l init) h = Some st ->
    sigma init h = None ->
    Some st = sigma (run_init_for init h) h.
Proof.
  intros.
  pose proof (initial_nodes_ptr_correct l h init).
  intuition congruence.
Qed.
  
Lemma ptr_correct :
  forall gst h st,
    reachable_st gst ->
    sigma gst h = Some st ->
    ptr st = make_pointer h.
Proof.
  intros. induct_reachable_st.
  - intros.
    unfold initial_st in *.
    find_apply_lem_hyp initial_nodes_ptr_correct_Some; simpl in *; auto.
    unfold run_init_for in *. simpl in *.
    repeat break_match. subst. simpl in *.
    rewrite_update. find_inversion.
    unfold start_handler in *. repeat break_match.
    + unfold empty_start_res in *.
      find_inversion. auto.
    + unfold start_query in *.
      repeat break_match; subst; simpl in *;
        find_inversion; auto.
    + find_inversion. auto.
  -

(*
This is a very good and easy invariant.  At a node h, ptr st is a copy
of a pointer to h. It's set when the node starts up and never changed
anywhere.

DIFFICULTY: 1
USED: In phase two.
*)
Admitted.
