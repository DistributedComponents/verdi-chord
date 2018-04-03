Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationPairs.

Require Import InfSeqExt.infseq.
Require Import StructTact.StructTactics.

Set Implicit Arguments.

Section wf_liveness.
  Variables (T : Type) (R : relation T).
  Notation "t > t'" := (R t' t).
  Notation "t < t'" := (R t t').
  Variable wf : well_founded R.

  Definition stuck (t : T) : Prop :=
    forall t', t > t' -> False.

  Variable stuck_dec :
    forall t, {stuck t} + {~ stuck t}.

  Lemma stuck_acc :
    forall t,
      stuck t ->
      Acc R t.
  Proof using T R.
    unfold stuck.
    constructor; intros.
    exfalso; eauto.
  Qed.

  Lemma eventual_drop_means_eventually_stuck :
    forall ex,
      always (fun s =>
                ~ stuck (hd s) ->
                eventually (now (fun t => t < (hd s))) s) ex ->
      eventually (now stuck) ex.
  Proof.
    intros until 0.
    destruct (stuck_dec (hd ex));
      [destruct ex; constructor; eauto|].
    pose proof (wf (hd ex)) as w.
    remember (hd ex) as e.
    generalize dependent ex.
    induction w; intros; subst.
    assert (eventually (now (fun t => t < hd ex)) ex)
      by (find_apply_lem_hyp always_now'; eauto).
    match goal with
    | H: always _ _ |- _ => revert H
    end.
    induction 0.
    - destruct s as [o s].
      destruct (stuck_dec o);
        [constructor; eauto|].
      destruct s; simpl in *.
      eapply H0; eauto.
    - intros.
      destruct (stuck_dec x);
        [constructor; eauto|].
      apply E_next.
      eapply IHeventually; eauto using always_invar.
  Qed.

End wf_liveness.
Hint Resolve stuck_acc.

Definition diag {U : Type} (R : relation (U * U)) : relation U :=
  fun x y => R (x, x) (y, y).

Lemma diag_wf :
  forall U (R : relation (U * U)),
    well_founded R ->
    well_founded (diag R).
Proof.
  unfold well_founded; intros.
  assert (Hacc: Acc R (a, a)) by auto.
  remember (a, a) as da.
  generalize dependent a.
  induction Hacc; intros; subst.
  constructor; eauto.
Qed.
Hint Resolve diag_wf.

Section lex.
  (* This development of the lexicographic product follows one given
    by Arthur Azevedo De Amorim on StackOverflow:
    https://stackoverflow.com/questions/42520130/lexicographical-comparison-of-tuples-of-nats#42520191
    ...which itself is an adaptation of the standard library's version
    to remove awkward sigma types. *)

  Variables (U V : Type) (equiv R : relation U) (S : relation V).
  Context `{Eq: Equivalence U equiv}.
  Context `{R_compat : Proper _ (equiv ==> equiv ==> iff) R}.

  Notation "a ~= b" := (equiv a b) (at level 50).

  Inductive lex : relation (U * V) :=
  | LexL : forall x y x' y',
      R x x' ->
      lex (x, y) (x', y')
  | LexR : forall x x' y y',
      S y y' ->
      x ~= x' ->
      lex (x, y) (x', y').

  Lemma acc_R_equiv :
    forall x x',
      Acc R x ->
      x ~= x' ->
      Acc R x'.
  Proof using Eq R_compat.
    constructor; intros.
    inv_prop Acc; eauto.
    eapply H2.
    eapply R_compat; eauto using Equivalence_Reflexive.
  Qed.
  Hint Resolve acc_R_equiv.

  Ltac rewriter_goal :=
    match goal with
    | H: _ |- _ =>
      rewrite -> H
    end.

  Ltac rewritel_goal :=
    match goal with
    | H: _ |- _ =>
      rewrite <- H
    end.

  Lemma lex_properL :
    forall x y x' b,
      lex (x, y) b ->
      x ~= x' ->
      lex (x', y) b.
  Proof using Eq R_compat.
    intros.
    inv_prop lex.
    - constructor.
      eapply R_compat;
        eauto; eauto with relations.
    - constructor 2; eauto.
      repeat rewritel_goal;
        reflexivity.
  Qed.
  Hint Resolve lex_properL.

  Lemma lex_properR :
    forall x y x' b,
      lex b (x, y) ->
      x ~= x' ->
      lex b (x', y).
  Proof using Eq R_compat.
    intros.
    inv_prop lex.
    - constructor.
      now repeat rewritel_goal.
    - constructor 2; eauto using Equivalence_Transitive. 
  Qed.
  Hint Resolve lex_properR.

  Instance lex_proper :
    Proper (equiv * eq ==> equiv * eq ==> iff) lex.
  Proof.
    unfold Proper.
    repeat intro.
    destruct x, y, x0, y0; cbv in *.
    break_and; subst.
    split; eauto with relations.
  Qed.

  Lemma lex_acc_proper :
    forall x x' y,
      Acc lex (x, y) ->
      x ~= x' ->
      Acc lex (x', y).
  Proof using Eq R_compat.
    intros.
    constructor; intros.
    inv_prop Acc.
    inv_prop lex;
      eauto with relations.
  Qed.
  Hint Resolve lex_acc_proper.

  Lemma lex_wf :
    well_founded R ->
    well_founded S ->
    well_founded lex.
  Proof using Eq R_compat.
    unfold well_founded; intros.
    destruct a as [a b]; revert b.
    assert (Haacc: Acc _ a) by auto.
    induction Haacc; intros b.
    assert (Hbacc: Acc _ b) by auto.
    induction Hbacc; subst.
    constructor; intros.
    inv_prop lex; eauto with relations.
  Qed.

  Lemma lex_stuck :
    forall u v,
      stuck lex (u, v) ->
      stuck R u /\
      stuck S v.
  Proof.
    unfold stuck.
    intros.
    split.
    - intros.
      eapply (H (t', v)).
      constructor; eauto.
    - intros.
      eapply (H (u, t')).
      constructor 2;
        eauto with relations.
  Qed.

End lex.
Hint Resolve lex_acc_proper.
Hint Resolve lex_wf.
Hint Resolve lex_stuck.

Section lex_diag.
  Variables (U : Type) (equiv R S : relation U).
  Context `{Eq: Equivalence U equiv}.
  Context `{R_compat : Proper _ (equiv ==> equiv ==> iff) R}.

  Definition lex_diag : relation U :=
    diag (lex equiv R S).

  Lemma lex_diag_wf :
    well_founded R ->
    well_founded S ->
    well_founded lex_diag.
  Proof using Eq R_compat.
    unfold lex_diag;
      eauto with relations.
  Qed.
  Hint Resolve lex_diag_wf.

  Lemma lex_diag_stuck_l :
    forall u,
      stuck lex_diag u -> 
      stuck R u.
  Proof.
    unfold lex_diag, diag, stuck; intros.
    eapply H; constructor; eauto.
  Qed.
  Hint Resolve lex_diag_stuck_l.

End lex_diag.
Hint Resolve lex_diag_wf.
Hint Resolve lex_diag_stuck_l.
