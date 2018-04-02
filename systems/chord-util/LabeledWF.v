Require Import InfSeqExt.infseq.
Require Import StructTact.StructTactics.

Definition rel (T : Type) : Type :=
  T -> T -> Prop.

Set Implicit Arguments.

Section lex.
  (* This development of the lexicographic product follows one given
    by Arthur Azevedo De Amorim on StackOverflow:
    https://stackoverflow.com/questions/42520130/lexicographical-comparison-of-tuples-of-nats#42520191
    ...which itself is an adaptation of the standard library's version
    to remove awkward sigma types. *)

  Variables (U V : Type) (R R' : rel U) (S : rel V).

  Inductive lex : rel (U * V) :=
  | LexL : forall x y x' y',
      R x x' ->
      lex (x, y) (x', y')
  | LexR : forall x y y',
      S y y' ->
      lex (x, y) (x, y').

  Lemma lex_wf :
    well_founded R ->
    well_founded S ->
    well_founded lex.
  Proof.
    unfold well_founded; intros.
    destruct a as [a b].
    generalize dependent b.
    assert (Haacc: Acc _ a) by auto.
    induction Haacc; intros b.
    assert (Hbacc: Acc _ b) by auto.
    induction Hbacc; subst.
    constructor; intros.
    inv_prop lex; eauto.
  Qed.

End lex.
(* hints don't survive sections *)
Hint Resolve lex_wf.

Definition diag {U : Type} (R : rel (U * U)) (x y : U) :=
  R (x, x) (y, y).

Definition lex_diag {U : Type} (R R' : rel U) : rel U :=
  diag (lex R R').

Lemma diag_wf :
  forall U (R : rel (U * U)),
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

Lemma lex_diag_wf :
  forall U (R S : rel U),
    well_founded R ->
    well_founded S ->
    well_founded (lex_diag R S).
Proof.
  unfold lex_diag; eauto.
Qed.
Hint Resolve lex_diag_wf.

Section wf_liveness.
  Variable T : Type.
  Variable R : T -> T -> Prop.
  Notation "t > t'" := (R t' t).
  Notation "t < t'" := (R t t').
  Variable wf : well_founded R.

  Definition stuck (t : T) : Prop :=
    forall t', t > t' -> False.

  Lemma stuck_acc :
    forall t,
      stuck t ->
      Acc R t.
  Proof using T R.
    unfold stuck.
    constructor; intros.
    exfalso; eauto.
  Qed.

  Variable stuck_dec :
    forall t, {stuck t} + {~ stuck t}.

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

Lemma lex_stuck :
  forall (U V : Type) R S (u : U) (v : V),
    stuck (lex R S) (u, v) ->
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
    constructor 2; eauto.
Qed.

Lemma lex_diag_stuck_l :
  forall (U : Type) R S (u : U),
    stuck (lex_diag R S) u -> 
    stuck R u.
Proof.
  unfold lex_diag, diag, stuck; intros.
  eapply H; constructor; eauto.
Qed.
Hint Resolve lex_diag_stuck_l.
