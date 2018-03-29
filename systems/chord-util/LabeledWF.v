Require Import InfSeqExt.infseq.
Require Import StructTact.StructTactics.

Section wf_liveness.
  Variable T : Type.
  Variable R : T -> T -> Prop.
  Notation "t > t'" := (R t' t).
  Notation "t < t'" := (R t t').
  Variable wf : well_founded R.

  Definition stuck (t : T) : Prop :=
    forall t', t > t' -> False.

  Variable stuck_dec :
    forall t, {stuck t} + {~ stuck t}.

  Lemma eventual_drop_means_eventually_stuck :
    forall (ex: infseq T),
      ~ stuck (hd ex) ->
      always (fun s =>
                ~ stuck (hd s) ->
                eventually (now (fun t => t < (hd s))) s) ex ->
      eventually (now stuck) ex.
  Proof.
    intros until 0.
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
