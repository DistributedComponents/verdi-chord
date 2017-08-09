Require Import StructTact.StructTactics.
Require Import InfSeqExt.infseq.

(**
Given a hypothesis H of the form

    H: forall ex,
          P ex ->
          Q ex ->
          rest,

replace H with

    H: forall ex,
          (Q /\_ P) ex ->
          rest.
 *)
Ltac accum_and_tl H P Q rest ex :=
  let H' := fresh in
  rename H into H';
  assert (H: forall ex, (and_tl Q P) ex -> rest)
    by (intros; invcs_prop and_tl; auto);
  clear H'.

Ltac prep_eventually_monotonic :=
  repeat lazymatch goal with
         | [H: forall ex, ?fst ex -> ?P ex -> @?conclusion ex,
              H_P : eventually ?P ?s |- _] =>
           fail
         | H: forall ex, ?fst ex -> ?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, ?fst ex -> @?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, @?fst ex -> ?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, @?fst ex -> @?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         end.

Ltac prep_always_inv :=
  apply always_inv;
  unfold and_tl in *;
  [intros; repeat break_and; break_and_goal|tauto].

Ltac lift_eventually lem :=
  pose proof lem;
  unfold continuously in *;
  prep_eventually_monotonic;
  eapply eventually_monotonic; eauto;
  try prep_always_inv.


(* would be nice to be able to tell which possible invariant things are actually
   going to be invariants before we apply inf_often_monotonic_invar, maybe a
   typeclass would help? *)
Ltac prep_inf_often_monotonic_invar :=
  repeat lazymatch goal with
         | [H: forall ex, ?fst ex -> ?P ex -> @?conclusion ex,
              H_P : inf_often ?P ?s |- inf_often ?conclusion ?s] =>
           fail
         | H: forall ex, ?fst ex -> ?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, ?fst ex -> @?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, @?fst ex -> ?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, @?fst ex -> @?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         end.

Ltac lift_inf_often lem :=
  pose proof lem;
  prep_inf_often_monotonic_invar;
  eapply inf_often_monotonic_invar; eauto;
  try prep_always_inv.

Ltac prep_always_monotonic :=
  repeat lazymatch goal with
         (* | [H: forall ex, ?fst ex -> ?P ex -> @?conclusion ex, *)
         (*      H_P : always ?P ?s |- _] => *)
         (*   accum_and_tl H fst P (conclusion ex) ex; fail *)
         | H: forall ex, ?fst ex -> ?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, ?fst ex -> @?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, @?fst ex -> ?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         | H: forall ex, @?fst ex -> @?snd ex -> ?tl |- _ =>
           accum_and_tl H fst snd tl ex
         end.

Ltac lift_always lem :=
  pose proof lem;
  unfold inf_often in *;
  prep_always_monotonic;
  eapply always_monotonic; eauto;
  try prep_always_inv.