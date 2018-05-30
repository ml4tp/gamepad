Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrnat.

Lemma split_pat : forall P: Prop, True /\ (P -> P).
Proof.
  intro.
  split => [| HP].
  trivial.
  trivial.
Qed.

Lemma case_split : forall (P Q M: Prop), (P \/ Q) -> M -> (Q /\ M) \/ (P /\ M).
Proof.
  intros.
  case H => [hP | hQ].
  right. split; trivial.
  left. split; trivial.
Qed.

