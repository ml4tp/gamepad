Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrnat.

Lemma foo : forall P: Prop, True /\ (P -> P).
Proof.
  intro.
  split => [| HP].
  trivial.
  trivial.
Qed.