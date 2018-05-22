Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrnat.

Lemma foo : forall n: nat, n + 0 = n.
Proof.
  intros.
  induction n.
  do 2 (try (move => n)).
  reflexivity.
  done.
Qed.