Require Import mathcomp.ssreflect.ssreflect.

Lemma foobar : forall n : nat, n = n.
Proof.
  induction n. {
    have h1: 0 = 0 by auto.
    assumption.
  } {
    have h1: S n = S n by auto.
    assumption.
  }
Qed.
