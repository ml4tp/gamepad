Lemma foobar : forall n : nat, n = n.
Proof.
  induction n. {
    assert (0 = 0) as H by auto.
    assumption.
  } {
    assert (S n = S n) as H by auto.
    assumption.
  }
Qed.