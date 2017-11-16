Lemma plus_zero : forall n, n = n + 0.
Proof.
  induction n. {
    simpl.
    reflexivity.
  } {
    simpl.
    rewrite <- IHn.
    reflexivity.
  }
Qed.

Lemma S_comm : forall n m, S n + m = n + S m.
Proof.
  induction n. {
    simpl.
    intro.
    reflexivity.
  } {
    simpl.
    intro.
    rewrite <- IHn.
    simpl.
    reflexivity.
  }
Qed.

Lemma plus_comm : forall n m: nat, n + m = m + n.
Proof.
  induction n. {
    intro.
    simpl.
    apply plus_zero.
  } {
    intro.
    simpl.
    rewrite IHn.
    simpl.
    apply S_comm.
  }
Qed.
