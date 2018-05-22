Lemma foo : forall n: nat, n + 0 = n.
Proof.
  induction n.
  solve [assumption | trivial].
  solve [simpl; trivial | simpl; rewrite IHn; trivial].
Qed.