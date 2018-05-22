Lemma foobar : forall (P Q: Prop), P /\ Q -> Q /\ P.
Proof.
  intro P.
  intro Q.
  intro H.
  split.
  destruct H.
  apply H0.
  destruct H.
  apply H.
Qed.

Lemma foobar2 : forall (P Q M: Prop), (P /\ Q) /\ M -> M /\ (P /\ Q).
Proof.
  intros.
  destruct H.
  apply foobar.
  split.
  apply H.
  apply H0.
Qed.