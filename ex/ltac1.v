Ltac hohoho := try reflexivity; simpl; reflexivity.

Lemma foobar : forall n : nat, n = n.
Proof.
  induction n; hohoho.
Qed.
  
             