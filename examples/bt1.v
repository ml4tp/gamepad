Set Ltac Profiling.

Lemma foobar : forall n : nat, S (S n) = S (S n) -> S n = S n -> n = n.
Proof.
  auto.
Qed.

Lemma nat_eq_refl : forall n : nat, n = n.
Proof.
  induction n; try case n; intros; apply foobar; reflexivity.
Qed.

(* Show Ltac Profile. *)