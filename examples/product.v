Lemma foobar : forall x y: nat, let (a, b) := (x + y, x - y) in
                                a = x + y /\ b = x - y.
Proof.
  intros.
  simpl.
  auto.
Qed.

Lemma foobar' : forall x y: nat, let z := (x + y, x - y) in
                                 fst z = x + y /\ snd z = x - y.
Proof.
  intros.
  simpl.
  auto.
Qed.

Lemma foobar'' : forall x y: nat, let '(a, b, c) := (x + y, x - y, x) in
                                  a = x + y /\ b = x - y /\ c = x.
Proof.
  intros.
  simpl.
  auto.
Qed.