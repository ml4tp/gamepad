Lemma foo4 : forall A B: Prop, A -> B -> A \/ B.
Proof.
  try split; intros; auto.
Qed.

(*
Lemma foo4 : forall A B: Prop, A -> B -> A /\ B.
Proof.
  intros; split; assumption.
Qed.
*)