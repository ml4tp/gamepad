Lemma foo4 : forall A B: Prop, A -> B -> A \/ B.
Proof.
  try split; intro; intro; try assumption; auto.
Qed.

(*
Lemma foo4 : forall A B: Prop, A -> B -> A /\ B.
Proof.
  intros; split; assumption.
Qed.
*)
