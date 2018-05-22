Definition compose {A B C: Prop} (f: A -> B) (g: B -> C) (x: A) := g (f (x)).

Lemma transitive : forall A B C D: Prop, forall f: A -> B, forall g: B -> C, forall h: C -> D, forall x: A, h ((compose f g) x) = (compose g h) (f x).
Proof.
  intros.
  unfold compose.
  reflexivity.
Qed.
