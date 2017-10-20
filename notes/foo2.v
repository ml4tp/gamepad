Require Import mathcomp.ssreflect.ssreflect.

Lemma foo2 : forall n: nat, n + 0 = n.
Proof.
  intro.
  induction n. {
    simpl.
    reflexivity.
  } {
    simpl.
    have ihn : 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +  n + 0 = n by assumption.
    rewrite -> IHn.
    reflexivity.
  }
Qed.
  