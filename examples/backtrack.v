Require Import mathcomp.ssreflect.ssreflect.

Set Ltac Profiling.

Lemma plus_O : forall n m: nat, n + m = m + n.
Proof.
  induction n; try done; simpl; intro.
  rewrite IHn.
  done.
Qed.

Show Ltac Profile.