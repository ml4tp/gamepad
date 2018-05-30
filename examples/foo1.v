Require Import mathcomp.ssreflect.ssreflect.

Lemma foo1 : forall n: nat, n = n.
Proof.
  intro.
  case: n => [|n]; simpl; try case: n => [|n]; simpl ; (have hf: 0 = 0 by reflexivity); (have hf2: 0 = 0 by auto); apply:eq_refl.
Qed.  