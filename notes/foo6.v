Require Import mathcomp.ssreflect.ssreflect.

Lemma foo5' : forall n: nat, n = n -> S n = S n -> S (S n) = S (S n).
Proof.
  auto.
Qed.

(* Set Ltac Profiling. *)

Lemma foo5 : forall n: nat, n = n.
Proof.
  intro.
  case: n => [|n]; simpl; try case: n => [|n]; simpl ; (have hf: 0 = 0 by reflexivity); (have hf2: 0 = 0 by auto); do 2?(apply foo5'); apply:eq_refl.
Qed.

(* Show Ltac Profile. *)