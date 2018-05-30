Require Import mathcomp.ssreflect.ssreflect.

Lemma foo : forall n: nat, n = n.
Proof.
  intro.
  done.
Qed.

(*
Ltac done' := try (done; auto).

Ltac inst tac :=
  match goal with
  | _ => tac; auto
  | _ => try tac; auto
  end.

Lemma wtf : forall n: nat, n + n = 2 * n.
Proof.
Admitted.

Hint Immediate wtf.

Set Ltac Profiling.
Lemma foo1 : forall n: nat, n + n = 2 * n.
Proof.
  intro.
  inst done.
Qed.
Show Ltac Profile.


Lemma foo7 : forall n: nat, n = n.
Proof.
  intro.
  case: n => [|n]; simpl; simpl ; (have hf: 0 = 0 by done'); done'.
Qed.
*)
