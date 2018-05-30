Require Import mathcomp.ssreflect.ssreflect.

(* Set Ltac Profiling. *)

Lemma foo7 : forall n: nat, n = n.
Proof.
  intro.
  case: n => [|n]; simpl; simpl ; (have hf: 0 = 0 by done); done.
Qed.
    

(* Show Ltac Profile. *)