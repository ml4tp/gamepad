Require Import mathcomp.ssreflect.ssreflect.

Lemma foo2 : forall n: nat, n + 0 = n.
Proof.
  intro.
  induction n. {
    simpl.
    reflexivity.
  } {
    simpl.
    have foo: 0 = 0 by simpl; reflexivity.
    have foo2: 0 = 0 by assumption.
    have foo3: 0 = 0 by trivial.
    have foo4: 0 = 0 by exact foo3.
    have foo5: 0 = 0 by apply foo4.
    (* have ihn : 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 +  n + 0 = n by assumption. *)
    rewrite -> IHn.
    reflexivity.
  }
Qed.
  
