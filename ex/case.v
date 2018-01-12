Print and.

Lemma foo : forall A B: Prop, A -> B -> A /\ B.
Proof.
  auto.
Qed.

Print foo.

Set Printing all.

Print foo.
Locate "->".


Definition ident (n: nat) :=
  match n with
  | O => O
  | S n => S n
  end.

Lemma ident_nat : forall n: nat, ident n = n.
Proof.
  intro n.
  case n; reflexivity.
Qed.

(*
Print ident.
*)