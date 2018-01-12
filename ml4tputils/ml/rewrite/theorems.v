(*Set Printing All.*)
Require Import Omega.

Section Group.
(* The set of the group. *)
Axiom G : Set.

(* The left identity for +. *)
Axiom e : G.

(* The right identity for +. *)
Axiom m : G.

(* + binary operator. *)
Axiom f : G -> G -> G.

(* For readability, we use infix <+> to stand for the binary operator. *)
Infix "<+>" := f (at level 50).

(* [m] is the right-identity for all elements [a] *)
Axiom id_r : forall a, a <+> m = a.

(* [e] is the left-identity for all elements [a] *)
Axiom id_l : forall a, e <+> a = a.

Hint Rewrite id_r id_l : ids.

Ltac my_rewrite :=
  match goal with
  | [ |- ?X <+> m = ?Y ] => rewrite id_r
  | [ |- e <+> ?X = ?Y ] => rewrite id_l
  end.

Theorem rewrite_eq_0:
forall b, ( ( ( ( ( b ) <+> m ) <+> m ) <+> m ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_1:
forall b, e <+> ( ( ( e <+> ( ( b ) <+> m ) ) <+> m ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_2:
forall b, ( ( ( ( ( b ) <+> m ) <+> m ) <+> m ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_3:
forall b, e <+> ( e <+> ( e <+> ( e <+> ( e <+> ( b ) ) ) ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_4:
forall b, e <+> ( e <+> ( e <+> ( ( ( b ) <+> m ) <+> m ) ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_5:
forall b, e <+> ( ( e <+> ( ( e <+> ( b ) ) <+> m ) ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_6:
forall b, e <+> ( ( e <+> ( e <+> ( e <+> ( b ) ) ) ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_7:
forall b, e <+> ( ( ( ( ( b ) <+> m ) <+> m ) <+> m ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_8:
forall b, ( ( e <+> ( e <+> ( e <+> ( b ) ) ) ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_9:
forall b, ( e <+> ( ( ( e <+> ( b ) ) <+> m ) <+> m ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

