(*Set Printing All.*)
Require Import Omega.

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
forall b, ( e <+> ( ( e <+> ( ( e <+> ( e <+> ( e <+> ( ( e <+> ( b ) ) <+> m ) ) ) ) <+> m ) ) <+> m ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_1:
forall b, e <+> ( ( ( ( e <+> ( ( ( e <+> ( e <+> ( e <+> ( b ) ) ) ) <+> m ) <+> m ) ) <+> m ) <+> m ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_2:
forall b, ( e <+> ( ( e <+> ( e <+> ( ( ( e <+> ( ( ( b ) <+> m ) <+> m ) ) <+> m ) <+> m ) ) ) <+> m ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_3:
forall b, ( e <+> ( ( e <+> ( ( ( e <+> ( e <+> ( ( ( b ) <+> m ) <+> m ) ) ) <+> m ) <+> m ) ) <+> m ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_4:
forall b, ( ( e <+> ( e <+> ( e <+> ( ( e <+> ( ( e <+> ( ( b ) <+> m ) ) <+> m ) ) <+> m ) ) ) ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_5:
forall b, ( e <+> ( ( e <+> ( e <+> ( ( e <+> ( e <+> ( ( ( b ) <+> m ) <+> m ) ) ) <+> m ) ) ) <+> m ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_6:
forall b, ( e <+> ( e <+> ( e <+> ( e <+> ( ( e <+> ( ( ( e <+> ( b ) ) <+> m ) <+> m ) ) <+> m ) ) ) ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_7:
forall b, ( e <+> ( ( e <+> ( ( ( ( e <+> ( ( ( b ) <+> m ) <+> m ) ) <+> m ) <+> m ) <+> m ) ) <+> m ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_8:
forall b, ( e <+> ( ( ( e <+> ( e <+> ( ( ( ( ( b ) <+> m ) <+> m ) <+> m ) <+> m ) ) ) <+> m ) <+> m ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_9:
forall b, e <+> ( e <+> ( ( ( e <+> ( e <+> ( ( ( e <+> ( ( b ) <+> m ) ) <+> m ) <+> m ) ) ) <+> m ) <+> m ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_10:
forall b, ( ( e <+> ( ( e <+> ( e <+> ( ( e <+> ( e <+> ( e <+> ( b ) ) ) ) <+> m ) ) ) <+> m ) ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_11:
forall b, e <+> ( e <+> ( e <+> ( ( e <+> ( ( ( e <+> ( e <+> ( ( b ) <+> m ) ) ) <+> m ) <+> m ) ) <+> m ) ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_12:
forall b, ( ( e <+> ( e <+> ( e <+> ( e <+> ( e <+> ( ( e <+> ( ( b ) <+> m ) ) <+> m ) ) ) ) ) ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_13:
forall b, e <+> ( ( ( e <+> ( ( ( ( ( ( e <+> ( b ) ) <+> m ) <+> m ) <+> m ) <+> m ) <+> m ) ) <+> m ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_14:
forall b, ( e <+> ( e <+> ( e <+> ( e <+> ( e <+> ( ( e <+> ( ( ( b ) <+> m ) <+> m ) ) <+> m ) ) ) ) ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_15:
forall b, e <+> ( e <+> ( ( ( ( ( ( ( e <+> ( ( b ) <+> m ) ) <+> m ) <+> m ) <+> m ) <+> m ) <+> m ) <+> m ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_16:
forall b, ( e <+> ( ( ( ( ( e <+> ( e <+> ( ( ( b ) <+> m ) <+> m ) ) ) <+> m ) <+> m ) <+> m ) <+> m ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_17:
forall b, e <+> ( ( ( e <+> ( ( e <+> ( e <+> ( e <+> ( ( e <+> ( b ) ) <+> m ) ) ) ) <+> m ) ) <+> m ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_18:
forall b, e <+> ( e <+> ( e <+> ( e <+> ( ( ( ( e <+> ( ( e <+> ( b ) ) <+> m ) ) <+> m ) <+> m ) <+> m ) ) ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_19:
forall b, ( e <+> ( ( ( ( ( ( e <+> ( ( e <+> ( b ) ) <+> m ) ) <+> m ) <+> m ) <+> m ) <+> m ) <+> m ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_20:
forall b, ( ( ( e <+> ( e <+> ( ( e <+> ( e <+> ( ( ( b ) <+> m ) <+> m ) ) ) <+> m ) ) ) <+> m ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_21:
forall b, e <+> ( e <+> ( e <+> ( ( ( e <+> ( ( ( ( e <+> ( b ) ) <+> m ) <+> m ) <+> m ) ) <+> m ) <+> m ) ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_22:
forall b, ( ( e <+> ( ( ( ( ( e <+> ( ( e <+> ( b ) ) <+> m ) ) <+> m ) <+> m ) <+> m ) <+> m ) ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_23:
forall b, e <+> ( ( ( e <+> ( e <+> ( e <+> ( e <+> ( ( e <+> ( ( b ) <+> m ) ) <+> m ) ) ) ) ) <+> m ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_24:
forall b, e <+> ( ( e <+> ( ( e <+> ( ( ( e <+> ( ( ( b ) <+> m ) <+> m ) ) <+> m ) <+> m ) ) <+> m ) ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_25:
forall b, e <+> ( e <+> ( ( ( e <+> ( ( ( e <+> ( ( e <+> ( b ) ) <+> m ) ) <+> m ) <+> m ) ) <+> m ) <+> m ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_26:
forall b, e <+> ( e <+> ( ( ( e <+> ( ( ( ( ( e <+> ( b ) ) <+> m ) <+> m ) <+> m ) <+> m ) ) <+> m ) <+> m ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_27:
forall b, e <+> ( ( ( ( e <+> ( e <+> ( ( ( ( ( b ) <+> m ) <+> m ) <+> m ) <+> m ) ) ) <+> m ) <+> m ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_28:
forall b, ( ( e <+> ( ( e <+> ( e <+> ( ( e <+> ( e <+> ( ( b ) <+> m ) ) ) <+> m ) ) ) <+> m ) ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_29:
forall b, ( e <+> ( ( ( ( ( ( ( e <+> ( ( b ) <+> m ) ) <+> m ) <+> m ) <+> m ) <+> m ) <+> m ) <+> m ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_30:
forall b, ( ( ( e <+> ( ( e <+> ( e <+> ( ( ( ( b ) <+> m ) <+> m ) <+> m ) ) ) <+> m ) ) <+> m ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_31:
forall b, ( ( ( e <+> ( ( e <+> ( e <+> ( ( ( e <+> ( b ) ) <+> m ) <+> m ) ) ) <+> m ) ) <+> m ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_32:
forall b, ( ( e <+> ( ( e <+> ( ( e <+> ( ( ( ( b ) <+> m ) <+> m ) <+> m ) ) <+> m ) ) <+> m ) ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_33:
forall b, e <+> ( e <+> ( ( ( e <+> ( ( ( ( e <+> ( ( b ) <+> m ) ) <+> m ) <+> m ) <+> m ) ) <+> m ) <+> m ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_34:
forall b, ( ( e <+> ( e <+> ( ( e <+> ( ( e <+> ( e <+> ( e <+> ( b ) ) ) ) <+> m ) ) <+> m ) ) ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_35:
forall b, e <+> ( ( ( e <+> ( e <+> ( e <+> ( ( ( ( ( b ) <+> m ) <+> m ) <+> m ) <+> m ) ) ) ) <+> m ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_36:
forall b, e <+> ( e <+> ( e <+> ( ( e <+> ( ( e <+> ( e <+> ( e <+> ( e <+> ( b ) ) ) ) ) <+> m ) ) <+> m ) ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_37:
forall b, e <+> ( ( ( e <+> ( ( e <+> ( ( ( ( ( b ) <+> m ) <+> m ) <+> m ) <+> m ) ) <+> m ) ) <+> m ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_38:
forall b, ( ( ( e <+> ( e <+> ( ( e <+> ( ( e <+> ( ( b ) <+> m ) ) <+> m ) ) <+> m ) ) ) <+> m ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_39:
forall b, e <+> ( e <+> ( e <+> ( e <+> ( ( e <+> ( ( e <+> ( e <+> ( e <+> ( b ) ) ) ) <+> m ) ) <+> m ) ) ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_40:
forall b, ( ( e <+> ( e <+> ( e <+> ( e <+> ( ( ( e <+> ( ( b ) <+> m ) ) <+> m ) <+> m ) ) ) ) ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_41:
forall b, ( e <+> ( e <+> ( e <+> ( ( ( e <+> ( ( ( ( b ) <+> m ) <+> m ) <+> m ) ) <+> m ) <+> m ) ) ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_42:
forall b, ( ( ( e <+> ( ( e <+> ( e <+> ( ( ( e <+> ( b ) ) <+> m ) <+> m ) ) ) <+> m ) ) <+> m ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_43:
forall b, ( ( e <+> ( ( ( ( e <+> ( e <+> ( ( e <+> ( b ) ) <+> m ) ) ) <+> m ) <+> m ) <+> m ) ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_44:
forall b, e <+> ( e <+> ( ( e <+> ( e <+> ( e <+> ( e <+> ( e <+> ( e <+> ( e <+> ( b ) ) ) ) ) ) ) ) <+> m ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_45:
forall b, e <+> ( ( ( ( ( e <+> ( e <+> ( e <+> ( e <+> ( e <+> ( b ) ) ) ) ) ) <+> m ) <+> m ) <+> m ) <+> m ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_46:
forall b, e <+> ( e <+> ( ( ( ( ( ( ( e <+> ( e <+> ( b ) ) ) <+> m ) <+> m ) <+> m ) <+> m ) <+> m ) <+> m ) ) = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_47:
forall b, ( ( e <+> ( e <+> ( e <+> ( ( e <+> ( e <+> ( ( ( b ) <+> m ) <+> m ) ) ) <+> m ) ) ) ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_48:
forall b, ( ( ( ( e <+> ( ( e <+> ( ( ( e <+> ( b ) ) <+> m ) <+> m ) ) <+> m ) ) <+> m ) <+> m ) <+> m ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

Theorem rewrite_eq_49:
forall b, ( e <+> ( e <+> ( e <+> ( ( ( e <+> ( ( ( e <+> ( b ) ) <+> m ) <+> m ) ) <+> m ) <+> m ) ) ) ) <+> m = b.
intros.
repeat my_rewrite.
reflexivity.
Qed.

