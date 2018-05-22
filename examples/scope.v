Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrnat.

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

Ltac surgery dir e1 e2 :=
  match goal with
  | [ |- _ ] =>
    let H := fresh in
    (have H : e1 = e2 by repeat (rewrite dir); reflexivity); rewrite H; clear H
  end.

Lemma rewrite_eq_0: forall b: G, (e <+> m) <+> b = b.
Proof.
  intros.
  surgery id_r ((e <+> m) <+> b) (e <+> b).
  surgery id_l (e <+> b) b.
  reflexivity.
Qed.
