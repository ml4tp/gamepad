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


Set Printing All.
Check id_r.
Check eq.
Check id_l.

Lemma foo : forall n: nat, @eq nat n n.
Proof.
  reflexivity.
Qed.

Print foo.

Definition foo2 : forall n : nat, @eq nat (addn n O) n.
Proof.
  induction n.
  reflexivity.
  unfold addn in *.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
     

Ltac my_rewrite :=
  match goal with
  | [ |- ?X <+> m = ?Y ] => rewrite id_r
  | [ |- e <+> ?X = ?Y ] => rewrite id_l
  end.


Ltac surgery_r e1 e2 :=
  let H := fresh in assert (e1 = e2) as H;
  try (rewrite id_r; reflexivity).

Ltac surgery_l e1 e2 :=
  let H := fresh in assert (e1 = e2) as H;
  try (rewrite id_l; reflexivity).


Ltac my_rewrite3 :=
  match goal with
  | [ |- ?X <+> m = ?Y ] =>
    match X with
    | ?Z <+> m => rewrite id_r (* surgery ((?Z <+> m) <+> m) (Z <+> m) *)
    | e <+> ?Z  => rewrite id_l
    end
  | [ |- e <+> ?X = ?Y ] =>
    match X with
    | ?Z <+> m => rewrite id_r
    | e <+> ?Z  => rewrite id_l
    end
  end.

Ltac my_rewrite4 :=
  match goal with
  | [ |- (?X <+> m) <+> (?Z <+> m) = ?Y ] =>
    assert ((X <+> m) <+> (Z <+> m) = X <+> (Z <+> m)); first [rewrite id_r; reflexivity | rewrite id_l; reflexivity]
  end.

Ltac surgery' dir e1 e2 :=
  let H := fresh in
  (have H : e1 = e2 by repeat (rewrite dir); reflexivity); rewrite H; clear H.


Lemma rewrite_eq_0: forall b: G, (b <+> (m <+> (e <+> (e <+> ((e <+> e) <+> m))))) = b.
Proof.
  intros.
  surgery' id_l ((f b (f m (f e (f e (f (f e e) m)))))) ((f b (f m (f e (f e (f (f e e) m)))))).

Check f.

Lemma rewrite_eq_0: forall b: G, (e <+> m) <+> (b <+> (e <+> m)) = b.
Proof.
  intros.
  have H : (Top.f (f e m) (f b (f e m))) = (f e (f b e)) by repeat (rewrite id_r); reflexivity.
  rewrite H.
                                              
  surgery' id_r ((f (f e m) (f b (f e m)))) ((f e (f b e))).
  
  surgery' id_l ((f (f e (f b (f e m))) m)) ((f (f e (f b m)) m)).
  
  have H: (f (f e (f b (f e m))) m) = (f (f e (f b m)) m).
  repeat (rewrite id_l).
  re
  surgery' id_l ((f (f e (f b (f e m))) m)) ((f (f e (f b m)) m)).

Theorem wtf : forall b: G, ((e <+> b) <+> m) <+> m = b.
Proof.
  intros.
  surgery' id_r (f (f (f e b) m) m) (f (f e b) m).
  surgery' id_l ((e <+> b) <+> m) (b <+> m).
  surgery' id_r (b <+> m) b.
  reflexivity.
Qed.
  
  
   
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

