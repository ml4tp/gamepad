Require Import mathcomp.ssreflect.ssreflect.

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

(*
Ltac surgery dir e1 e2 :=
  let H := fresh in
  (have H : e1 = e2 by repeat (rewrite dir); reflexivity); rewrite H; clear H.
*)
Lemma rewrite_eq_0: forall b: G, ((e <+> (e <+> m)) <+> ((b <+> ((m <+> m) <+> m)) <+> ((e <+> e) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e m)) (f (f b (f (f m m) m)) (f (f e e) m)))) ((f (f e m) (f (f b (f (f m m) m)) (f (f e e) m)))).
surgery id_r ((f (f e m) (f (f b (f (f m m) m)) (f (f e e) m)))) ((f e (f (f b (f (f m m) m)) (f (f e e) m)))).
surgery id_r ((f e (f (f b (f (f m m) m)) (f (f e e) m)))) ((f e (f (f b (f m m)) (f (f e e) m)))).
surgery id_r ((f e (f (f b (f m m)) (f (f e e) m)))) ((f e (f (f b m) (f (f e e) m)))).
surgery id_r ((f e (f (f b m) (f (f e e) m)))) ((f e (f b (f (f e e) m)))).
surgery id_l ((f e (f b (f (f e e) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_1: forall b: G, ((((e <+> e) <+> m) <+> ((e <+> m) <+> ((e <+> m) <+> m))) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) (f (f e m) (f (f e m) m))) (f b m))) ((f (f (f e e) (f (f e m) (f (f e m) m))) (f b m))).
surgery id_l ((f (f (f e e) (f (f e m) (f (f e m) m))) (f b m))) ((f (f e (f (f e m) (f (f e m) m))) (f b m))).
surgery id_r ((f (f e (f (f e m) (f (f e m) m))) (f b m))) ((f (f e (f e (f (f e m) m))) (f b m))).
surgery id_l ((f (f e (f e (f (f e m) m))) (f b m))) ((f (f e (f (f e m) m)) (f b m))).
surgery id_r ((f (f e (f (f e m) m)) (f b m))) ((f (f e (f e m)) (f b m))).
surgery id_l ((f (f e (f e m)) (f b m))) ((f (f e m) (f b m))).
surgery id_r ((f (f e m) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_2: forall b: G, ((e <+> ((((e <+> e) <+> m) <+> e) <+> m)) <+> (e <+> (e <+> (e <+> b)))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f (f (f e e) m) e) m)) (f e (f e (f e b))))) ((f (f e (f (f (f e e) e) m)) (f e (f e (f e b))))).
surgery id_l ((f (f e (f (f (f e e) e) m)) (f e (f e (f e b))))) ((f (f e (f (f e e) m)) (f e (f e (f e b))))).
surgery id_l ((f (f e (f (f e e) m)) (f e (f e (f e b))))) ((f (f e (f e m)) (f e (f e (f e b))))).
surgery id_l ((f (f e (f e m)) (f e (f e (f e b))))) ((f (f e m) (f e (f e (f e b))))).
surgery id_r ((f (f e m) (f e (f e (f e b))))) ((f e (f e (f e (f e b))))).
surgery id_l ((f e (f e (f e (f e b))))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_3: forall b: G, (e <+> (((e <+> m) <+> e) <+> (e <+> (((e <+> e) <+> m) <+> (b <+> m))))) = b.
Proof.
intros.
surgery id_r ((f e (f (f (f e m) e) (f e (f (f (f e e) m) (f b m)))))) ((f e (f (f e e) (f e (f (f (f e e) m) (f b m)))))).
surgery id_l ((f e (f (f e e) (f e (f (f (f e e) m) (f b m)))))) ((f e (f e (f e (f (f (f e e) m) (f b m)))))).
surgery id_l ((f e (f e (f e (f (f (f e e) m) (f b m)))))) ((f e (f e (f (f (f e e) m) (f b m))))).
surgery id_l ((f e (f e (f (f (f e e) m) (f b m))))) ((f e (f (f (f e e) m) (f b m)))).
surgery id_r ((f e (f (f (f e e) m) (f b m)))) ((f e (f (f e e) (f b m)))).
surgery id_l ((f e (f (f e e) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_4: forall b: G, (((e <+> (e <+> (((e <+> m) <+> m) <+> (m <+> m)))) <+> m) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f e (f (f (f e m) m) (f m m)))) m) (f e b))) ((f (f e (f e (f (f (f e m) m) (f m m)))) (f e b))).
surgery id_l ((f (f e (f e (f (f (f e m) m) (f m m)))) (f e b))) ((f (f e (f (f (f e m) m) (f m m))) (f e b))).
surgery id_r ((f (f e (f (f (f e m) m) (f m m))) (f e b))) ((f (f e (f (f e m) (f m m))) (f e b))).
surgery id_r ((f (f e (f (f e m) (f m m))) (f e b))) ((f (f e (f e (f m m))) (f e b))).
surgery id_l ((f (f e (f e (f m m))) (f e b))) ((f (f e (f m m)) (f e b))).
surgery id_r ((f (f e (f m m)) (f e b))) ((f (f e m) (f e b))).
surgery id_r ((f (f e m) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_5: forall b: G, ((((e <+> e) <+> ((e <+> e) <+> (e <+> m))) <+> (e <+> m)) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) (f (f e e) (f e m))) (f e m)) (f b m))) ((f (f (f e (f (f e e) (f e m))) (f e m)) (f b m))).
surgery id_l ((f (f (f e (f (f e e) (f e m))) (f e m)) (f b m))) ((f (f (f e (f e (f e m))) (f e m)) (f b m))).
surgery id_l ((f (f (f e (f e (f e m))) (f e m)) (f b m))) ((f (f (f e (f e m)) (f e m)) (f b m))).
surgery id_l ((f (f (f e (f e m)) (f e m)) (f b m))) ((f (f (f e m) (f e m)) (f b m))).
surgery id_r ((f (f (f e m) (f e m)) (f b m))) ((f (f e (f e m)) (f b m))).
surgery id_l ((f (f e (f e m)) (f b m))) ((f (f e m) (f b m))).
surgery id_r ((f (f e m) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_6: forall b: G, (e <+> (((e <+> m) <+> (e <+> (m <+> ((e <+> e) <+> m)))) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_r ((f e (f (f (f e m) (f e (f m (f (f e e) m)))) (f e b)))) ((f e (f (f e (f e (f m (f (f e e) m)))) (f e b)))).
surgery id_l ((f e (f (f e (f e (f m (f (f e e) m)))) (f e b)))) ((f e (f (f e (f m (f (f e e) m))) (f e b)))).
surgery id_l ((f e (f (f e (f m (f (f e e) m))) (f e b)))) ((f e (f (f e (f m (f e m))) (f e b)))).
surgery id_l ((f e (f (f e (f m (f e m))) (f e b)))) ((f e (f (f e (f m m)) (f e b)))).
surgery id_r ((f e (f (f e (f m m)) (f e b)))) ((f e (f (f e m) (f e b)))).
surgery id_r ((f e (f (f e m) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_7: forall b: G, (((e <+> m) <+> ((e <+> m) <+> (e <+> ((e <+> (m <+> m)) <+> m)))) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f (f e m) (f e (f (f e (f m m)) m)))) b)) ((f (f e (f (f e m) (f e (f (f e (f m m)) m)))) b)).
surgery id_r ((f (f e (f (f e m) (f e (f (f e (f m m)) m)))) b)) ((f (f e (f e (f e (f (f e (f m m)) m)))) b)).
surgery id_l ((f (f e (f e (f e (f (f e (f m m)) m)))) b)) ((f (f e (f e (f (f e (f m m)) m))) b)).
surgery id_l ((f (f e (f e (f (f e (f m m)) m))) b)) ((f (f e (f (f e (f m m)) m)) b)).
surgery id_r ((f (f e (f (f e (f m m)) m)) b)) ((f (f e (f (f e m) m)) b)).
surgery id_r ((f (f e (f (f e m) m)) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_8: forall b: G, (((((e <+> e) <+> m) <+> m) <+> (e <+> m)) <+> ((e <+> e) <+> (b <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e e) m) m) (f e m)) (f (f e e) (f b m)))) ((f (f (f (f e e) m) (f e m)) (f (f e e) (f b m)))).
surgery id_r ((f (f (f (f e e) m) (f e m)) (f (f e e) (f b m)))) ((f (f (f e e) (f e m)) (f (f e e) (f b m)))).
surgery id_l ((f (f (f e e) (f e m)) (f (f e e) (f b m)))) ((f (f e (f e m)) (f (f e e) (f b m)))).
surgery id_l ((f (f e (f e m)) (f (f e e) (f b m)))) ((f (f e m) (f (f e e) (f b m)))).
surgery id_r ((f (f e m) (f (f e e) (f b m)))) ((f e (f (f e e) (f b m)))).
surgery id_l ((f e (f (f e e) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_9: forall b: G, (((((e <+> e) <+> m) <+> m) <+> ((e <+> (e <+> b)) <+> (m <+> m))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e e) m) m) (f (f e (f e b)) (f m m))) m)) ((f (f (f (f e e) m) m) (f (f e (f e b)) (f m m)))).
surgery id_r ((f (f (f (f e e) m) m) (f (f e (f e b)) (f m m)))) ((f (f (f e e) m) (f (f e (f e b)) (f m m)))).
surgery id_r ((f (f (f e e) m) (f (f e (f e b)) (f m m)))) ((f (f e e) (f (f e (f e b)) (f m m)))).
surgery id_l ((f (f e e) (f (f e (f e b)) (f m m)))) ((f e (f (f e (f e b)) (f m m)))).
surgery id_l ((f e (f (f e (f e b)) (f m m)))) ((f e (f (f e b) (f m m)))).
surgery id_l ((f e (f (f e b) (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_10: forall b: G, ((e <+> ((e <+> m) <+> m)) <+> (e <+> ((b <+> m) <+> ((e <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f e m) m)) (f e (f (f b m) (f (f e m) m))))) ((f (f e (f e m)) (f e (f (f b m) (f (f e m) m))))).
surgery id_l ((f (f e (f e m)) (f e (f (f b m) (f (f e m) m))))) ((f (f e m) (f e (f (f b m) (f (f e m) m))))).
surgery id_r ((f (f e m) (f e (f (f b m) (f (f e m) m))))) ((f e (f e (f (f b m) (f (f e m) m))))).
surgery id_l ((f e (f e (f (f b m) (f (f e m) m))))) ((f e (f (f b m) (f (f e m) m)))).
surgery id_r ((f e (f (f b m) (f (f e m) m)))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_11: forall b: G, ((((e <+> (e <+> (m <+> (e <+> m)))) <+> b) <+> m) <+> ((e <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e (f e (f m (f e m)))) b) m) (f (f e m) m))) ((f (f (f e (f e (f m (f e m)))) b) (f (f e m) m))).
surgery id_l ((f (f (f e (f e (f m (f e m)))) b) (f (f e m) m))) ((f (f (f e (f m (f e m))) b) (f (f e m) m))).
surgery id_l ((f (f (f e (f m (f e m))) b) (f (f e m) m))) ((f (f (f e (f m m)) b) (f (f e m) m))).
surgery id_r ((f (f (f e (f m m)) b) (f (f e m) m))) ((f (f (f e m) b) (f (f e m) m))).
surgery id_r ((f (f (f e m) b) (f (f e m) m))) ((f (f e b) (f (f e m) m))).
surgery id_l ((f (f e b) (f (f e m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_12: forall b: G, ((((e <+> m) <+> b) <+> m) <+> (((((e <+> e) <+> e) <+> m) <+> e) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) b) m) (f (f (f (f (f e e) e) m) e) m))) ((f (f (f e m) b) (f (f (f (f (f e e) e) m) e) m))).
surgery id_r ((f (f (f e m) b) (f (f (f (f (f e e) e) m) e) m))) ((f (f e b) (f (f (f (f (f e e) e) m) e) m))).
surgery id_l ((f (f e b) (f (f (f (f (f e e) e) m) e) m))) ((f b (f (f (f (f (f e e) e) m) e) m))).
surgery id_r ((f b (f (f (f (f (f e e) e) m) e) m))) ((f b (f (f (f (f e e) e) e) m))).
surgery id_l ((f b (f (f (f (f e e) e) e) m))) ((f b (f (f (f e e) e) m))).
surgery id_l ((f b (f (f (f e e) e) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_13: forall b: G, (((e <+> (e <+> m)) <+> (e <+> m)) <+> ((b <+> m) <+> ((e <+> m) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f e m)) (f (f b m) (f (f e m) m)))) ((f (f (f e m) (f e m)) (f (f b m) (f (f e m) m)))).
surgery id_r ((f (f (f e m) (f e m)) (f (f b m) (f (f e m) m)))) ((f (f e (f e m)) (f (f b m) (f (f e m) m)))).
surgery id_l ((f (f e (f e m)) (f (f b m) (f (f e m) m)))) ((f (f e m) (f (f b m) (f (f e m) m)))).
surgery id_r ((f (f e m) (f (f b m) (f (f e m) m)))) ((f e (f (f b m) (f (f e m) m)))).
surgery id_r ((f e (f (f b m) (f (f e m) m)))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_14: forall b: G, ((((e <+> m) <+> (e <+> e)) <+> (((e <+> m) <+> m) <+> (e <+> m))) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f e e)) (f (f (f e m) m) (f e m))) b)) ((f (f (f e (f e e)) (f (f (f e m) m) (f e m))) b)).
surgery id_l ((f (f (f e (f e e)) (f (f (f e m) m) (f e m))) b)) ((f (f (f e e) (f (f (f e m) m) (f e m))) b)).
surgery id_l ((f (f (f e e) (f (f (f e m) m) (f e m))) b)) ((f (f e (f (f (f e m) m) (f e m))) b)).
surgery id_r ((f (f e (f (f (f e m) m) (f e m))) b)) ((f (f e (f (f e m) (f e m))) b)).
surgery id_r ((f (f e (f (f e m) (f e m))) b)) ((f (f e (f e (f e m))) b)).
surgery id_l ((f (f e (f e (f e m))) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_15: forall b: G, ((((e <+> e) <+> m) <+> (e <+> (b <+> m))) <+> ((e <+> e) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) (f e (f b m))) (f (f e e) (f m m)))) ((f (f (f e e) (f e (f b m))) (f (f e e) (f m m)))).
surgery id_l ((f (f (f e e) (f e (f b m))) (f (f e e) (f m m)))) ((f (f e (f e (f b m))) (f (f e e) (f m m)))).
surgery id_l ((f (f e (f e (f b m))) (f (f e e) (f m m)))) ((f (f e (f b m)) (f (f e e) (f m m)))).
surgery id_r ((f (f e (f b m)) (f (f e e) (f m m)))) ((f (f e b) (f (f e e) (f m m)))).
surgery id_l ((f (f e b) (f (f e e) (f m m)))) ((f b (f (f e e) (f m m)))).
surgery id_l ((f b (f (f e e) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_16: forall b: G, (b <+> ((m <+> (m <+> m)) <+> ((e <+> e) <+> (((e <+> m) <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f b (f (f m (f m m)) (f (f e e) (f (f (f e m) m) m))))) ((f b (f (f m m) (f (f e e) (f (f (f e m) m) m))))).
surgery id_r ((f b (f (f m m) (f (f e e) (f (f (f e m) m) m))))) ((f b (f m (f (f e e) (f (f (f e m) m) m))))).
surgery id_l ((f b (f m (f (f e e) (f (f (f e m) m) m))))) ((f b (f m (f e (f (f (f e m) m) m))))).
surgery id_l ((f b (f m (f e (f (f (f e m) m) m))))) ((f b (f m (f (f (f e m) m) m)))).
surgery id_r ((f b (f m (f (f (f e m) m) m)))) ((f b (f m (f (f e m) m)))).
surgery id_r ((f b (f m (f (f e m) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_17: forall b: G, ((e <+> m) <+> ((((e <+> m) <+> e) <+> e) <+> (b <+> ((e <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f (f (f e m) e) e) (f b (f (f e m) m))))) ((f e (f (f (f (f e m) e) e) (f b (f (f e m) m))))).
surgery id_r ((f e (f (f (f (f e m) e) e) (f b (f (f e m) m))))) ((f e (f (f (f e e) e) (f b (f (f e m) m))))).
surgery id_l ((f e (f (f (f e e) e) (f b (f (f e m) m))))) ((f e (f (f e e) (f b (f (f e m) m))))).
surgery id_l ((f e (f (f e e) (f b (f (f e m) m))))) ((f e (f e (f b (f (f e m) m))))).
surgery id_l ((f e (f e (f b (f (f e m) m))))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_18: forall b: G, ((((e <+> e) <+> (e <+> m)) <+> (((e <+> e) <+> (b <+> m)) <+> m)) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) (f e m)) (f (f (f e e) (f b m)) m)) m)) ((f (f (f e e) (f e m)) (f (f (f e e) (f b m)) m))).
surgery id_l ((f (f (f e e) (f e m)) (f (f (f e e) (f b m)) m))) ((f (f e (f e m)) (f (f (f e e) (f b m)) m))).
surgery id_l ((f (f e (f e m)) (f (f (f e e) (f b m)) m))) ((f (f e m) (f (f (f e e) (f b m)) m))).
surgery id_r ((f (f e m) (f (f (f e e) (f b m)) m))) ((f e (f (f (f e e) (f b m)) m))).
surgery id_l ((f e (f (f (f e e) (f b m)) m))) ((f e (f (f e (f b m)) m))).
surgery id_r ((f e (f (f e (f b m)) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_19: forall b: G, ((((e <+> e) <+> (e <+> (e <+> m))) <+> m) <+> (b <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) (f e (f e m))) m) (f b (f e (f e m))))) ((f (f (f e e) (f e (f e m))) (f b (f e (f e m))))).
surgery id_l ((f (f (f e e) (f e (f e m))) (f b (f e (f e m))))) ((f (f e (f e (f e m))) (f b (f e (f e m))))).
surgery id_l ((f (f e (f e (f e m))) (f b (f e (f e m))))) ((f (f e (f e m)) (f b (f e (f e m))))).
surgery id_l ((f (f e (f e m)) (f b (f e (f e m))))) ((f (f e m) (f b (f e (f e m))))).
surgery id_r ((f (f e m) (f b (f e (f e m))))) ((f e (f b (f e (f e m))))).
surgery id_l ((f e (f b (f e (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_20: forall b: G, (((b <+> m) <+> m) <+> ((((e <+> m) <+> m) <+> m) <+> ((e <+> e) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) m) (f (f (f (f e m) m) m) (f (f e e) m)))) ((f (f b m) (f (f (f (f e m) m) m) (f (f e e) m)))).
surgery id_r ((f (f b m) (f (f (f (f e m) m) m) (f (f e e) m)))) ((f b (f (f (f (f e m) m) m) (f (f e e) m)))).
surgery id_r ((f b (f (f (f (f e m) m) m) (f (f e e) m)))) ((f b (f (f (f e m) m) (f (f e e) m)))).
surgery id_r ((f b (f (f (f e m) m) (f (f e e) m)))) ((f b (f (f e m) (f (f e e) m)))).
surgery id_r ((f b (f (f e m) (f (f e e) m)))) ((f b (f e (f (f e e) m)))).
surgery id_l ((f b (f e (f (f e e) m)))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_21: forall b: G, (((e <+> e) <+> ((e <+> e) <+> (e <+> (e <+> b)))) <+> ((e <+> m) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f e e) (f e (f e b)))) (f (f e m) m))) ((f (f e (f (f e e) (f e (f e b)))) (f (f e m) m))).
surgery id_l ((f (f e (f (f e e) (f e (f e b)))) (f (f e m) m))) ((f (f e (f e (f e (f e b)))) (f (f e m) m))).
surgery id_l ((f (f e (f e (f e (f e b)))) (f (f e m) m))) ((f (f e (f e (f e b))) (f (f e m) m))).
surgery id_l ((f (f e (f e (f e b))) (f (f e m) m))) ((f (f e (f e b)) (f (f e m) m))).
surgery id_l ((f (f e (f e b)) (f (f e m) m))) ((f (f e b) (f (f e m) m))).
surgery id_l ((f (f e b) (f (f e m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_22: forall b: G, ((((e <+> ((e <+> m) <+> b)) <+> m) <+> m) <+> ((e <+> m) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e (f (f e m) b)) m) m) (f (f e m) (f e m)))) ((f (f (f e (f (f e m) b)) m) (f (f e m) (f e m)))).
surgery id_r ((f (f (f e (f (f e m) b)) m) (f (f e m) (f e m)))) ((f (f e (f (f e m) b)) (f (f e m) (f e m)))).
surgery id_r ((f (f e (f (f e m) b)) (f (f e m) (f e m)))) ((f (f e (f e b)) (f (f e m) (f e m)))).
surgery id_l ((f (f e (f e b)) (f (f e m) (f e m)))) ((f (f e b) (f (f e m) (f e m)))).
surgery id_l ((f (f e b) (f (f e m) (f e m)))) ((f b (f (f e m) (f e m)))).
surgery id_r ((f b (f (f e m) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_23: forall b: G, (e <+> (((e <+> (e <+> m)) <+> e) <+> ((b <+> (m <+> m)) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f e (f (f (f e (f e m)) e) (f (f b (f m m)) (f m m))))) ((f e (f (f (f e m) e) (f (f b (f m m)) (f m m))))).
surgery id_r ((f e (f (f (f e m) e) (f (f b (f m m)) (f m m))))) ((f e (f (f e e) (f (f b (f m m)) (f m m))))).
surgery id_l ((f e (f (f e e) (f (f b (f m m)) (f m m))))) ((f e (f e (f (f b (f m m)) (f m m))))).
surgery id_l ((f e (f e (f (f b (f m m)) (f m m))))) ((f e (f (f b (f m m)) (f m m)))).
surgery id_r ((f e (f (f b (f m m)) (f m m)))) ((f e (f (f b m) (f m m)))).
surgery id_r ((f e (f (f b m) (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_24: forall b: G, (((e <+> (e <+> (e <+> m))) <+> (b <+> ((e <+> m) <+> m))) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e (f e m))) (f b (f (f e m) m))) (f e m))) ((f (f (f e (f e m)) (f b (f (f e m) m))) (f e m))).
surgery id_l ((f (f (f e (f e m)) (f b (f (f e m) m))) (f e m))) ((f (f (f e m) (f b (f (f e m) m))) (f e m))).
surgery id_r ((f (f (f e m) (f b (f (f e m) m))) (f e m))) ((f (f e (f b (f (f e m) m))) (f e m))).
surgery id_r ((f (f e (f b (f (f e m) m))) (f e m))) ((f (f e (f b (f e m))) (f e m))).
surgery id_l ((f (f e (f b (f e m))) (f e m))) ((f (f e (f b m)) (f e m))).
surgery id_r ((f (f e (f b m)) (f e m))) ((f (f e b) (f e m))).
surgery id_l ((f (f e b) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_25: forall b: G, (((e <+> ((e <+> (e <+> m)) <+> (m <+> m))) <+> (m <+> (e <+> m))) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f (f e (f e m)) (f m m))) (f m (f e m))) b)) ((f (f (f e (f (f e m) (f m m))) (f m (f e m))) b)).
surgery id_r ((f (f (f e (f (f e m) (f m m))) (f m (f e m))) b)) ((f (f (f e (f e (f m m))) (f m (f e m))) b)).
surgery id_l ((f (f (f e (f e (f m m))) (f m (f e m))) b)) ((f (f (f e (f m m)) (f m (f e m))) b)).
surgery id_r ((f (f (f e (f m m)) (f m (f e m))) b)) ((f (f (f e m) (f m (f e m))) b)).
surgery id_r ((f (f (f e m) (f m (f e m))) b)) ((f (f e (f m (f e m))) b)).
surgery id_l ((f (f e (f m (f e m))) b)) ((f (f e (f m m)) b)).
surgery id_r ((f (f e (f m m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_26: forall b: G, (e <+> ((b <+> ((e <+> m) <+> m)) <+> ((e <+> (e <+> (e <+> m))) <+> m))) = b.
Proof.
intros.
surgery id_r ((f e (f (f b (f (f e m) m)) (f (f e (f e (f e m))) m)))) ((f e (f (f b (f e m)) (f (f e (f e (f e m))) m)))).
surgery id_l ((f e (f (f b (f e m)) (f (f e (f e (f e m))) m)))) ((f e (f (f b m) (f (f e (f e (f e m))) m)))).
surgery id_r ((f e (f (f b m) (f (f e (f e (f e m))) m)))) ((f e (f b (f (f e (f e (f e m))) m)))).
surgery id_l ((f e (f b (f (f e (f e (f e m))) m)))) ((f e (f b (f (f e (f e m)) m)))).
surgery id_l ((f e (f b (f (f e (f e m)) m)))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_27: forall b: G, (((e <+> m) <+> ((e <+> m) <+> ((e <+> m) <+> ((e <+> m) <+> b)))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f (f e m) (f (f e m) (f (f e m) b)))) m)) ((f (f e m) (f (f e m) (f (f e m) (f (f e m) b))))).
surgery id_r ((f (f e m) (f (f e m) (f (f e m) (f (f e m) b))))) ((f e (f (f e m) (f (f e m) (f (f e m) b))))).
surgery id_r ((f e (f (f e m) (f (f e m) (f (f e m) b))))) ((f e (f e (f (f e m) (f (f e m) b))))).
surgery id_l ((f e (f e (f (f e m) (f (f e m) b))))) ((f e (f (f e m) (f (f e m) b)))).
surgery id_r ((f e (f (f e m) (f (f e m) b)))) ((f e (f e (f (f e m) b)))).
surgery id_l ((f e (f e (f (f e m) b)))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_28: forall b: G, (((e <+> e) <+> e) <+> (b <+> (((e <+> m) <+> m) <+> (e <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) e) (f b (f (f (f e m) m) (f e (f m m)))))) ((f (f e e) (f b (f (f (f e m) m) (f e (f m m)))))).
surgery id_l ((f (f e e) (f b (f (f (f e m) m) (f e (f m m)))))) ((f e (f b (f (f (f e m) m) (f e (f m m)))))).
surgery id_r ((f e (f b (f (f (f e m) m) (f e (f m m)))))) ((f e (f b (f (f e m) (f e (f m m)))))).
surgery id_r ((f e (f b (f (f e m) (f e (f m m)))))) ((f e (f b (f e (f e (f m m)))))).
surgery id_l ((f e (f b (f e (f e (f m m)))))) ((f e (f b (f e (f m m))))).
surgery id_l ((f e (f b (f e (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_29: forall b: G, ((((e <+> m) <+> (e <+> m)) <+> (e <+> (e <+> e))) <+> ((e <+> e) <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f e m)) (f e (f e e))) (f (f e e) b))) ((f (f (f e (f e m)) (f e (f e e))) (f (f e e) b))).
surgery id_l ((f (f (f e (f e m)) (f e (f e e))) (f (f e e) b))) ((f (f (f e m) (f e (f e e))) (f (f e e) b))).
surgery id_r ((f (f (f e m) (f e (f e e))) (f (f e e) b))) ((f (f e (f e (f e e))) (f (f e e) b))).
surgery id_l ((f (f e (f e (f e e))) (f (f e e) b))) ((f (f e (f e e)) (f (f e e) b))).
surgery id_l ((f (f e (f e e)) (f (f e e) b))) ((f (f e e) (f (f e e) b))).
surgery id_l ((f (f e e) (f (f e e) b))) ((f e (f (f e e) b))).
surgery id_l ((f e (f (f e e) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_30: forall b: G, (((((e <+> e) <+> e) <+> ((e <+> m) <+> m)) <+> ((e <+> m) <+> m)) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f (f (f e e) e) (f (f e m) m)) (f (f e m) m)) b)) ((f (f (f (f e e) (f (f e m) m)) (f (f e m) m)) b)).
surgery id_l ((f (f (f (f e e) (f (f e m) m)) (f (f e m) m)) b)) ((f (f (f e (f (f e m) m)) (f (f e m) m)) b)).
surgery id_r ((f (f (f e (f (f e m) m)) (f (f e m) m)) b)) ((f (f (f e (f e m)) (f (f e m) m)) b)).
surgery id_l ((f (f (f e (f e m)) (f (f e m) m)) b)) ((f (f (f e m) (f (f e m) m)) b)).
surgery id_r ((f (f (f e m) (f (f e m) m)) b)) ((f (f e (f (f e m) m)) b)).
surgery id_r ((f (f e (f (f e m) m)) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_31: forall b: G, (e <+> ((e <+> ((e <+> (m <+> m)) <+> m)) <+> ((e <+> (e <+> m)) <+> b))) = b.
Proof.
intros.
surgery id_r ((f e (f (f e (f (f e (f m m)) m)) (f (f e (f e m)) b)))) ((f e (f (f e (f (f e m) m)) (f (f e (f e m)) b)))).
surgery id_r ((f e (f (f e (f (f e m) m)) (f (f e (f e m)) b)))) ((f e (f (f e (f e m)) (f (f e (f e m)) b)))).
surgery id_l ((f e (f (f e (f e m)) (f (f e (f e m)) b)))) ((f e (f (f e m) (f (f e (f e m)) b)))).
surgery id_r ((f e (f (f e m) (f (f e (f e m)) b)))) ((f e (f e (f (f e (f e m)) b)))).
surgery id_l ((f e (f e (f (f e (f e m)) b)))) ((f e (f (f e (f e m)) b))).
surgery id_l ((f e (f (f e (f e m)) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_32: forall b: G, ((((e <+> b) <+> m) <+> ((m <+> (e <+> m)) <+> m)) <+> ((m <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e b) m) (f (f m (f e m)) m)) (f (f m m) m))) ((f (f (f e b) (f (f m (f e m)) m)) (f (f m m) m))).
surgery id_l ((f (f (f e b) (f (f m (f e m)) m)) (f (f m m) m))) ((f (f b (f (f m (f e m)) m)) (f (f m m) m))).
surgery id_l ((f (f b (f (f m (f e m)) m)) (f (f m m) m))) ((f (f b (f (f m m) m)) (f (f m m) m))).
surgery id_r ((f (f b (f (f m m) m)) (f (f m m) m))) ((f (f b (f m m)) (f (f m m) m))).
surgery id_r ((f (f b (f m m)) (f (f m m) m))) ((f (f b m) (f (f m m) m))).
surgery id_r ((f (f b m) (f (f m m) m))) ((f b (f (f m m) m))).
surgery id_r ((f b (f (f m m) m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_33: forall b: G, (((e <+> ((((e <+> m) <+> (e <+> m)) <+> m) <+> m)) <+> b) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f (f (f e m) (f e m)) m) m)) b) (f m m))) ((f (f (f e (f (f (f e m) (f e m)) m)) b) (f m m))).
surgery id_r ((f (f (f e (f (f (f e m) (f e m)) m)) b) (f m m))) ((f (f (f e (f (f e (f e m)) m)) b) (f m m))).
surgery id_l ((f (f (f e (f (f e (f e m)) m)) b) (f m m))) ((f (f (f e (f (f e m) m)) b) (f m m))).
surgery id_r ((f (f (f e (f (f e m) m)) b) (f m m))) ((f (f (f e (f e m)) b) (f m m))).
surgery id_l ((f (f (f e (f e m)) b) (f m m))) ((f (f (f e m) b) (f m m))).
surgery id_r ((f (f (f e m) b) (f m m))) ((f (f e b) (f m m))).
surgery id_l ((f (f e b) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_34: forall b: G, (((e <+> e) <+> (b <+> ((e <+> m) <+> ((e <+> m) <+> m)))) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f b (f (f e m) (f (f e m) m)))) (f e m))) ((f (f e (f b (f (f e m) (f (f e m) m)))) (f e m))).
surgery id_r ((f (f e (f b (f (f e m) (f (f e m) m)))) (f e m))) ((f (f e (f b (f e (f (f e m) m)))) (f e m))).
surgery id_l ((f (f e (f b (f e (f (f e m) m)))) (f e m))) ((f (f e (f b (f (f e m) m))) (f e m))).
surgery id_r ((f (f e (f b (f (f e m) m))) (f e m))) ((f (f e (f b (f e m))) (f e m))).
surgery id_l ((f (f e (f b (f e m))) (f e m))) ((f (f e (f b m)) (f e m))).
surgery id_r ((f (f e (f b m)) (f e m))) ((f (f e b) (f e m))).
surgery id_l ((f (f e b) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_35: forall b: G, ((e <+> m) <+> (((e <+> (((e <+> m) <+> m) <+> m)) <+> (b <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f (f e (f (f (f e m) m) m)) (f b m)) m))) ((f e (f (f (f e (f (f (f e m) m) m)) (f b m)) m))).
surgery id_r ((f e (f (f (f e (f (f (f e m) m) m)) (f b m)) m))) ((f e (f (f (f e (f (f e m) m)) (f b m)) m))).
surgery id_r ((f e (f (f (f e (f (f e m) m)) (f b m)) m))) ((f e (f (f (f e (f e m)) (f b m)) m))).
surgery id_l ((f e (f (f (f e (f e m)) (f b m)) m))) ((f e (f (f (f e m) (f b m)) m))).
surgery id_r ((f e (f (f (f e m) (f b m)) m))) ((f e (f (f e (f b m)) m))).
surgery id_r ((f e (f (f e (f b m)) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_36: forall b: G, (((e <+> m) <+> (e <+> (e <+> m))) <+> ((e <+> (e <+> m)) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f e (f e m))) (f (f e (f e m)) (f e b)))) ((f (f e (f e (f e m))) (f (f e (f e m)) (f e b)))).
surgery id_l ((f (f e (f e (f e m))) (f (f e (f e m)) (f e b)))) ((f (f e (f e m)) (f (f e (f e m)) (f e b)))).
surgery id_l ((f (f e (f e m)) (f (f e (f e m)) (f e b)))) ((f (f e m) (f (f e (f e m)) (f e b)))).
surgery id_r ((f (f e m) (f (f e (f e m)) (f e b)))) ((f e (f (f e (f e m)) (f e b)))).
surgery id_l ((f e (f (f e (f e m)) (f e b)))) ((f e (f (f e m) (f e b)))).
surgery id_r ((f e (f (f e m) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_37: forall b: G, ((e <+> (e <+> (e <+> (e <+> ((b <+> m) <+> m))))) <+> ((e <+> m) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f e (f e (f e (f e (f (f b m) m))))) (f (f e m) m))) ((f (f e (f e (f e (f (f b m) m)))) (f (f e m) m))).
surgery id_l ((f (f e (f e (f e (f (f b m) m)))) (f (f e m) m))) ((f (f e (f e (f (f b m) m))) (f (f e m) m))).
surgery id_l ((f (f e (f e (f (f b m) m))) (f (f e m) m))) ((f (f e (f (f b m) m)) (f (f e m) m))).
surgery id_r ((f (f e (f (f b m) m)) (f (f e m) m))) ((f (f e (f b m)) (f (f e m) m))).
surgery id_r ((f (f e (f b m)) (f (f e m) m))) ((f (f e b) (f (f e m) m))).
surgery id_l ((f (f e b) (f (f e m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_38: forall b: G, (((((b <+> m) <+> m) <+> m) <+> (m <+> m)) <+> (m <+> ((e <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f b m) m) m) (f m m)) (f m (f (f e m) m)))) ((f (f (f (f b m) m) (f m m)) (f m (f (f e m) m)))).
surgery id_r ((f (f (f (f b m) m) (f m m)) (f m (f (f e m) m)))) ((f (f (f b m) (f m m)) (f m (f (f e m) m)))).
surgery id_r ((f (f (f b m) (f m m)) (f m (f (f e m) m)))) ((f (f b (f m m)) (f m (f (f e m) m)))).
surgery id_r ((f (f b (f m m)) (f m (f (f e m) m)))) ((f (f b m) (f m (f (f e m) m)))).
surgery id_r ((f (f b m) (f m (f (f e m) m)))) ((f b (f m (f (f e m) m)))).
surgery id_r ((f b (f m (f (f e m) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_39: forall b: G, ((((e <+> (e <+> e)) <+> e) <+> ((e <+> (m <+> m)) <+> b)) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e (f e e)) e) (f (f e (f m m)) b)) (f e m))) ((f (f (f (f e e) e) (f (f e (f m m)) b)) (f e m))).
surgery id_l ((f (f (f (f e e) e) (f (f e (f m m)) b)) (f e m))) ((f (f (f e e) (f (f e (f m m)) b)) (f e m))).
surgery id_l ((f (f (f e e) (f (f e (f m m)) b)) (f e m))) ((f (f e (f (f e (f m m)) b)) (f e m))).
surgery id_r ((f (f e (f (f e (f m m)) b)) (f e m))) ((f (f e (f (f e m) b)) (f e m))).
surgery id_r ((f (f e (f (f e m) b)) (f e m))) ((f (f e (f e b)) (f e m))).
surgery id_l ((f (f e (f e b)) (f e m))) ((f (f e b) (f e m))).
surgery id_l ((f (f e b) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_40: forall b: G, (((e <+> m) <+> e) <+> ((((e <+> b) <+> m) <+> m) <+> (m <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) e) (f (f (f (f e b) m) m) (f m (f m m))))) ((f (f e e) (f (f (f (f e b) m) m) (f m (f m m))))).
surgery id_l ((f (f e e) (f (f (f (f e b) m) m) (f m (f m m))))) ((f e (f (f (f (f e b) m) m) (f m (f m m))))).
surgery id_r ((f e (f (f (f (f e b) m) m) (f m (f m m))))) ((f e (f (f (f e b) m) (f m (f m m))))).
surgery id_r ((f e (f (f (f e b) m) (f m (f m m))))) ((f e (f (f e b) (f m (f m m))))).
surgery id_l ((f e (f (f e b) (f m (f m m))))) ((f e (f b (f m (f m m))))).
surgery id_r ((f e (f b (f m (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_41: forall b: G, ((e <+> (e <+> e)) <+> ((e <+> (e <+> e)) <+> ((e <+> e) <+> (e <+> b)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e e)) (f (f e (f e e)) (f (f e e) (f e b))))) ((f (f e e) (f (f e (f e e)) (f (f e e) (f e b))))).
surgery id_l ((f (f e e) (f (f e (f e e)) (f (f e e) (f e b))))) ((f e (f (f e (f e e)) (f (f e e) (f e b))))).
surgery id_l ((f e (f (f e (f e e)) (f (f e e) (f e b))))) ((f e (f (f e e) (f (f e e) (f e b))))).
surgery id_l ((f e (f (f e e) (f (f e e) (f e b))))) ((f e (f e (f (f e e) (f e b))))).
surgery id_l ((f e (f e (f (f e e) (f e b))))) ((f e (f (f e e) (f e b)))).
surgery id_l ((f e (f (f e e) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_42: forall b: G, ((b <+> ((e <+> m) <+> (m <+> m))) <+> ((e <+> e) <+> ((m <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b (f (f e m) (f m m))) (f (f e e) (f (f m m) m)))) ((f (f b (f e (f m m))) (f (f e e) (f (f m m) m)))).
surgery id_l ((f (f b (f e (f m m))) (f (f e e) (f (f m m) m)))) ((f (f b (f m m)) (f (f e e) (f (f m m) m)))).
surgery id_r ((f (f b (f m m)) (f (f e e) (f (f m m) m)))) ((f (f b m) (f (f e e) (f (f m m) m)))).
surgery id_r ((f (f b m) (f (f e e) (f (f m m) m)))) ((f b (f (f e e) (f (f m m) m)))).
surgery id_l ((f b (f (f e e) (f (f m m) m)))) ((f b (f e (f (f m m) m)))).
surgery id_l ((f b (f e (f (f m m) m)))) ((f b (f (f m m) m))).
surgery id_r ((f b (f (f m m) m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_43: forall b: G, ((e <+> ((e <+> m) <+> (m <+> ((e <+> m) <+> m)))) <+> (e <+> (b <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f e m) (f m (f (f e m) m)))) (f e (f b m)))) ((f (f e (f e (f m (f (f e m) m)))) (f e (f b m)))).
surgery id_l ((f (f e (f e (f m (f (f e m) m)))) (f e (f b m)))) ((f (f e (f m (f (f e m) m))) (f e (f b m)))).
surgery id_r ((f (f e (f m (f (f e m) m))) (f e (f b m)))) ((f (f e (f m (f e m))) (f e (f b m)))).
surgery id_l ((f (f e (f m (f e m))) (f e (f b m)))) ((f (f e (f m m)) (f e (f b m)))).
surgery id_r ((f (f e (f m m)) (f e (f b m)))) ((f (f e m) (f e (f b m)))).
surgery id_r ((f (f e m) (f e (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_44: forall b: G, ((((e <+> (e <+> b)) <+> ((((e <+> e) <+> m) <+> m) <+> m)) <+> m) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e (f e b)) (f (f (f (f e e) m) m) m)) m) m)) ((f (f (f e (f e b)) (f (f (f (f e e) m) m) m)) m)).
surgery id_r ((f (f (f e (f e b)) (f (f (f (f e e) m) m) m)) m)) ((f (f e (f e b)) (f (f (f (f e e) m) m) m))).
surgery id_l ((f (f e (f e b)) (f (f (f (f e e) m) m) m))) ((f (f e b) (f (f (f (f e e) m) m) m))).
surgery id_l ((f (f e b) (f (f (f (f e e) m) m) m))) ((f b (f (f (f (f e e) m) m) m))).
surgery id_r ((f b (f (f (f (f e e) m) m) m))) ((f b (f (f (f e e) m) m))).
surgery id_r ((f b (f (f (f e e) m) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_45: forall b: G, ((((e <+> b) <+> (e <+> m)) <+> m) <+> (e <+> (m <+> (e <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e b) (f e m)) m) (f e (f m (f e (f m m)))))) ((f (f (f e b) (f e m)) (f e (f m (f e (f m m)))))).
surgery id_l ((f (f (f e b) (f e m)) (f e (f m (f e (f m m)))))) ((f (f b (f e m)) (f e (f m (f e (f m m)))))).
surgery id_l ((f (f b (f e m)) (f e (f m (f e (f m m)))))) ((f (f b m) (f e (f m (f e (f m m)))))).
surgery id_r ((f (f b m) (f e (f m (f e (f m m)))))) ((f b (f e (f m (f e (f m m)))))).
surgery id_l ((f b (f e (f m (f e (f m m)))))) ((f b (f m (f e (f m m))))).
surgery id_l ((f b (f m (f e (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_46: forall b: G, (((e <+> ((e <+> m) <+> m)) <+> (e <+> (m <+> (e <+> m)))) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f e m) m)) (f e (f m (f e m)))) (f e b))) ((f (f (f e (f e m)) (f e (f m (f e m)))) (f e b))).
surgery id_l ((f (f (f e (f e m)) (f e (f m (f e m)))) (f e b))) ((f (f (f e m) (f e (f m (f e m)))) (f e b))).
surgery id_r ((f (f (f e m) (f e (f m (f e m)))) (f e b))) ((f (f e (f e (f m (f e m)))) (f e b))).
surgery id_l ((f (f e (f e (f m (f e m)))) (f e b))) ((f (f e (f m (f e m))) (f e b))).
surgery id_l ((f (f e (f m (f e m))) (f e b))) ((f (f e (f m m)) (f e b))).
surgery id_r ((f (f e (f m m)) (f e b))) ((f (f e m) (f e b))).
surgery id_r ((f (f e m) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_47: forall b: G, (((e <+> (e <+> m)) <+> e) <+> ((b <+> (m <+> (m <+> m))) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) e) (f (f b (f m (f m m))) (f e m)))) ((f (f (f e m) e) (f (f b (f m (f m m))) (f e m)))).
surgery id_r ((f (f (f e m) e) (f (f b (f m (f m m))) (f e m)))) ((f (f e e) (f (f b (f m (f m m))) (f e m)))).
surgery id_l ((f (f e e) (f (f b (f m (f m m))) (f e m)))) ((f e (f (f b (f m (f m m))) (f e m)))).
surgery id_r ((f e (f (f b (f m (f m m))) (f e m)))) ((f e (f (f b (f m m)) (f e m)))).
surgery id_r ((f e (f (f b (f m m)) (f e m)))) ((f e (f (f b m) (f e m)))).
surgery id_r ((f e (f (f b m) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_48: forall b: G, ((((e <+> m) <+> e) <+> (m <+> m)) <+> (b <+> (((e <+> e) <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) e) (f m m)) (f b (f (f (f e e) m) m)))) ((f (f (f e e) (f m m)) (f b (f (f (f e e) m) m)))).
surgery id_l ((f (f (f e e) (f m m)) (f b (f (f (f e e) m) m)))) ((f (f e (f m m)) (f b (f (f (f e e) m) m)))).
surgery id_r ((f (f e (f m m)) (f b (f (f (f e e) m) m)))) ((f (f e m) (f b (f (f (f e e) m) m)))).
surgery id_r ((f (f e m) (f b (f (f (f e e) m) m)))) ((f e (f b (f (f (f e e) m) m)))).
surgery id_r ((f e (f b (f (f (f e e) m) m)))) ((f e (f b (f (f e e) m)))).
surgery id_l ((f e (f b (f (f e e) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_49: forall b: G, ((((e <+> m) <+> b) <+> (((e <+> e) <+> (e <+> e)) <+> m)) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) b) (f (f (f e e) (f e e)) m)) (f e m))) ((f (f (f e b) (f (f (f e e) (f e e)) m)) (f e m))).
surgery id_l ((f (f (f e b) (f (f (f e e) (f e e)) m)) (f e m))) ((f (f b (f (f (f e e) (f e e)) m)) (f e m))).
surgery id_l ((f (f b (f (f (f e e) (f e e)) m)) (f e m))) ((f (f b (f (f e (f e e)) m)) (f e m))).
surgery id_l ((f (f b (f (f e (f e e)) m)) (f e m))) ((f (f b (f (f e e) m)) (f e m))).
surgery id_l ((f (f b (f (f e e) m)) (f e m))) ((f (f b (f e m)) (f e m))).
surgery id_l ((f (f b (f e m)) (f e m))) ((f (f b m) (f e m))).
surgery id_r ((f (f b m) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_50: forall b: G, ((b <+> (e <+> m)) <+> ((((e <+> m) <+> (e <+> (e <+> m))) <+> m) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f b (f e m)) (f (f (f (f e m) (f e (f e m))) m) m))) ((f (f b m) (f (f (f (f e m) (f e (f e m))) m) m))).
surgery id_r ((f (f b m) (f (f (f (f e m) (f e (f e m))) m) m))) ((f b (f (f (f (f e m) (f e (f e m))) m) m))).
surgery id_r ((f b (f (f (f (f e m) (f e (f e m))) m) m))) ((f b (f (f (f e m) (f e (f e m))) m))).
surgery id_r ((f b (f (f (f e m) (f e (f e m))) m))) ((f b (f (f e (f e (f e m))) m))).
surgery id_l ((f b (f (f e (f e (f e m))) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_51: forall b: G, (e <+> (((e <+> m) <+> m) <+> (b <+> ((e <+> m) <+> (e <+> (e <+> m)))))) = b.
Proof.
intros.
surgery id_r ((f e (f (f (f e m) m) (f b (f (f e m) (f e (f e m))))))) ((f e (f (f e m) (f b (f (f e m) (f e (f e m))))))).
surgery id_r ((f e (f (f e m) (f b (f (f e m) (f e (f e m))))))) ((f e (f e (f b (f (f e m) (f e (f e m))))))).
surgery id_l ((f e (f e (f b (f (f e m) (f e (f e m))))))) ((f e (f b (f (f e m) (f e (f e m)))))).
surgery id_r ((f e (f b (f (f e m) (f e (f e m)))))) ((f e (f b (f e (f e (f e m)))))).
surgery id_l ((f e (f b (f e (f e (f e m)))))) ((f e (f b (f e (f e m))))).
surgery id_l ((f e (f b (f e (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_52: forall b: G, ((e <+> (e <+> ((e <+> e) <+> e))) <+> ((e <+> m) <+> (b <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e (f (f e e) e))) (f (f e m) (f b (f m m))))) ((f (f e (f (f e e) e)) (f (f e m) (f b (f m m))))).
surgery id_l ((f (f e (f (f e e) e)) (f (f e m) (f b (f m m))))) ((f (f e (f e e)) (f (f e m) (f b (f m m))))).
surgery id_l ((f (f e (f e e)) (f (f e m) (f b (f m m))))) ((f (f e e) (f (f e m) (f b (f m m))))).
surgery id_l ((f (f e e) (f (f e m) (f b (f m m))))) ((f e (f (f e m) (f b (f m m))))).
surgery id_r ((f e (f (f e m) (f b (f m m))))) ((f e (f e (f b (f m m))))).
surgery id_l ((f e (f e (f b (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_53: forall b: G, (((((e <+> e) <+> m) <+> (m <+> m)) <+> b) <+> (m <+> ((e <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e e) m) (f m m)) b) (f m (f (f e m) m)))) ((f (f (f (f e e) (f m m)) b) (f m (f (f e m) m)))).
surgery id_l ((f (f (f (f e e) (f m m)) b) (f m (f (f e m) m)))) ((f (f (f e (f m m)) b) (f m (f (f e m) m)))).
surgery id_r ((f (f (f e (f m m)) b) (f m (f (f e m) m)))) ((f (f (f e m) b) (f m (f (f e m) m)))).
surgery id_r ((f (f (f e m) b) (f m (f (f e m) m)))) ((f (f e b) (f m (f (f e m) m)))).
surgery id_l ((f (f e b) (f m (f (f e m) m)))) ((f b (f m (f (f e m) m)))).
surgery id_r ((f b (f m (f (f e m) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_54: forall b: G, ((e <+> (((e <+> e) <+> e) <+> m)) <+> (e <+> ((e <+> (e <+> e)) <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f (f e e) e) m)) (f e (f (f e (f e e)) b)))) ((f (f e (f (f e e) m)) (f e (f (f e (f e e)) b)))).
surgery id_l ((f (f e (f (f e e) m)) (f e (f (f e (f e e)) b)))) ((f (f e (f e m)) (f e (f (f e (f e e)) b)))).
surgery id_l ((f (f e (f e m)) (f e (f (f e (f e e)) b)))) ((f (f e m) (f e (f (f e (f e e)) b)))).
surgery id_r ((f (f e m) (f e (f (f e (f e e)) b)))) ((f e (f e (f (f e (f e e)) b)))).
surgery id_l ((f e (f e (f (f e (f e e)) b)))) ((f e (f (f e (f e e)) b))).
surgery id_l ((f e (f (f e (f e e)) b))) ((f e (f (f e e) b))).
surgery id_l ((f e (f (f e e) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_55: forall b: G, ((e <+> b) <+> (((m <+> m) <+> (e <+> ((e <+> m) <+> m))) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f (f (f m m) (f e (f (f e m) m))) (f e m)))) ((f b (f (f (f m m) (f e (f (f e m) m))) (f e m)))).
surgery id_r ((f b (f (f (f m m) (f e (f (f e m) m))) (f e m)))) ((f b (f (f m (f e (f (f e m) m))) (f e m)))).
surgery id_l ((f b (f (f m (f e (f (f e m) m))) (f e m)))) ((f b (f (f m (f (f e m) m)) (f e m)))).
surgery id_r ((f b (f (f m (f (f e m) m)) (f e m)))) ((f b (f (f m (f e m)) (f e m)))).
surgery id_l ((f b (f (f m (f e m)) (f e m)))) ((f b (f (f m m) (f e m)))).
surgery id_r ((f b (f (f m m) (f e m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_56: forall b: G, ((e <+> m) <+> ((e <+> b) <+> ((e <+> (m <+> m)) <+> ((e <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f e b) (f (f e (f m m)) (f (f e m) m))))) ((f e (f (f e b) (f (f e (f m m)) (f (f e m) m))))).
surgery id_l ((f e (f (f e b) (f (f e (f m m)) (f (f e m) m))))) ((f e (f b (f (f e (f m m)) (f (f e m) m))))).
surgery id_r ((f e (f b (f (f e (f m m)) (f (f e m) m))))) ((f e (f b (f (f e m) (f (f e m) m))))).
surgery id_r ((f e (f b (f (f e m) (f (f e m) m))))) ((f e (f b (f e (f (f e m) m))))).
surgery id_l ((f e (f b (f e (f (f e m) m))))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_57: forall b: G, ((b <+> m) <+> (((e <+> (e <+> m)) <+> ((e <+> e) <+> (e <+> m))) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f (f e (f e m)) (f (f e e) (f e m))) m))) ((f b (f (f (f e (f e m)) (f (f e e) (f e m))) m))).
surgery id_l ((f b (f (f (f e (f e m)) (f (f e e) (f e m))) m))) ((f b (f (f (f e m) (f (f e e) (f e m))) m))).
surgery id_r ((f b (f (f (f e m) (f (f e e) (f e m))) m))) ((f b (f (f e (f (f e e) (f e m))) m))).
surgery id_l ((f b (f (f e (f (f e e) (f e m))) m))) ((f b (f (f e (f e (f e m))) m))).
surgery id_l ((f b (f (f e (f e (f e m))) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_58: forall b: G, (e <+> (((((e <+> m) <+> e) <+> m) <+> (b <+> m)) <+> ((m <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f e (f (f (f (f (f e m) e) m) (f b m)) (f (f m m) m)))) ((f e (f (f (f (f e m) e) (f b m)) (f (f m m) m)))).
surgery id_r ((f e (f (f (f (f e m) e) (f b m)) (f (f m m) m)))) ((f e (f (f (f e e) (f b m)) (f (f m m) m)))).
surgery id_l ((f e (f (f (f e e) (f b m)) (f (f m m) m)))) ((f e (f (f e (f b m)) (f (f m m) m)))).
surgery id_r ((f e (f (f e (f b m)) (f (f m m) m)))) ((f e (f (f e b) (f (f m m) m)))).
surgery id_l ((f e (f (f e b) (f (f m m) m)))) ((f e (f b (f (f m m) m)))).
surgery id_r ((f e (f b (f (f m m) m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_59: forall b: G, ((e <+> ((e <+> m) <+> (((e <+> e) <+> e) <+> ((e <+> m) <+> m)))) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f e m) (f (f (f e e) e) (f (f e m) m)))) b)) ((f (f e (f e (f (f (f e e) e) (f (f e m) m)))) b)).
surgery id_l ((f (f e (f e (f (f (f e e) e) (f (f e m) m)))) b)) ((f (f e (f (f (f e e) e) (f (f e m) m))) b)).
surgery id_l ((f (f e (f (f (f e e) e) (f (f e m) m))) b)) ((f (f e (f (f e e) (f (f e m) m))) b)).
surgery id_l ((f (f e (f (f e e) (f (f e m) m))) b)) ((f (f e (f e (f (f e m) m))) b)).
surgery id_l ((f (f e (f e (f (f e m) m))) b)) ((f (f e (f (f e m) m)) b)).
surgery id_r ((f (f e (f (f e m) m)) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_60: forall b: G, (((e <+> e) <+> (((e <+> m) <+> (b <+> m)) <+> ((e <+> m) <+> m))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f e e) (f (f (f e m) (f b m)) (f (f e m) m))) m)) ((f (f e e) (f (f (f e m) (f b m)) (f (f e m) m)))).
surgery id_l ((f (f e e) (f (f (f e m) (f b m)) (f (f e m) m)))) ((f e (f (f (f e m) (f b m)) (f (f e m) m)))).
surgery id_r ((f e (f (f (f e m) (f b m)) (f (f e m) m)))) ((f e (f (f e (f b m)) (f (f e m) m)))).
surgery id_r ((f e (f (f e (f b m)) (f (f e m) m)))) ((f e (f (f e b) (f (f e m) m)))).
surgery id_l ((f e (f (f e b) (f (f e m) m)))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_61: forall b: G, ((((e <+> e) <+> e) <+> m) <+> ((e <+> m) <+> (b <+> ((e <+> e) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) e) m) (f (f e m) (f b (f (f e e) m))))) ((f (f (f e e) e) (f (f e m) (f b (f (f e e) m))))).
surgery id_l ((f (f (f e e) e) (f (f e m) (f b (f (f e e) m))))) ((f (f e e) (f (f e m) (f b (f (f e e) m))))).
surgery id_l ((f (f e e) (f (f e m) (f b (f (f e e) m))))) ((f e (f (f e m) (f b (f (f e e) m))))).
surgery id_r ((f e (f (f e m) (f b (f (f e e) m))))) ((f e (f e (f b (f (f e e) m))))).
surgery id_l ((f e (f e (f b (f (f e e) m))))) ((f e (f b (f (f e e) m)))).
surgery id_l ((f e (f b (f (f e e) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_62: forall b: G, ((e <+> b) <+> ((((e <+> (m <+> (m <+> m))) <+> m) <+> (m <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f (f (f (f e (f m (f m m))) m) (f m m)) m))) ((f b (f (f (f (f e (f m (f m m))) m) (f m m)) m))).
surgery id_r ((f b (f (f (f (f e (f m (f m m))) m) (f m m)) m))) ((f b (f (f (f e (f m (f m m))) (f m m)) m))).
surgery id_r ((f b (f (f (f e (f m (f m m))) (f m m)) m))) ((f b (f (f (f e (f m m)) (f m m)) m))).
surgery id_r ((f b (f (f (f e (f m m)) (f m m)) m))) ((f b (f (f (f e m) (f m m)) m))).
surgery id_r ((f b (f (f (f e m) (f m m)) m))) ((f b (f (f e (f m m)) m))).
surgery id_r ((f b (f (f e (f m m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_63: forall b: G, ((e <+> b) <+> (m <+> ((m <+> m) <+> (((m <+> (e <+> m)) <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f m (f (f m m) (f (f (f m (f e m)) m) m))))) ((f b (f m (f (f m m) (f (f (f m (f e m)) m) m))))).
surgery id_r ((f b (f m (f (f m m) (f (f (f m (f e m)) m) m))))) ((f b (f m (f m (f (f (f m (f e m)) m) m))))).
surgery id_r ((f b (f m (f m (f (f (f m (f e m)) m) m))))) ((f b (f m (f m (f (f m (f e m)) m))))).
surgery id_l ((f b (f m (f m (f (f m (f e m)) m))))) ((f b (f m (f m (f (f m m) m))))).
surgery id_r ((f b (f m (f m (f (f m m) m))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_64: forall b: G, (b <+> (((e <+> (e <+> m)) <+> ((e <+> m) <+> (e <+> (e <+> m)))) <+> m)) = b.
Proof.
intros.
surgery id_l ((f b (f (f (f e (f e m)) (f (f e m) (f e (f e m)))) m))) ((f b (f (f (f e m) (f (f e m) (f e (f e m)))) m))).
surgery id_r ((f b (f (f (f e m) (f (f e m) (f e (f e m)))) m))) ((f b (f (f e (f (f e m) (f e (f e m)))) m))).
surgery id_r ((f b (f (f e (f (f e m) (f e (f e m)))) m))) ((f b (f (f e (f e (f e (f e m)))) m))).
surgery id_l ((f b (f (f e (f e (f e (f e m)))) m))) ((f b (f (f e (f e (f e m))) m))).
surgery id_l ((f b (f (f e (f e (f e m))) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_65: forall b: G, ((e <+> (m <+> m)) <+> ((((e <+> m) <+> e) <+> (e <+> m)) <+> (b <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f m m)) (f (f (f (f e m) e) (f e m)) (f b m)))) ((f (f e m) (f (f (f (f e m) e) (f e m)) (f b m)))).
surgery id_r ((f (f e m) (f (f (f (f e m) e) (f e m)) (f b m)))) ((f e (f (f (f (f e m) e) (f e m)) (f b m)))).
surgery id_r ((f e (f (f (f (f e m) e) (f e m)) (f b m)))) ((f e (f (f (f e e) (f e m)) (f b m)))).
surgery id_l ((f e (f (f (f e e) (f e m)) (f b m)))) ((f e (f (f e (f e m)) (f b m)))).
surgery id_l ((f e (f (f e (f e m)) (f b m)))) ((f e (f (f e m) (f b m)))).
surgery id_r ((f e (f (f e m) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_66: forall b: G, ((e <+> b) <+> ((m <+> m) <+> (((e <+> e) <+> e) <+> (e <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f (f m m) (f (f (f e e) e) (f e (f m m)))))) ((f b (f (f m m) (f (f (f e e) e) (f e (f m m)))))).
surgery id_r ((f b (f (f m m) (f (f (f e e) e) (f e (f m m)))))) ((f b (f m (f (f (f e e) e) (f e (f m m)))))).
surgery id_l ((f b (f m (f (f (f e e) e) (f e (f m m)))))) ((f b (f m (f (f e e) (f e (f m m)))))).
surgery id_l ((f b (f m (f (f e e) (f e (f m m)))))) ((f b (f m (f e (f e (f m m)))))).
surgery id_l ((f b (f m (f e (f e (f m m)))))) ((f b (f m (f e (f m m))))).
surgery id_l ((f b (f m (f e (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_67: forall b: G, (((e <+> m) <+> (e <+> ((e <+> e) <+> e))) <+> ((e <+> (b <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f e (f (f e e) e))) (f (f e (f b m)) m))) ((f (f e (f e (f (f e e) e))) (f (f e (f b m)) m))).
surgery id_l ((f (f e (f e (f (f e e) e))) (f (f e (f b m)) m))) ((f (f e (f (f e e) e)) (f (f e (f b m)) m))).
surgery id_l ((f (f e (f (f e e) e)) (f (f e (f b m)) m))) ((f (f e (f e e)) (f (f e (f b m)) m))).
surgery id_l ((f (f e (f e e)) (f (f e (f b m)) m))) ((f (f e e) (f (f e (f b m)) m))).
surgery id_l ((f (f e e) (f (f e (f b m)) m))) ((f e (f (f e (f b m)) m))).
surgery id_r ((f e (f (f e (f b m)) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_68: forall b: G, (((e <+> (e <+> b)) <+> ((e <+> ((e <+> e) <+> e)) <+> m)) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e b)) (f (f e (f (f e e) e)) m)) (f m m))) ((f (f (f e b) (f (f e (f (f e e) e)) m)) (f m m))).
surgery id_l ((f (f (f e b) (f (f e (f (f e e) e)) m)) (f m m))) ((f (f b (f (f e (f (f e e) e)) m)) (f m m))).
surgery id_l ((f (f b (f (f e (f (f e e) e)) m)) (f m m))) ((f (f b (f (f e (f e e)) m)) (f m m))).
surgery id_l ((f (f b (f (f e (f e e)) m)) (f m m))) ((f (f b (f (f e e) m)) (f m m))).
surgery id_l ((f (f b (f (f e e) m)) (f m m))) ((f (f b (f e m)) (f m m))).
surgery id_l ((f (f b (f e m)) (f m m))) ((f (f b m) (f m m))).
surgery id_r ((f (f b m) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_69: forall b: G, ((e <+> (e <+> m)) <+> (((e <+> (m <+> m)) <+> ((m <+> m) <+> m)) <+> b)) = b.
Proof.
intros.
surgery id_l ((f (f e (f e m)) (f (f (f e (f m m)) (f (f m m) m)) b))) ((f (f e m) (f (f (f e (f m m)) (f (f m m) m)) b))).
surgery id_r ((f (f e m) (f (f (f e (f m m)) (f (f m m) m)) b))) ((f e (f (f (f e (f m m)) (f (f m m) m)) b))).
surgery id_r ((f e (f (f (f e (f m m)) (f (f m m) m)) b))) ((f e (f (f (f e m) (f (f m m) m)) b))).
surgery id_r ((f e (f (f (f e m) (f (f m m) m)) b))) ((f e (f (f e (f (f m m) m)) b))).
surgery id_r ((f e (f (f e (f (f m m) m)) b))) ((f e (f (f e (f m m)) b))).
surgery id_r ((f e (f (f e (f m m)) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_70: forall b: G, ((b <+> ((e <+> (((e <+> m) <+> m) <+> m)) <+> m)) <+> ((e <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f b (f (f e (f (f (f e m) m) m)) m)) (f (f e m) m))) ((f (f b (f (f e (f (f e m) m)) m)) (f (f e m) m))).
surgery id_r ((f (f b (f (f e (f (f e m) m)) m)) (f (f e m) m))) ((f (f b (f (f e (f e m)) m)) (f (f e m) m))).
surgery id_l ((f (f b (f (f e (f e m)) m)) (f (f e m) m))) ((f (f b (f (f e m) m)) (f (f e m) m))).
surgery id_r ((f (f b (f (f e m) m)) (f (f e m) m))) ((f (f b (f e m)) (f (f e m) m))).
surgery id_l ((f (f b (f e m)) (f (f e m) m))) ((f (f b m) (f (f e m) m))).
surgery id_r ((f (f b m) (f (f e m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_71: forall b: G, (((e <+> e) <+> ((e <+> m) <+> e)) <+> ((e <+> (e <+> (m <+> m))) <+> b)) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f e m) e)) (f (f e (f e (f m m))) b))) ((f (f e (f (f e m) e)) (f (f e (f e (f m m))) b))).
surgery id_r ((f (f e (f (f e m) e)) (f (f e (f e (f m m))) b))) ((f (f e (f e e)) (f (f e (f e (f m m))) b))).
surgery id_l ((f (f e (f e e)) (f (f e (f e (f m m))) b))) ((f (f e e) (f (f e (f e (f m m))) b))).
surgery id_l ((f (f e e) (f (f e (f e (f m m))) b))) ((f e (f (f e (f e (f m m))) b))).
surgery id_l ((f e (f (f e (f e (f m m))) b))) ((f e (f (f e (f m m)) b))).
surgery id_r ((f e (f (f e (f m m)) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_72: forall b: G, (((e <+> e) <+> b) <+> (e <+> ((e <+> e) <+> ((e <+> (e <+> m)) <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) b) (f e (f (f e e) (f (f e (f e m)) m))))) ((f (f e b) (f e (f (f e e) (f (f e (f e m)) m))))).
surgery id_l ((f (f e b) (f e (f (f e e) (f (f e (f e m)) m))))) ((f b (f e (f (f e e) (f (f e (f e m)) m))))).
surgery id_l ((f b (f e (f (f e e) (f (f e (f e m)) m))))) ((f b (f (f e e) (f (f e (f e m)) m)))).
surgery id_l ((f b (f (f e e) (f (f e (f e m)) m)))) ((f b (f e (f (f e (f e m)) m)))).
surgery id_l ((f b (f e (f (f e (f e m)) m)))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_73: forall b: G, ((((e <+> e) <+> (b <+> m)) <+> ((e <+> e) <+> m)) <+> ((e <+> e) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) (f b m)) (f (f e e) m)) (f (f e e) m))) ((f (f (f e (f b m)) (f (f e e) m)) (f (f e e) m))).
surgery id_r ((f (f (f e (f b m)) (f (f e e) m)) (f (f e e) m))) ((f (f (f e b) (f (f e e) m)) (f (f e e) m))).
surgery id_l ((f (f (f e b) (f (f e e) m)) (f (f e e) m))) ((f (f b (f (f e e) m)) (f (f e e) m))).
surgery id_l ((f (f b (f (f e e) m)) (f (f e e) m))) ((f (f b (f e m)) (f (f e e) m))).
surgery id_l ((f (f b (f e m)) (f (f e e) m))) ((f (f b m) (f (f e e) m))).
surgery id_r ((f (f b m) (f (f e e) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_74: forall b: G, ((b <+> (m <+> m)) <+> ((((e <+> e) <+> m) <+> (e <+> m)) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b (f m m)) (f (f (f (f e e) m) (f e m)) (f e m)))) ((f (f b m) (f (f (f (f e e) m) (f e m)) (f e m)))).
surgery id_r ((f (f b m) (f (f (f (f e e) m) (f e m)) (f e m)))) ((f b (f (f (f (f e e) m) (f e m)) (f e m)))).
surgery id_r ((f b (f (f (f (f e e) m) (f e m)) (f e m)))) ((f b (f (f (f e e) (f e m)) (f e m)))).
surgery id_l ((f b (f (f (f e e) (f e m)) (f e m)))) ((f b (f (f e (f e m)) (f e m)))).
surgery id_l ((f b (f (f e (f e m)) (f e m)))) ((f b (f (f e m) (f e m)))).
surgery id_r ((f b (f (f e m) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_75: forall b: G, (((b <+> (e <+> (m <+> m))) <+> ((m <+> m) <+> m)) <+> (m <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f b (f e (f m m))) (f (f m m) m)) (f m (f m m)))) ((f (f (f b (f m m)) (f (f m m) m)) (f m (f m m)))).
surgery id_r ((f (f (f b (f m m)) (f (f m m) m)) (f m (f m m)))) ((f (f (f b m) (f (f m m) m)) (f m (f m m)))).
surgery id_r ((f (f (f b m) (f (f m m) m)) (f m (f m m)))) ((f (f b (f (f m m) m)) (f m (f m m)))).
surgery id_r ((f (f b (f (f m m) m)) (f m (f m m)))) ((f (f b (f m m)) (f m (f m m)))).
surgery id_r ((f (f b (f m m)) (f m (f m m)))) ((f (f b m) (f m (f m m)))).
surgery id_r ((f (f b m) (f m (f m m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_76: forall b: G, (b <+> ((e <+> m) <+> ((((e <+> e) <+> ((e <+> m) <+> m)) <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f b (f (f e m) (f (f (f (f e e) (f (f e m) m)) m) m)))) ((f b (f e (f (f (f (f e e) (f (f e m) m)) m) m)))).
surgery id_l ((f b (f e (f (f (f (f e e) (f (f e m) m)) m) m)))) ((f b (f (f (f (f e e) (f (f e m) m)) m) m))).
surgery id_r ((f b (f (f (f (f e e) (f (f e m) m)) m) m))) ((f b (f (f (f e e) (f (f e m) m)) m))).
surgery id_l ((f b (f (f (f e e) (f (f e m) m)) m))) ((f b (f (f e (f (f e m) m)) m))).
surgery id_r ((f b (f (f e (f (f e m) m)) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_77: forall b: G, (((b <+> (m <+> (e <+> m))) <+> ((e <+> m) <+> (m <+> m))) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f b (f m (f e m))) (f (f e m) (f m m))) (f e m))) ((f (f (f b (f m m)) (f (f e m) (f m m))) (f e m))).
surgery id_r ((f (f (f b (f m m)) (f (f e m) (f m m))) (f e m))) ((f (f (f b m) (f (f e m) (f m m))) (f e m))).
surgery id_r ((f (f (f b m) (f (f e m) (f m m))) (f e m))) ((f (f b (f (f e m) (f m m))) (f e m))).
surgery id_r ((f (f b (f (f e m) (f m m))) (f e m))) ((f (f b (f e (f m m))) (f e m))).
surgery id_l ((f (f b (f e (f m m))) (f e m))) ((f (f b (f m m)) (f e m))).
surgery id_r ((f (f b (f m m)) (f e m))) ((f (f b m) (f e m))).
surgery id_r ((f (f b m) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_78: forall b: G, ((e <+> ((e <+> (e <+> m)) <+> m)) <+> (e <+> (b <+> ((e <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f e (f e m)) m)) (f e (f b (f (f e m) m))))) ((f (f e (f (f e m) m)) (f e (f b (f (f e m) m))))).
surgery id_r ((f (f e (f (f e m) m)) (f e (f b (f (f e m) m))))) ((f (f e (f e m)) (f e (f b (f (f e m) m))))).
surgery id_l ((f (f e (f e m)) (f e (f b (f (f e m) m))))) ((f (f e m) (f e (f b (f (f e m) m))))).
surgery id_r ((f (f e m) (f e (f b (f (f e m) m))))) ((f e (f e (f b (f (f e m) m))))).
surgery id_l ((f e (f e (f b (f (f e m) m))))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_79: forall b: G, ((((e <+> ((e <+> m) <+> (e <+> m))) <+> e) <+> (e <+> e)) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e (f (f e m) (f e m))) e) (f e e)) (f e b))) ((f (f (f (f e (f e (f e m))) e) (f e e)) (f e b))).
surgery id_l ((f (f (f (f e (f e (f e m))) e) (f e e)) (f e b))) ((f (f (f (f e (f e m)) e) (f e e)) (f e b))).
surgery id_l ((f (f (f (f e (f e m)) e) (f e e)) (f e b))) ((f (f (f (f e m) e) (f e e)) (f e b))).
surgery id_r ((f (f (f (f e m) e) (f e e)) (f e b))) ((f (f (f e e) (f e e)) (f e b))).
surgery id_l ((f (f (f e e) (f e e)) (f e b))) ((f (f e (f e e)) (f e b))).
surgery id_l ((f (f e (f e e)) (f e b))) ((f (f e e) (f e b))).
surgery id_l ((f (f e e) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_80: forall b: G, ((((b <+> (e <+> m)) <+> (m <+> m)) <+> m) <+> ((e <+> e) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f b (f e m)) (f m m)) m) (f (f e e) (f e m)))) ((f (f (f b (f e m)) (f m m)) (f (f e e) (f e m)))).
surgery id_l ((f (f (f b (f e m)) (f m m)) (f (f e e) (f e m)))) ((f (f (f b m) (f m m)) (f (f e e) (f e m)))).
surgery id_r ((f (f (f b m) (f m m)) (f (f e e) (f e m)))) ((f (f b (f m m)) (f (f e e) (f e m)))).
surgery id_r ((f (f b (f m m)) (f (f e e) (f e m)))) ((f (f b m) (f (f e e) (f e m)))).
surgery id_r ((f (f b m) (f (f e e) (f e m)))) ((f b (f (f e e) (f e m)))).
surgery id_l ((f b (f (f e e) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_81: forall b: G, (((e <+> b) <+> (e <+> ((((e <+> m) <+> e) <+> (e <+> m)) <+> m))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f e b) (f e (f (f (f (f e m) e) (f e m)) m))) m)) ((f (f e b) (f e (f (f (f (f e m) e) (f e m)) m)))).
surgery id_l ((f (f e b) (f e (f (f (f (f e m) e) (f e m)) m)))) ((f b (f e (f (f (f (f e m) e) (f e m)) m)))).
surgery id_l ((f b (f e (f (f (f (f e m) e) (f e m)) m)))) ((f b (f (f (f (f e m) e) (f e m)) m))).
surgery id_r ((f b (f (f (f (f e m) e) (f e m)) m))) ((f b (f (f (f e e) (f e m)) m))).
surgery id_l ((f b (f (f (f e e) (f e m)) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_82: forall b: G, (((e <+> m) <+> (e <+> m)) <+> (((e <+> e) <+> (e <+> (e <+> b))) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f e m)) (f (f (f e e) (f e (f e b))) m))) ((f (f e (f e m)) (f (f (f e e) (f e (f e b))) m))).
surgery id_l ((f (f e (f e m)) (f (f (f e e) (f e (f e b))) m))) ((f (f e m) (f (f (f e e) (f e (f e b))) m))).
surgery id_r ((f (f e m) (f (f (f e e) (f e (f e b))) m))) ((f e (f (f (f e e) (f e (f e b))) m))).
surgery id_l ((f e (f (f (f e e) (f e (f e b))) m))) ((f e (f (f e (f e (f e b))) m))).
surgery id_l ((f e (f (f e (f e (f e b))) m))) ((f e (f (f e (f e b)) m))).
surgery id_l ((f e (f (f e (f e b)) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_83: forall b: G, ((e <+> (b <+> m)) <+> (((e <+> m) <+> (e <+> m)) <+> (m <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e (f b m)) (f (f (f e m) (f e m)) (f m (f m m))))) ((f (f e b) (f (f (f e m) (f e m)) (f m (f m m))))).
surgery id_l ((f (f e b) (f (f (f e m) (f e m)) (f m (f m m))))) ((f b (f (f (f e m) (f e m)) (f m (f m m))))).
surgery id_r ((f b (f (f (f e m) (f e m)) (f m (f m m))))) ((f b (f (f e (f e m)) (f m (f m m))))).
surgery id_l ((f b (f (f e (f e m)) (f m (f m m))))) ((f b (f (f e m) (f m (f m m))))).
surgery id_r ((f b (f (f e m) (f m (f m m))))) ((f b (f e (f m (f m m))))).
surgery id_l ((f b (f e (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_84: forall b: G, ((e <+> (e <+> (e <+> ((m <+> m) <+> m)))) <+> ((e <+> (b <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f e (f e (f e (f (f m m) m)))) (f (f e (f b m)) m))) ((f (f e (f e (f (f m m) m))) (f (f e (f b m)) m))).
surgery id_l ((f (f e (f e (f (f m m) m))) (f (f e (f b m)) m))) ((f (f e (f (f m m) m)) (f (f e (f b m)) m))).
surgery id_r ((f (f e (f (f m m) m)) (f (f e (f b m)) m))) ((f (f e (f m m)) (f (f e (f b m)) m))).
surgery id_r ((f (f e (f m m)) (f (f e (f b m)) m))) ((f (f e m) (f (f e (f b m)) m))).
surgery id_r ((f (f e m) (f (f e (f b m)) m))) ((f e (f (f e (f b m)) m))).
surgery id_r ((f e (f (f e (f b m)) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_85: forall b: G, ((e <+> (((e <+> m) <+> m) <+> m)) <+> (((e <+> e) <+> e) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f (f e m) m) m)) (f (f (f e e) e) (f e b)))) ((f (f e (f (f e m) m)) (f (f (f e e) e) (f e b)))).
surgery id_r ((f (f e (f (f e m) m)) (f (f (f e e) e) (f e b)))) ((f (f e (f e m)) (f (f (f e e) e) (f e b)))).
surgery id_l ((f (f e (f e m)) (f (f (f e e) e) (f e b)))) ((f (f e m) (f (f (f e e) e) (f e b)))).
surgery id_r ((f (f e m) (f (f (f e e) e) (f e b)))) ((f e (f (f (f e e) e) (f e b)))).
surgery id_l ((f e (f (f (f e e) e) (f e b)))) ((f e (f (f e e) (f e b)))).
surgery id_l ((f e (f (f e e) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_86: forall b: G, ((((e <+> m) <+> (e <+> m)) <+> ((e <+> m) <+> ((e <+> m) <+> m))) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f e m)) (f (f e m) (f (f e m) m))) b)) ((f (f (f e (f e m)) (f (f e m) (f (f e m) m))) b)).
surgery id_l ((f (f (f e (f e m)) (f (f e m) (f (f e m) m))) b)) ((f (f (f e m) (f (f e m) (f (f e m) m))) b)).
surgery id_r ((f (f (f e m) (f (f e m) (f (f e m) m))) b)) ((f (f e (f (f e m) (f (f e m) m))) b)).
surgery id_r ((f (f e (f (f e m) (f (f e m) m))) b)) ((f (f e (f e (f (f e m) m))) b)).
surgery id_l ((f (f e (f e (f (f e m) m))) b)) ((f (f e (f (f e m) m)) b)).
surgery id_r ((f (f e (f (f e m) m)) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_87: forall b: G, ((b <+> (m <+> m)) <+> (((e <+> m) <+> m) <+> (((m <+> m) <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b (f m m)) (f (f (f e m) m) (f (f (f m m) m) m)))) ((f (f b m) (f (f (f e m) m) (f (f (f m m) m) m)))).
surgery id_r ((f (f b m) (f (f (f e m) m) (f (f (f m m) m) m)))) ((f b (f (f (f e m) m) (f (f (f m m) m) m)))).
surgery id_r ((f b (f (f (f e m) m) (f (f (f m m) m) m)))) ((f b (f (f e m) (f (f (f m m) m) m)))).
surgery id_r ((f b (f (f e m) (f (f (f m m) m) m)))) ((f b (f e (f (f (f m m) m) m)))).
surgery id_l ((f b (f e (f (f (f m m) m) m)))) ((f b (f (f (f m m) m) m))).
surgery id_r ((f b (f (f (f m m) m) m))) ((f b (f (f m m) m))).
surgery id_r ((f b (f (f m m) m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_88: forall b: G, (((e <+> m) <+> ((e <+> m) <+> e)) <+> (((e <+> b) <+> m) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f (f e m) e)) (f (f (f e b) m) (f m m)))) ((f (f e (f (f e m) e)) (f (f (f e b) m) (f m m)))).
surgery id_r ((f (f e (f (f e m) e)) (f (f (f e b) m) (f m m)))) ((f (f e (f e e)) (f (f (f e b) m) (f m m)))).
surgery id_l ((f (f e (f e e)) (f (f (f e b) m) (f m m)))) ((f (f e e) (f (f (f e b) m) (f m m)))).
surgery id_l ((f (f e e) (f (f (f e b) m) (f m m)))) ((f e (f (f (f e b) m) (f m m)))).
surgery id_r ((f e (f (f (f e b) m) (f m m)))) ((f e (f (f e b) (f m m)))).
surgery id_l ((f e (f (f e b) (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_89: forall b: G, ((((e <+> e) <+> m) <+> (((b <+> m) <+> m) <+> m)) <+> (e <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) (f (f (f b m) m) m)) (f e (f m m)))) ((f (f (f e e) (f (f (f b m) m) m)) (f e (f m m)))).
surgery id_l ((f (f (f e e) (f (f (f b m) m) m)) (f e (f m m)))) ((f (f e (f (f (f b m) m) m)) (f e (f m m)))).
surgery id_r ((f (f e (f (f (f b m) m) m)) (f e (f m m)))) ((f (f e (f (f b m) m)) (f e (f m m)))).
surgery id_r ((f (f e (f (f b m) m)) (f e (f m m)))) ((f (f e (f b m)) (f e (f m m)))).
surgery id_r ((f (f e (f b m)) (f e (f m m)))) ((f (f e b) (f e (f m m)))).
surgery id_l ((f (f e b) (f e (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_90: forall b: G, (b <+> ((e <+> m) <+> ((e <+> m) <+> (((e <+> (e <+> e)) <+> e) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f b (f (f e m) (f (f e m) (f (f (f e (f e e)) e) m))))) ((f b (f e (f (f e m) (f (f (f e (f e e)) e) m))))).
surgery id_l ((f b (f e (f (f e m) (f (f (f e (f e e)) e) m))))) ((f b (f (f e m) (f (f (f e (f e e)) e) m)))).
surgery id_r ((f b (f (f e m) (f (f (f e (f e e)) e) m)))) ((f b (f e (f (f (f e (f e e)) e) m)))).
surgery id_l ((f b (f e (f (f (f e (f e e)) e) m)))) ((f b (f (f (f e (f e e)) e) m))).
surgery id_l ((f b (f (f (f e (f e e)) e) m))) ((f b (f (f (f e e) e) m))).
surgery id_l ((f b (f (f (f e e) e) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_91: forall b: G, (((e <+> m) <+> ((e <+> e) <+> (m <+> m))) <+> (b <+> ((e <+> e) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f (f e e) (f m m))) (f b (f (f e e) m)))) ((f (f e (f (f e e) (f m m))) (f b (f (f e e) m)))).
surgery id_l ((f (f e (f (f e e) (f m m))) (f b (f (f e e) m)))) ((f (f e (f e (f m m))) (f b (f (f e e) m)))).
surgery id_l ((f (f e (f e (f m m))) (f b (f (f e e) m)))) ((f (f e (f m m)) (f b (f (f e e) m)))).
surgery id_r ((f (f e (f m m)) (f b (f (f e e) m)))) ((f (f e m) (f b (f (f e e) m)))).
surgery id_r ((f (f e m) (f b (f (f e e) m)))) ((f e (f b (f (f e e) m)))).
surgery id_l ((f e (f b (f (f e e) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_92: forall b: G, ((b <+> (e <+> (e <+> (m <+> m)))) <+> (((e <+> e) <+> (e <+> e)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f b (f e (f e (f m m)))) (f (f (f e e) (f e e)) m))) ((f (f b (f e (f m m))) (f (f (f e e) (f e e)) m))).
surgery id_l ((f (f b (f e (f m m))) (f (f (f e e) (f e e)) m))) ((f (f b (f m m)) (f (f (f e e) (f e e)) m))).
surgery id_r ((f (f b (f m m)) (f (f (f e e) (f e e)) m))) ((f (f b m) (f (f (f e e) (f e e)) m))).
surgery id_r ((f (f b m) (f (f (f e e) (f e e)) m))) ((f b (f (f (f e e) (f e e)) m))).
surgery id_l ((f b (f (f (f e e) (f e e)) m))) ((f b (f (f e (f e e)) m))).
surgery id_l ((f b (f (f e (f e e)) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_93: forall b: G, (((e <+> ((e <+> m) <+> m)) <+> (e <+> b)) <+> (((m <+> m) <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f e m) m)) (f e b)) (f (f (f m m) m) m))) ((f (f (f e (f e m)) (f e b)) (f (f (f m m) m) m))).
surgery id_l ((f (f (f e (f e m)) (f e b)) (f (f (f m m) m) m))) ((f (f (f e m) (f e b)) (f (f (f m m) m) m))).
surgery id_r ((f (f (f e m) (f e b)) (f (f (f m m) m) m))) ((f (f e (f e b)) (f (f (f m m) m) m))).
surgery id_l ((f (f e (f e b)) (f (f (f m m) m) m))) ((f (f e b) (f (f (f m m) m) m))).
surgery id_l ((f (f e b) (f (f (f m m) m) m))) ((f b (f (f (f m m) m) m))).
surgery id_r ((f b (f (f (f m m) m) m))) ((f b (f (f m m) m))).
surgery id_r ((f b (f (f m m) m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_94: forall b: G, ((e <+> b) <+> ((m <+> m) <+> (m <+> (m <+> ((e <+> m) <+> (m <+> m)))))) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f (f m m) (f m (f m (f (f e m) (f m m))))))) ((f b (f (f m m) (f m (f m (f (f e m) (f m m))))))).
surgery id_r ((f b (f (f m m) (f m (f m (f (f e m) (f m m))))))) ((f b (f m (f m (f m (f (f e m) (f m m))))))).
surgery id_r ((f b (f m (f m (f m (f (f e m) (f m m))))))) ((f b (f m (f m (f m (f e (f m m))))))).
surgery id_l ((f b (f m (f m (f m (f e (f m m))))))) ((f b (f m (f m (f m (f m m)))))).
surgery id_r ((f b (f m (f m (f m (f m m)))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_95: forall b: G, ((e <+> e) <+> ((b <+> m) <+> ((e <+> (e <+> m)) <+> ((e <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f b m) (f (f e (f e m)) (f (f e m) m))))) ((f e (f (f b m) (f (f e (f e m)) (f (f e m) m))))).
surgery id_r ((f e (f (f b m) (f (f e (f e m)) (f (f e m) m))))) ((f e (f b (f (f e (f e m)) (f (f e m) m))))).
surgery id_l ((f e (f b (f (f e (f e m)) (f (f e m) m))))) ((f e (f b (f (f e m) (f (f e m) m))))).
surgery id_r ((f e (f b (f (f e m) (f (f e m) m))))) ((f e (f b (f e (f (f e m) m))))).
surgery id_l ((f e (f b (f e (f (f e m) m))))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_96: forall b: G, ((e <+> e) <+> ((e <+> (b <+> (e <+> m))) <+> (m <+> (m <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f e (f b (f e m))) (f m (f m (f m m)))))) ((f e (f (f e (f b (f e m))) (f m (f m (f m m)))))).
surgery id_l ((f e (f (f e (f b (f e m))) (f m (f m (f m m)))))) ((f e (f (f e (f b m)) (f m (f m (f m m)))))).
surgery id_r ((f e (f (f e (f b m)) (f m (f m (f m m)))))) ((f e (f (f e b) (f m (f m (f m m)))))).
surgery id_l ((f e (f (f e b) (f m (f m (f m m)))))) ((f e (f b (f m (f m (f m m)))))).
surgery id_r ((f e (f b (f m (f m (f m m)))))) ((f e (f b (f m (f m m))))).
surgery id_r ((f e (f b (f m (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_97: forall b: G, ((((e <+> (e <+> m)) <+> (e <+> (e <+> (e <+> e)))) <+> b) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e (f e m)) (f e (f e (f e e)))) b) (f m m))) ((f (f (f (f e m) (f e (f e (f e e)))) b) (f m m))).
surgery id_r ((f (f (f (f e m) (f e (f e (f e e)))) b) (f m m))) ((f (f (f e (f e (f e (f e e)))) b) (f m m))).
surgery id_l ((f (f (f e (f e (f e (f e e)))) b) (f m m))) ((f (f (f e (f e (f e e))) b) (f m m))).
surgery id_l ((f (f (f e (f e (f e e))) b) (f m m))) ((f (f (f e (f e e)) b) (f m m))).
surgery id_l ((f (f (f e (f e e)) b) (f m m))) ((f (f (f e e) b) (f m m))).
surgery id_l ((f (f (f e e) b) (f m m))) ((f (f e b) (f m m))).
surgery id_l ((f (f e b) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_98: forall b: G, ((e <+> m) <+> ((e <+> e) <+> ((b <+> m) <+> (((m <+> m) <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f e e) (f (f b m) (f (f (f m m) m) m))))) ((f e (f (f e e) (f (f b m) (f (f (f m m) m) m))))).
surgery id_l ((f e (f (f e e) (f (f b m) (f (f (f m m) m) m))))) ((f e (f e (f (f b m) (f (f (f m m) m) m))))).
surgery id_l ((f e (f e (f (f b m) (f (f (f m m) m) m))))) ((f e (f (f b m) (f (f (f m m) m) m)))).
surgery id_r ((f e (f (f b m) (f (f (f m m) m) m)))) ((f e (f b (f (f (f m m) m) m)))).
surgery id_r ((f e (f b (f (f (f m m) m) m)))) ((f e (f b (f (f m m) m)))).
surgery id_r ((f e (f b (f (f m m) m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_99: forall b: G, (((e <+> e) <+> ((((e <+> e) <+> m) <+> (e <+> b)) <+> m)) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f (f (f e e) m) (f e b)) m)) (f m m))) ((f (f e (f (f (f (f e e) m) (f e b)) m)) (f m m))).
surgery id_r ((f (f e (f (f (f (f e e) m) (f e b)) m)) (f m m))) ((f (f e (f (f (f e e) (f e b)) m)) (f m m))).
surgery id_l ((f (f e (f (f (f e e) (f e b)) m)) (f m m))) ((f (f e (f (f e (f e b)) m)) (f m m))).
surgery id_l ((f (f e (f (f e (f e b)) m)) (f m m))) ((f (f e (f (f e b) m)) (f m m))).
surgery id_l ((f (f e (f (f e b) m)) (f m m))) ((f (f e (f b m)) (f m m))).
surgery id_r ((f (f e (f b m)) (f m m))) ((f (f e b) (f m m))).
surgery id_l ((f (f e b) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_100: forall b: G, (e <+> (((e <+> m) <+> ((((e <+> m) <+> m) <+> e) <+> m)) <+> (b <+> m))) = b.
Proof.
intros.
surgery id_r ((f e (f (f (f e m) (f (f (f (f e m) m) e) m)) (f b m)))) ((f e (f (f e (f (f (f (f e m) m) e) m)) (f b m)))).
surgery id_r ((f e (f (f e (f (f (f (f e m) m) e) m)) (f b m)))) ((f e (f (f e (f (f (f e m) e) m)) (f b m)))).
surgery id_r ((f e (f (f e (f (f (f e m) e) m)) (f b m)))) ((f e (f (f e (f (f e e) m)) (f b m)))).
surgery id_l ((f e (f (f e (f (f e e) m)) (f b m)))) ((f e (f (f e (f e m)) (f b m)))).
surgery id_l ((f e (f (f e (f e m)) (f b m)))) ((f e (f (f e m) (f b m)))).
surgery id_r ((f e (f (f e m) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_101: forall b: G, (((((e <+> m) <+> e) <+> (m <+> m)) <+> (b <+> (m <+> m))) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e m) e) (f m m)) (f b (f m m))) (f m m))) ((f (f (f (f e e) (f m m)) (f b (f m m))) (f m m))).
surgery id_l ((f (f (f (f e e) (f m m)) (f b (f m m))) (f m m))) ((f (f (f e (f m m)) (f b (f m m))) (f m m))).
surgery id_r ((f (f (f e (f m m)) (f b (f m m))) (f m m))) ((f (f (f e m) (f b (f m m))) (f m m))).
surgery id_r ((f (f (f e m) (f b (f m m))) (f m m))) ((f (f e (f b (f m m))) (f m m))).
surgery id_r ((f (f e (f b (f m m))) (f m m))) ((f (f e (f b m)) (f m m))).
surgery id_r ((f (f e (f b m)) (f m m))) ((f (f e b) (f m m))).
surgery id_l ((f (f e b) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_102: forall b: G, ((((((e <+> e) <+> m) <+> (e <+> e)) <+> (e <+> m)) <+> (m <+> m)) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f (f e e) m) (f e e)) (f e m)) (f m m)) b)) ((f (f (f (f (f e e) (f e e)) (f e m)) (f m m)) b)).
surgery id_l ((f (f (f (f (f e e) (f e e)) (f e m)) (f m m)) b)) ((f (f (f (f e (f e e)) (f e m)) (f m m)) b)).
surgery id_l ((f (f (f (f e (f e e)) (f e m)) (f m m)) b)) ((f (f (f (f e e) (f e m)) (f m m)) b)).
surgery id_l ((f (f (f (f e e) (f e m)) (f m m)) b)) ((f (f (f e (f e m)) (f m m)) b)).
surgery id_l ((f (f (f e (f e m)) (f m m)) b)) ((f (f (f e m) (f m m)) b)).
surgery id_r ((f (f (f e m) (f m m)) b)) ((f (f e (f m m)) b)).
surgery id_r ((f (f e (f m m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_103: forall b: G, (((e <+> (e <+> m)) <+> (m <+> (e <+> m))) <+> ((b <+> (e <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f m (f e m))) (f (f b (f e m)) m))) ((f (f (f e m) (f m (f e m))) (f (f b (f e m)) m))).
surgery id_r ((f (f (f e m) (f m (f e m))) (f (f b (f e m)) m))) ((f (f e (f m (f e m))) (f (f b (f e m)) m))).
surgery id_l ((f (f e (f m (f e m))) (f (f b (f e m)) m))) ((f (f e (f m m)) (f (f b (f e m)) m))).
surgery id_r ((f (f e (f m m)) (f (f b (f e m)) m))) ((f (f e m) (f (f b (f e m)) m))).
surgery id_r ((f (f e m) (f (f b (f e m)) m))) ((f e (f (f b (f e m)) m))).
surgery id_l ((f e (f (f b (f e m)) m))) ((f e (f (f b m) m))).
surgery id_r ((f e (f (f b m) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_104: forall b: G, ((((e <+> e) <+> (m <+> (e <+> m))) <+> (e <+> m)) <+> ((e <+> b) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) (f m (f e m))) (f e m)) (f (f e b) m))) ((f (f (f e (f m (f e m))) (f e m)) (f (f e b) m))).
surgery id_l ((f (f (f e (f m (f e m))) (f e m)) (f (f e b) m))) ((f (f (f e (f m m)) (f e m)) (f (f e b) m))).
surgery id_r ((f (f (f e (f m m)) (f e m)) (f (f e b) m))) ((f (f (f e m) (f e m)) (f (f e b) m))).
surgery id_r ((f (f (f e m) (f e m)) (f (f e b) m))) ((f (f e (f e m)) (f (f e b) m))).
surgery id_l ((f (f e (f e m)) (f (f e b) m))) ((f (f e m) (f (f e b) m))).
surgery id_r ((f (f e m) (f (f e b) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_105: forall b: G, (((e <+> b) <+> (e <+> m)) <+> ((e <+> (e <+> m)) <+> ((e <+> e) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e b) (f e m)) (f (f e (f e m)) (f (f e e) m)))) ((f (f b (f e m)) (f (f e (f e m)) (f (f e e) m)))).
surgery id_l ((f (f b (f e m)) (f (f e (f e m)) (f (f e e) m)))) ((f (f b m) (f (f e (f e m)) (f (f e e) m)))).
surgery id_r ((f (f b m) (f (f e (f e m)) (f (f e e) m)))) ((f b (f (f e (f e m)) (f (f e e) m)))).
surgery id_l ((f b (f (f e (f e m)) (f (f e e) m)))) ((f b (f (f e m) (f (f e e) m)))).
surgery id_r ((f b (f (f e m) (f (f e e) m)))) ((f b (f e (f (f e e) m)))).
surgery id_l ((f b (f e (f (f e e) m)))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_106: forall b: G, (e <+> ((e <+> (e <+> e)) <+> ((b <+> ((e <+> m) <+> m)) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f e (f (f e (f e e)) (f (f b (f (f e m) m)) (f m m))))) ((f e (f (f e e) (f (f b (f (f e m) m)) (f m m))))).
surgery id_l ((f e (f (f e e) (f (f b (f (f e m) m)) (f m m))))) ((f e (f e (f (f b (f (f e m) m)) (f m m))))).
surgery id_l ((f e (f e (f (f b (f (f e m) m)) (f m m))))) ((f e (f (f b (f (f e m) m)) (f m m)))).
surgery id_r ((f e (f (f b (f (f e m) m)) (f m m)))) ((f e (f (f b (f e m)) (f m m)))).
surgery id_l ((f e (f (f b (f e m)) (f m m)))) ((f e (f (f b m) (f m m)))).
surgery id_r ((f e (f (f b m) (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_107: forall b: G, ((((e <+> e) <+> (m <+> m)) <+> m) <+> (b <+> ((e <+> m) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) (f m m)) m) (f b (f (f e m) (f e m))))) ((f (f (f e e) (f m m)) (f b (f (f e m) (f e m))))).
surgery id_l ((f (f (f e e) (f m m)) (f b (f (f e m) (f e m))))) ((f (f e (f m m)) (f b (f (f e m) (f e m))))).
surgery id_r ((f (f e (f m m)) (f b (f (f e m) (f e m))))) ((f (f e m) (f b (f (f e m) (f e m))))).
surgery id_r ((f (f e m) (f b (f (f e m) (f e m))))) ((f e (f b (f (f e m) (f e m))))).
surgery id_r ((f e (f b (f (f e m) (f e m))))) ((f e (f b (f e (f e m))))).
surgery id_l ((f e (f b (f e (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_108: forall b: G, ((((e <+> (e <+> (e <+> e))) <+> e) <+> ((e <+> m) <+> m)) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e (f e (f e e))) e) (f (f e m) m)) (f b m))) ((f (f (f (f e (f e e)) e) (f (f e m) m)) (f b m))).
surgery id_l ((f (f (f (f e (f e e)) e) (f (f e m) m)) (f b m))) ((f (f (f (f e e) e) (f (f e m) m)) (f b m))).
surgery id_l ((f (f (f (f e e) e) (f (f e m) m)) (f b m))) ((f (f (f e e) (f (f e m) m)) (f b m))).
surgery id_l ((f (f (f e e) (f (f e m) m)) (f b m))) ((f (f e (f (f e m) m)) (f b m))).
surgery id_r ((f (f e (f (f e m) m)) (f b m))) ((f (f e (f e m)) (f b m))).
surgery id_l ((f (f e (f e m)) (f b m))) ((f (f e m) (f b m))).
surgery id_r ((f (f e m) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_109: forall b: G, (b <+> ((e <+> e) <+> (((e <+> e) <+> ((e <+> m) <+> (e <+> m))) <+> m))) = b.
Proof.
intros.
surgery id_l ((f b (f (f e e) (f (f (f e e) (f (f e m) (f e m))) m)))) ((f b (f e (f (f (f e e) (f (f e m) (f e m))) m)))).
surgery id_l ((f b (f e (f (f (f e e) (f (f e m) (f e m))) m)))) ((f b (f (f (f e e) (f (f e m) (f e m))) m))).
surgery id_l ((f b (f (f (f e e) (f (f e m) (f e m))) m))) ((f b (f (f e (f (f e m) (f e m))) m))).
surgery id_r ((f b (f (f e (f (f e m) (f e m))) m))) ((f b (f (f e (f e (f e m))) m))).
surgery id_l ((f b (f (f e (f e (f e m))) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_110: forall b: G, (((e <+> e) <+> (m <+> (e <+> m))) <+> (((e <+> e) <+> e) <+> (b <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f m (f e m))) (f (f (f e e) e) (f b m)))) ((f (f e (f m (f e m))) (f (f (f e e) e) (f b m)))).
surgery id_l ((f (f e (f m (f e m))) (f (f (f e e) e) (f b m)))) ((f (f e (f m m)) (f (f (f e e) e) (f b m)))).
surgery id_r ((f (f e (f m m)) (f (f (f e e) e) (f b m)))) ((f (f e m) (f (f (f e e) e) (f b m)))).
surgery id_r ((f (f e m) (f (f (f e e) e) (f b m)))) ((f e (f (f (f e e) e) (f b m)))).
surgery id_l ((f e (f (f (f e e) e) (f b m)))) ((f e (f (f e e) (f b m)))).
surgery id_l ((f e (f (f e e) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_111: forall b: G, ((e <+> (m <+> m)) <+> ((e <+> (e <+> (e <+> (e <+> e)))) <+> (b <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f m m)) (f (f e (f e (f e (f e e)))) (f b m)))) ((f (f e m) (f (f e (f e (f e (f e e)))) (f b m)))).
surgery id_r ((f (f e m) (f (f e (f e (f e (f e e)))) (f b m)))) ((f e (f (f e (f e (f e (f e e)))) (f b m)))).
surgery id_l ((f e (f (f e (f e (f e (f e e)))) (f b m)))) ((f e (f (f e (f e (f e e))) (f b m)))).
surgery id_l ((f e (f (f e (f e (f e e))) (f b m)))) ((f e (f (f e (f e e)) (f b m)))).
surgery id_l ((f e (f (f e (f e e)) (f b m)))) ((f e (f (f e e) (f b m)))).
surgery id_l ((f e (f (f e e) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_112: forall b: G, ((e <+> (e <+> m)) <+> ((((e <+> e) <+> e) <+> m) <+> (e <+> (e <+> b)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e m)) (f (f (f (f e e) e) m) (f e (f e b))))) ((f (f e m) (f (f (f (f e e) e) m) (f e (f e b))))).
surgery id_r ((f (f e m) (f (f (f (f e e) e) m) (f e (f e b))))) ((f e (f (f (f (f e e) e) m) (f e (f e b))))).
surgery id_r ((f e (f (f (f (f e e) e) m) (f e (f e b))))) ((f e (f (f (f e e) e) (f e (f e b))))).
surgery id_l ((f e (f (f (f e e) e) (f e (f e b))))) ((f e (f (f e e) (f e (f e b))))).
surgery id_l ((f e (f (f e e) (f e (f e b))))) ((f e (f e (f e (f e b))))).
surgery id_l ((f e (f e (f e (f e b))))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_113: forall b: G, (((b <+> m) <+> m) <+> ((((e <+> m) <+> (m <+> m)) <+> m) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) m) (f (f (f (f e m) (f m m)) m) (f m m)))) ((f (f b m) (f (f (f (f e m) (f m m)) m) (f m m)))).
surgery id_r ((f (f b m) (f (f (f (f e m) (f m m)) m) (f m m)))) ((f b (f (f (f (f e m) (f m m)) m) (f m m)))).
surgery id_r ((f b (f (f (f (f e m) (f m m)) m) (f m m)))) ((f b (f (f (f e m) (f m m)) (f m m)))).
surgery id_r ((f b (f (f (f e m) (f m m)) (f m m)))) ((f b (f (f e (f m m)) (f m m)))).
surgery id_r ((f b (f (f e (f m m)) (f m m)))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_114: forall b: G, (((e <+> (m <+> m)) <+> m) <+> ((e <+> (m <+> m)) <+> ((b <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f m m)) m) (f (f e (f m m)) (f (f b m) m)))) ((f (f e (f m m)) (f (f e (f m m)) (f (f b m) m)))).
surgery id_r ((f (f e (f m m)) (f (f e (f m m)) (f (f b m) m)))) ((f (f e m) (f (f e (f m m)) (f (f b m) m)))).
surgery id_r ((f (f e m) (f (f e (f m m)) (f (f b m) m)))) ((f e (f (f e (f m m)) (f (f b m) m)))).
surgery id_r ((f e (f (f e (f m m)) (f (f b m) m)))) ((f e (f (f e m) (f (f b m) m)))).
surgery id_r ((f e (f (f e m) (f (f b m) m)))) ((f e (f e (f (f b m) m)))).
surgery id_l ((f e (f e (f (f b m) m)))) ((f e (f (f b m) m))).
surgery id_r ((f e (f (f b m) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_115: forall b: G, ((e <+> (((e <+> m) <+> e) <+> m)) <+> (e <+> (e <+> ((e <+> m) <+> b)))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f (f e m) e) m)) (f e (f e (f (f e m) b))))) ((f (f e (f (f e e) m)) (f e (f e (f (f e m) b))))).
surgery id_l ((f (f e (f (f e e) m)) (f e (f e (f (f e m) b))))) ((f (f e (f e m)) (f e (f e (f (f e m) b))))).
surgery id_l ((f (f e (f e m)) (f e (f e (f (f e m) b))))) ((f (f e m) (f e (f e (f (f e m) b))))).
surgery id_r ((f (f e m) (f e (f e (f (f e m) b))))) ((f e (f e (f e (f (f e m) b))))).
surgery id_l ((f e (f e (f e (f (f e m) b))))) ((f e (f e (f (f e m) b)))).
surgery id_l ((f e (f e (f (f e m) b)))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_116: forall b: G, (((((e <+> (m <+> m)) <+> (m <+> ((e <+> e) <+> m))) <+> m) <+> e) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e (f m m)) (f m (f (f e e) m))) m) e) b)) ((f (f (f (f e (f m m)) (f m (f (f e e) m))) e) b)).
surgery id_r ((f (f (f (f e (f m m)) (f m (f (f e e) m))) e) b)) ((f (f (f (f e m) (f m (f (f e e) m))) e) b)).
surgery id_r ((f (f (f (f e m) (f m (f (f e e) m))) e) b)) ((f (f (f e (f m (f (f e e) m))) e) b)).
surgery id_l ((f (f (f e (f m (f (f e e) m))) e) b)) ((f (f (f e (f m (f e m))) e) b)).
surgery id_l ((f (f (f e (f m (f e m))) e) b)) ((f (f (f e (f m m)) e) b)).
surgery id_r ((f (f (f e (f m m)) e) b)) ((f (f (f e m) e) b)).
surgery id_r ((f (f (f e m) e) b)) ((f (f e e) b)).
surgery id_l ((f (f e e) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_117: forall b: G, ((e <+> ((e <+> m) <+> m)) <+> ((e <+> b) <+> ((e <+> (e <+> m)) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f e m) m)) (f (f e b) (f (f e (f e m)) m)))) ((f (f e (f e m)) (f (f e b) (f (f e (f e m)) m)))).
surgery id_l ((f (f e (f e m)) (f (f e b) (f (f e (f e m)) m)))) ((f (f e m) (f (f e b) (f (f e (f e m)) m)))).
surgery id_r ((f (f e m) (f (f e b) (f (f e (f e m)) m)))) ((f e (f (f e b) (f (f e (f e m)) m)))).
surgery id_l ((f e (f (f e b) (f (f e (f e m)) m)))) ((f e (f b (f (f e (f e m)) m)))).
surgery id_l ((f e (f b (f (f e (f e m)) m)))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_118: forall b: G, ((((e <+> e) <+> b) <+> (m <+> m)) <+> ((e <+> m) <+> (e <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) b) (f m m)) (f (f e m) (f e (f m m))))) ((f (f (f e b) (f m m)) (f (f e m) (f e (f m m))))).
surgery id_l ((f (f (f e b) (f m m)) (f (f e m) (f e (f m m))))) ((f (f b (f m m)) (f (f e m) (f e (f m m))))).
surgery id_r ((f (f b (f m m)) (f (f e m) (f e (f m m))))) ((f (f b m) (f (f e m) (f e (f m m))))).
surgery id_r ((f (f b m) (f (f e m) (f e (f m m))))) ((f b (f (f e m) (f e (f m m))))).
surgery id_r ((f b (f (f e m) (f e (f m m))))) ((f b (f e (f e (f m m))))).
surgery id_l ((f b (f e (f e (f m m))))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_119: forall b: G, (((((e <+> e) <+> m) <+> m) <+> (e <+> (b <+> (e <+> m)))) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e e) m) m) (f e (f b (f e m)))) (f m m))) ((f (f (f (f e e) m) (f e (f b (f e m)))) (f m m))).
surgery id_r ((f (f (f (f e e) m) (f e (f b (f e m)))) (f m m))) ((f (f (f e e) (f e (f b (f e m)))) (f m m))).
surgery id_l ((f (f (f e e) (f e (f b (f e m)))) (f m m))) ((f (f e (f e (f b (f e m)))) (f m m))).
surgery id_l ((f (f e (f e (f b (f e m)))) (f m m))) ((f (f e (f b (f e m))) (f m m))).
surgery id_l ((f (f e (f b (f e m))) (f m m))) ((f (f e (f b m)) (f m m))).
surgery id_r ((f (f e (f b m)) (f m m))) ((f (f e b) (f m m))).
surgery id_l ((f (f e b) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_120: forall b: G, (e <+> (((e <+> m) <+> (e <+> (m <+> ((e <+> e) <+> m)))) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_r ((f e (f (f (f e m) (f e (f m (f (f e e) m)))) (f e b)))) ((f e (f (f e (f e (f m (f (f e e) m)))) (f e b)))).
surgery id_l ((f e (f (f e (f e (f m (f (f e e) m)))) (f e b)))) ((f e (f (f e (f m (f (f e e) m))) (f e b)))).
surgery id_l ((f e (f (f e (f m (f (f e e) m))) (f e b)))) ((f e (f (f e (f m (f e m))) (f e b)))).
surgery id_l ((f e (f (f e (f m (f e m))) (f e b)))) ((f e (f (f e (f m m)) (f e b)))).
surgery id_r ((f e (f (f e (f m m)) (f e b)))) ((f e (f (f e m) (f e b)))).
surgery id_r ((f e (f (f e m) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_121: forall b: G, (((e <+> m) <+> e) <+> ((e <+> (e <+> (e <+> ((e <+> m) <+> m)))) <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) e) (f (f e (f e (f e (f (f e m) m)))) b))) ((f (f e e) (f (f e (f e (f e (f (f e m) m)))) b))).
surgery id_l ((f (f e e) (f (f e (f e (f e (f (f e m) m)))) b))) ((f e (f (f e (f e (f e (f (f e m) m)))) b))).
surgery id_l ((f e (f (f e (f e (f e (f (f e m) m)))) b))) ((f e (f (f e (f e (f (f e m) m))) b))).
surgery id_l ((f e (f (f e (f e (f (f e m) m))) b))) ((f e (f (f e (f (f e m) m)) b))).
surgery id_r ((f e (f (f e (f (f e m) m)) b))) ((f e (f (f e (f e m)) b))).
surgery id_l ((f e (f (f e (f e m)) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_122: forall b: G, (((e <+> e) <+> (m <+> (m <+> m))) <+> ((e <+> m) <+> (b <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f m (f m m))) (f (f e m) (f b (f e m))))) ((f (f e (f m (f m m))) (f (f e m) (f b (f e m))))).
surgery id_r ((f (f e (f m (f m m))) (f (f e m) (f b (f e m))))) ((f (f e (f m m)) (f (f e m) (f b (f e m))))).
surgery id_r ((f (f e (f m m)) (f (f e m) (f b (f e m))))) ((f (f e m) (f (f e m) (f b (f e m))))).
surgery id_r ((f (f e m) (f (f e m) (f b (f e m))))) ((f e (f (f e m) (f b (f e m))))).
surgery id_r ((f e (f (f e m) (f b (f e m))))) ((f e (f e (f b (f e m))))).
surgery id_l ((f e (f e (f b (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_123: forall b: G, (((e <+> ((m <+> m) <+> (e <+> m))) <+> ((e <+> m) <+> m)) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f m m) (f e m))) (f (f e m) m)) (f b m))) ((f (f (f e (f m (f e m))) (f (f e m) m)) (f b m))).
surgery id_l ((f (f (f e (f m (f e m))) (f (f e m) m)) (f b m))) ((f (f (f e (f m m)) (f (f e m) m)) (f b m))).
surgery id_r ((f (f (f e (f m m)) (f (f e m) m)) (f b m))) ((f (f (f e m) (f (f e m) m)) (f b m))).
surgery id_r ((f (f (f e m) (f (f e m) m)) (f b m))) ((f (f e (f (f e m) m)) (f b m))).
surgery id_r ((f (f e (f (f e m) m)) (f b m))) ((f (f e (f e m)) (f b m))).
surgery id_l ((f (f e (f e m)) (f b m))) ((f (f e m) (f b m))).
surgery id_r ((f (f e m) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_124: forall b: G, ((e <+> ((((e <+> m) <+> m) <+> m) <+> m)) <+> (b <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f (f (f e m) m) m) m)) (f b (f e (f e m))))) ((f (f e (f (f (f e m) m) m)) (f b (f e (f e m))))).
surgery id_r ((f (f e (f (f (f e m) m) m)) (f b (f e (f e m))))) ((f (f e (f (f e m) m)) (f b (f e (f e m))))).
surgery id_r ((f (f e (f (f e m) m)) (f b (f e (f e m))))) ((f (f e (f e m)) (f b (f e (f e m))))).
surgery id_l ((f (f e (f e m)) (f b (f e (f e m))))) ((f (f e m) (f b (f e (f e m))))).
surgery id_r ((f (f e m) (f b (f e (f e m))))) ((f e (f b (f e (f e m))))).
surgery id_l ((f e (f b (f e (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_125: forall b: G, (((e <+> (m <+> m)) <+> m) <+> (e <+> ((((e <+> b) <+> m) <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f m m)) m) (f e (f (f (f (f e b) m) m) m)))) ((f (f e (f m m)) (f e (f (f (f (f e b) m) m) m)))).
surgery id_r ((f (f e (f m m)) (f e (f (f (f (f e b) m) m) m)))) ((f (f e m) (f e (f (f (f (f e b) m) m) m)))).
surgery id_r ((f (f e m) (f e (f (f (f (f e b) m) m) m)))) ((f e (f e (f (f (f (f e b) m) m) m)))).
surgery id_l ((f e (f e (f (f (f (f e b) m) m) m)))) ((f e (f (f (f (f e b) m) m) m))).
surgery id_r ((f e (f (f (f (f e b) m) m) m))) ((f e (f (f (f e b) m) m))).
surgery id_r ((f e (f (f (f e b) m) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_126: forall b: G, ((e <+> ((e <+> m) <+> b)) <+> ((m <+> m) <+> ((e <+> m) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f e m) b)) (f (f m m) (f (f e m) (f e m))))) ((f (f e (f e b)) (f (f m m) (f (f e m) (f e m))))).
surgery id_l ((f (f e (f e b)) (f (f m m) (f (f e m) (f e m))))) ((f (f e b) (f (f m m) (f (f e m) (f e m))))).
surgery id_l ((f (f e b) (f (f m m) (f (f e m) (f e m))))) ((f b (f (f m m) (f (f e m) (f e m))))).
surgery id_r ((f b (f (f m m) (f (f e m) (f e m))))) ((f b (f m (f (f e m) (f e m))))).
surgery id_r ((f b (f m (f (f e m) (f e m))))) ((f b (f m (f e (f e m))))).
surgery id_l ((f b (f m (f e (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_127: forall b: G, ((b <+> (m <+> m)) <+> (e <+> (((((e <+> m) <+> m) <+> m) <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b (f m m)) (f e (f (f (f (f (f e m) m) m) m) m)))) ((f (f b m) (f e (f (f (f (f (f e m) m) m) m) m)))).
surgery id_r ((f (f b m) (f e (f (f (f (f (f e m) m) m) m) m)))) ((f b (f e (f (f (f (f (f e m) m) m) m) m)))).
surgery id_l ((f b (f e (f (f (f (f (f e m) m) m) m) m)))) ((f b (f (f (f (f (f e m) m) m) m) m))).
surgery id_r ((f b (f (f (f (f (f e m) m) m) m) m))) ((f b (f (f (f (f e m) m) m) m))).
surgery id_r ((f b (f (f (f (f e m) m) m) m))) ((f b (f (f (f e m) m) m))).
surgery id_r ((f b (f (f (f e m) m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_128: forall b: G, (e <+> (((b <+> (e <+> (e <+> m))) <+> (m <+> (e <+> m))) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f e (f (f (f b (f e (f e m))) (f m (f e m))) (f m m)))) ((f e (f (f (f b (f e m)) (f m (f e m))) (f m m)))).
surgery id_l ((f e (f (f (f b (f e m)) (f m (f e m))) (f m m)))) ((f e (f (f (f b m) (f m (f e m))) (f m m)))).
surgery id_r ((f e (f (f (f b m) (f m (f e m))) (f m m)))) ((f e (f (f b (f m (f e m))) (f m m)))).
surgery id_l ((f e (f (f b (f m (f e m))) (f m m)))) ((f e (f (f b (f m m)) (f m m)))).
surgery id_r ((f e (f (f b (f m m)) (f m m)))) ((f e (f (f b m) (f m m)))).
surgery id_r ((f e (f (f b m) (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_129: forall b: G, (((e <+> b) <+> m) <+> ((e <+> (m <+> ((e <+> m) <+> m))) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e b) m) (f (f e (f m (f (f e m) m))) (f m m)))) ((f (f e b) (f (f e (f m (f (f e m) m))) (f m m)))).
surgery id_l ((f (f e b) (f (f e (f m (f (f e m) m))) (f m m)))) ((f b (f (f e (f m (f (f e m) m))) (f m m)))).
surgery id_r ((f b (f (f e (f m (f (f e m) m))) (f m m)))) ((f b (f (f e (f m (f e m))) (f m m)))).
surgery id_l ((f b (f (f e (f m (f e m))) (f m m)))) ((f b (f (f e (f m m)) (f m m)))).
surgery id_r ((f b (f (f e (f m m)) (f m m)))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_130: forall b: G, (((((e <+> m) <+> m) <+> m) <+> ((e <+> e) <+> b)) <+> (e <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e m) m) m) (f (f e e) b)) (f e (f e m)))) ((f (f (f (f e m) m) (f (f e e) b)) (f e (f e m)))).
surgery id_r ((f (f (f (f e m) m) (f (f e e) b)) (f e (f e m)))) ((f (f (f e m) (f (f e e) b)) (f e (f e m)))).
surgery id_r ((f (f (f e m) (f (f e e) b)) (f e (f e m)))) ((f (f e (f (f e e) b)) (f e (f e m)))).
surgery id_l ((f (f e (f (f e e) b)) (f e (f e m)))) ((f (f e (f e b)) (f e (f e m)))).
surgery id_l ((f (f e (f e b)) (f e (f e m)))) ((f (f e b) (f e (f e m)))).
surgery id_l ((f (f e b) (f e (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_131: forall b: G, (b <+> (((m <+> m) <+> m) <+> ((e <+> (e <+> e)) <+> ((e <+> e) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f b (f (f (f m m) m) (f (f e (f e e)) (f (f e e) m))))) ((f b (f (f m m) (f (f e (f e e)) (f (f e e) m))))).
surgery id_r ((f b (f (f m m) (f (f e (f e e)) (f (f e e) m))))) ((f b (f m (f (f e (f e e)) (f (f e e) m))))).
surgery id_l ((f b (f m (f (f e (f e e)) (f (f e e) m))))) ((f b (f m (f (f e e) (f (f e e) m))))).
surgery id_l ((f b (f m (f (f e e) (f (f e e) m))))) ((f b (f m (f e (f (f e e) m))))).
surgery id_l ((f b (f m (f e (f (f e e) m))))) ((f b (f m (f (f e e) m)))).
surgery id_l ((f b (f m (f (f e e) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_132: forall b: G, (((((e <+> e) <+> e) <+> m) <+> (e <+> (e <+> ((e <+> m) <+> m)))) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e e) e) m) (f e (f e (f (f e m) m)))) b)) ((f (f (f (f e e) e) (f e (f e (f (f e m) m)))) b)).
surgery id_l ((f (f (f (f e e) e) (f e (f e (f (f e m) m)))) b)) ((f (f (f e e) (f e (f e (f (f e m) m)))) b)).
surgery id_l ((f (f (f e e) (f e (f e (f (f e m) m)))) b)) ((f (f e (f e (f e (f (f e m) m)))) b)).
surgery id_l ((f (f e (f e (f e (f (f e m) m)))) b)) ((f (f e (f e (f (f e m) m))) b)).
surgery id_l ((f (f e (f e (f (f e m) m))) b)) ((f (f e (f (f e m) m)) b)).
surgery id_r ((f (f e (f (f e m) m)) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_133: forall b: G, ((e <+> e) <+> ((((e <+> (e <+> e)) <+> m) <+> (b <+> (e <+> m))) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f (f (f e (f e e)) m) (f b (f e m))) m))) ((f e (f (f (f (f e (f e e)) m) (f b (f e m))) m))).
surgery id_r ((f e (f (f (f (f e (f e e)) m) (f b (f e m))) m))) ((f e (f (f (f e (f e e)) (f b (f e m))) m))).
surgery id_l ((f e (f (f (f e (f e e)) (f b (f e m))) m))) ((f e (f (f (f e e) (f b (f e m))) m))).
surgery id_l ((f e (f (f (f e e) (f b (f e m))) m))) ((f e (f (f e (f b (f e m))) m))).
surgery id_l ((f e (f (f e (f b (f e m))) m))) ((f e (f (f e (f b m)) m))).
surgery id_r ((f e (f (f e (f b m)) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_134: forall b: G, (((e <+> (e <+> m)) <+> (e <+> b)) <+> (m <+> ((e <+> (e <+> m)) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f e b)) (f m (f (f e (f e m)) m)))) ((f (f (f e m) (f e b)) (f m (f (f e (f e m)) m)))).
surgery id_r ((f (f (f e m) (f e b)) (f m (f (f e (f e m)) m)))) ((f (f e (f e b)) (f m (f (f e (f e m)) m)))).
surgery id_l ((f (f e (f e b)) (f m (f (f e (f e m)) m)))) ((f (f e b) (f m (f (f e (f e m)) m)))).
surgery id_l ((f (f e b) (f m (f (f e (f e m)) m)))) ((f b (f m (f (f e (f e m)) m)))).
surgery id_l ((f b (f m (f (f e (f e m)) m)))) ((f b (f m (f (f e m) m)))).
surgery id_r ((f b (f m (f (f e m) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_135: forall b: G, (((b <+> m) <+> (e <+> (m <+> m))) <+> (((e <+> (e <+> e)) <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f e (f m m))) (f (f (f e (f e e)) m) m))) ((f (f b (f e (f m m))) (f (f (f e (f e e)) m) m))).
surgery id_l ((f (f b (f e (f m m))) (f (f (f e (f e e)) m) m))) ((f (f b (f m m)) (f (f (f e (f e e)) m) m))).
surgery id_r ((f (f b (f m m)) (f (f (f e (f e e)) m) m))) ((f (f b m) (f (f (f e (f e e)) m) m))).
surgery id_r ((f (f b m) (f (f (f e (f e e)) m) m))) ((f b (f (f (f e (f e e)) m) m))).
surgery id_r ((f b (f (f (f e (f e e)) m) m))) ((f b (f (f e (f e e)) m))).
surgery id_l ((f b (f (f e (f e e)) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_136: forall b: G, (((e <+> (e <+> m)) <+> ((e <+> m) <+> (e <+> m))) <+> (e <+> (e <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f (f e m) (f e m))) (f e (f e b)))) ((f (f (f e m) (f (f e m) (f e m))) (f e (f e b)))).
surgery id_r ((f (f (f e m) (f (f e m) (f e m))) (f e (f e b)))) ((f (f e (f (f e m) (f e m))) (f e (f e b)))).
surgery id_r ((f (f e (f (f e m) (f e m))) (f e (f e b)))) ((f (f e (f e (f e m))) (f e (f e b)))).
surgery id_l ((f (f e (f e (f e m))) (f e (f e b)))) ((f (f e (f e m)) (f e (f e b)))).
surgery id_l ((f (f e (f e m)) (f e (f e b)))) ((f (f e m) (f e (f e b)))).
surgery id_r ((f (f e m) (f e (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_137: forall b: G, ((e <+> e) <+> ((e <+> (e <+> e)) <+> ((b <+> (m <+> (e <+> m))) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f e (f e e)) (f (f b (f m (f e m))) m)))) ((f e (f (f e (f e e)) (f (f b (f m (f e m))) m)))).
surgery id_l ((f e (f (f e (f e e)) (f (f b (f m (f e m))) m)))) ((f e (f (f e e) (f (f b (f m (f e m))) m)))).
surgery id_l ((f e (f (f e e) (f (f b (f m (f e m))) m)))) ((f e (f e (f (f b (f m (f e m))) m)))).
surgery id_l ((f e (f e (f (f b (f m (f e m))) m)))) ((f e (f (f b (f m (f e m))) m))).
surgery id_l ((f e (f (f b (f m (f e m))) m))) ((f e (f (f b (f m m)) m))).
surgery id_r ((f e (f (f b (f m m)) m))) ((f e (f (f b m) m))).
surgery id_r ((f e (f (f b m) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_138: forall b: G, ((((e <+> m) <+> e) <+> (((e <+> e) <+> e) <+> b)) <+> ((e <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) e) (f (f (f e e) e) b)) (f (f e m) m))) ((f (f (f e e) (f (f (f e e) e) b)) (f (f e m) m))).
surgery id_l ((f (f (f e e) (f (f (f e e) e) b)) (f (f e m) m))) ((f (f e (f (f (f e e) e) b)) (f (f e m) m))).
surgery id_l ((f (f e (f (f (f e e) e) b)) (f (f e m) m))) ((f (f e (f (f e e) b)) (f (f e m) m))).
surgery id_l ((f (f e (f (f e e) b)) (f (f e m) m))) ((f (f e (f e b)) (f (f e m) m))).
surgery id_l ((f (f e (f e b)) (f (f e m) m))) ((f (f e b) (f (f e m) m))).
surgery id_l ((f (f e b) (f (f e m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_139: forall b: G, (((e <+> b) <+> (((e <+> m) <+> e) <+> m)) <+> (m <+> ((m <+> m) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e b) (f (f (f e m) e) m)) (f m (f (f m m) m)))) ((f (f b (f (f (f e m) e) m)) (f m (f (f m m) m)))).
surgery id_r ((f (f b (f (f (f e m) e) m)) (f m (f (f m m) m)))) ((f (f b (f (f e e) m)) (f m (f (f m m) m)))).
surgery id_l ((f (f b (f (f e e) m)) (f m (f (f m m) m)))) ((f (f b (f e m)) (f m (f (f m m) m)))).
surgery id_l ((f (f b (f e m)) (f m (f (f m m) m)))) ((f (f b m) (f m (f (f m m) m)))).
surgery id_r ((f (f b m) (f m (f (f m m) m)))) ((f b (f m (f (f m m) m)))).
surgery id_r ((f b (f m (f (f m m) m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_140: forall b: G, ((b <+> m) <+> (((e <+> e) <+> m) <+> ((e <+> ((e <+> m) <+> m)) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f (f e e) m) (f (f e (f (f e m) m)) m)))) ((f b (f (f (f e e) m) (f (f e (f (f e m) m)) m)))).
surgery id_r ((f b (f (f (f e e) m) (f (f e (f (f e m) m)) m)))) ((f b (f (f e e) (f (f e (f (f e m) m)) m)))).
surgery id_l ((f b (f (f e e) (f (f e (f (f e m) m)) m)))) ((f b (f e (f (f e (f (f e m) m)) m)))).
surgery id_l ((f b (f e (f (f e (f (f e m) m)) m)))) ((f b (f (f e (f (f e m) m)) m))).
surgery id_r ((f b (f (f e (f (f e m) m)) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_141: forall b: G, ((b <+> ((m <+> m) <+> (e <+> (e <+> m)))) <+> (m <+> ((e <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b (f (f m m) (f e (f e m)))) (f m (f (f e m) m)))) ((f (f b (f m (f e (f e m)))) (f m (f (f e m) m)))).
surgery id_l ((f (f b (f m (f e (f e m)))) (f m (f (f e m) m)))) ((f (f b (f m (f e m))) (f m (f (f e m) m)))).
surgery id_l ((f (f b (f m (f e m))) (f m (f (f e m) m)))) ((f (f b (f m m)) (f m (f (f e m) m)))).
surgery id_r ((f (f b (f m m)) (f m (f (f e m) m)))) ((f (f b m) (f m (f (f e m) m)))).
surgery id_r ((f (f b m) (f m (f (f e m) m)))) ((f b (f m (f (f e m) m)))).
surgery id_r ((f b (f m (f (f e m) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_142: forall b: G, (((e <+> m) <+> ((m <+> m) <+> (m <+> (e <+> m)))) <+> (b <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f (f m m) (f m (f e m)))) (f b (f e m)))) ((f (f e (f (f m m) (f m (f e m)))) (f b (f e m)))).
surgery id_r ((f (f e (f (f m m) (f m (f e m)))) (f b (f e m)))) ((f (f e (f m (f m (f e m)))) (f b (f e m)))).
surgery id_l ((f (f e (f m (f m (f e m)))) (f b (f e m)))) ((f (f e (f m (f m m))) (f b (f e m)))).
surgery id_r ((f (f e (f m (f m m))) (f b (f e m)))) ((f (f e (f m m)) (f b (f e m)))).
surgery id_r ((f (f e (f m m)) (f b (f e m)))) ((f (f e m) (f b (f e m)))).
surgery id_r ((f (f e m) (f b (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_143: forall b: G, ((e <+> e) <+> (((e <+> e) <+> ((e <+> e) <+> (e <+> m))) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f (f e e) (f (f e e) (f e m))) (f e b)))) ((f e (f (f (f e e) (f (f e e) (f e m))) (f e b)))).
surgery id_l ((f e (f (f (f e e) (f (f e e) (f e m))) (f e b)))) ((f e (f (f e (f (f e e) (f e m))) (f e b)))).
surgery id_l ((f e (f (f e (f (f e e) (f e m))) (f e b)))) ((f e (f (f e (f e (f e m))) (f e b)))).
surgery id_l ((f e (f (f e (f e (f e m))) (f e b)))) ((f e (f (f e (f e m)) (f e b)))).
surgery id_l ((f e (f (f e (f e m)) (f e b)))) ((f e (f (f e m) (f e b)))).
surgery id_r ((f e (f (f e m) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_144: forall b: G, (((e <+> e) <+> b) <+> (m <+> (e <+> ((e <+> (e <+> (e <+> m))) <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) b) (f m (f e (f (f e (f e (f e m))) m))))) ((f (f e b) (f m (f e (f (f e (f e (f e m))) m))))).
surgery id_l ((f (f e b) (f m (f e (f (f e (f e (f e m))) m))))) ((f b (f m (f e (f (f e (f e (f e m))) m))))).
surgery id_l ((f b (f m (f e (f (f e (f e (f e m))) m))))) ((f b (f m (f (f e (f e (f e m))) m)))).
surgery id_l ((f b (f m (f (f e (f e (f e m))) m)))) ((f b (f m (f (f e (f e m)) m)))).
surgery id_l ((f b (f m (f (f e (f e m)) m)))) ((f b (f m (f (f e m) m)))).
surgery id_r ((f b (f m (f (f e m) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_145: forall b: G, (((e <+> (e <+> m)) <+> m) <+> ((e <+> (b <+> m)) <+> ((e <+> e) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f e m)) m) (f (f e (f b m)) (f (f e e) m)))) ((f (f e (f e m)) (f (f e (f b m)) (f (f e e) m)))).
surgery id_l ((f (f e (f e m)) (f (f e (f b m)) (f (f e e) m)))) ((f (f e m) (f (f e (f b m)) (f (f e e) m)))).
surgery id_r ((f (f e m) (f (f e (f b m)) (f (f e e) m)))) ((f e (f (f e (f b m)) (f (f e e) m)))).
surgery id_r ((f e (f (f e (f b m)) (f (f e e) m)))) ((f e (f (f e b) (f (f e e) m)))).
surgery id_l ((f e (f (f e b) (f (f e e) m)))) ((f e (f b (f (f e e) m)))).
surgery id_l ((f e (f b (f (f e e) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_146: forall b: G, ((e <+> (e <+> m)) <+> ((e <+> m) <+> (((e <+> m) <+> m) <+> (b <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e m)) (f (f e m) (f (f (f e m) m) (f b m))))) ((f (f e m) (f (f e m) (f (f (f e m) m) (f b m))))).
surgery id_r ((f (f e m) (f (f e m) (f (f (f e m) m) (f b m))))) ((f e (f (f e m) (f (f (f e m) m) (f b m))))).
surgery id_r ((f e (f (f e m) (f (f (f e m) m) (f b m))))) ((f e (f e (f (f (f e m) m) (f b m))))).
surgery id_l ((f e (f e (f (f (f e m) m) (f b m))))) ((f e (f (f (f e m) m) (f b m)))).
surgery id_r ((f e (f (f (f e m) m) (f b m)))) ((f e (f (f e m) (f b m)))).
surgery id_r ((f e (f (f e m) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_147: forall b: G, ((((e <+> e) <+> (b <+> (e <+> (e <+> m)))) <+> m) <+> (m <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) (f b (f e (f e m)))) m) (f m (f m m)))) ((f (f (f e e) (f b (f e (f e m)))) (f m (f m m)))).
surgery id_l ((f (f (f e e) (f b (f e (f e m)))) (f m (f m m)))) ((f (f e (f b (f e (f e m)))) (f m (f m m)))).
surgery id_l ((f (f e (f b (f e (f e m)))) (f m (f m m)))) ((f (f e (f b (f e m))) (f m (f m m)))).
surgery id_l ((f (f e (f b (f e m))) (f m (f m m)))) ((f (f e (f b m)) (f m (f m m)))).
surgery id_r ((f (f e (f b m)) (f m (f m m)))) ((f (f e b) (f m (f m m)))).
surgery id_l ((f (f e b) (f m (f m m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_148: forall b: G, ((((((e <+> m) <+> (e <+> e)) <+> e) <+> (b <+> m)) <+> (m <+> m)) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f (f e m) (f e e)) e) (f b m)) (f m m)) m)) ((f (f (f (f (f e m) (f e e)) e) (f b m)) (f m m))).
surgery id_r ((f (f (f (f (f e m) (f e e)) e) (f b m)) (f m m))) ((f (f (f (f e (f e e)) e) (f b m)) (f m m))).
surgery id_l ((f (f (f (f e (f e e)) e) (f b m)) (f m m))) ((f (f (f (f e e) e) (f b m)) (f m m))).
surgery id_l ((f (f (f (f e e) e) (f b m)) (f m m))) ((f (f (f e e) (f b m)) (f m m))).
surgery id_l ((f (f (f e e) (f b m)) (f m m))) ((f (f e (f b m)) (f m m))).
surgery id_r ((f (f e (f b m)) (f m m))) ((f (f e b) (f m m))).
surgery id_l ((f (f e b) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_149: forall b: G, (((e <+> m) <+> b) <+> ((m <+> m) <+> (e <+> ((e <+> m) <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) b) (f (f m m) (f e (f (f e m) (f e m)))))) ((f (f e b) (f (f m m) (f e (f (f e m) (f e m)))))).
surgery id_l ((f (f e b) (f (f m m) (f e (f (f e m) (f e m)))))) ((f b (f (f m m) (f e (f (f e m) (f e m)))))).
surgery id_r ((f b (f (f m m) (f e (f (f e m) (f e m)))))) ((f b (f m (f e (f (f e m) (f e m)))))).
surgery id_l ((f b (f m (f e (f (f e m) (f e m)))))) ((f b (f m (f (f e m) (f e m))))).
surgery id_r ((f b (f m (f (f e m) (f e m))))) ((f b (f m (f e (f e m))))).
surgery id_l ((f b (f m (f e (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_150: forall b: G, (e <+> ((e <+> ((e <+> m) <+> (b <+> (m <+> (m <+> m))))) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f e (f (f e (f (f e m) (f b (f m (f m m))))) (f e m)))) ((f e (f (f e (f e (f b (f m (f m m))))) (f e m)))).
surgery id_l ((f e (f (f e (f e (f b (f m (f m m))))) (f e m)))) ((f e (f (f e (f b (f m (f m m)))) (f e m)))).
surgery id_r ((f e (f (f e (f b (f m (f m m)))) (f e m)))) ((f e (f (f e (f b (f m m))) (f e m)))).
surgery id_r ((f e (f (f e (f b (f m m))) (f e m)))) ((f e (f (f e (f b m)) (f e m)))).
surgery id_r ((f e (f (f e (f b m)) (f e m)))) ((f e (f (f e b) (f e m)))).
surgery id_l ((f e (f (f e b) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_151: forall b: G, ((b <+> m) <+> (((m <+> m) <+> ((e <+> e) <+> (m <+> (e <+> m)))) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f (f m m) (f (f e e) (f m (f e m)))) m))) ((f b (f (f (f m m) (f (f e e) (f m (f e m)))) m))).
surgery id_r ((f b (f (f (f m m) (f (f e e) (f m (f e m)))) m))) ((f b (f (f m (f (f e e) (f m (f e m)))) m))).
surgery id_l ((f b (f (f m (f (f e e) (f m (f e m)))) m))) ((f b (f (f m (f e (f m (f e m)))) m))).
surgery id_l ((f b (f (f m (f e (f m (f e m)))) m))) ((f b (f (f m (f m (f e m))) m))).
surgery id_l ((f b (f (f m (f m (f e m))) m))) ((f b (f (f m (f m m)) m))).
surgery id_r ((f b (f (f m (f m m)) m))) ((f b (f (f m m) m))).
surgery id_r ((f b (f (f m m) m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_152: forall b: G, (((e <+> e) <+> (((e <+> e) <+> m) <+> m)) <+> ((e <+> m) <+> (b <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f (f e e) m) m)) (f (f e m) (f b m)))) ((f (f e (f (f (f e e) m) m)) (f (f e m) (f b m)))).
surgery id_r ((f (f e (f (f (f e e) m) m)) (f (f e m) (f b m)))) ((f (f e (f (f e e) m)) (f (f e m) (f b m)))).
surgery id_l ((f (f e (f (f e e) m)) (f (f e m) (f b m)))) ((f (f e (f e m)) (f (f e m) (f b m)))).
surgery id_l ((f (f e (f e m)) (f (f e m) (f b m)))) ((f (f e m) (f (f e m) (f b m)))).
surgery id_r ((f (f e m) (f (f e m) (f b m)))) ((f e (f (f e m) (f b m)))).
surgery id_r ((f e (f (f e m) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_153: forall b: G, (b <+> ((e <+> (m <+> (((e <+> e) <+> (m <+> m)) <+> (m <+> m)))) <+> m)) = b.
Proof.
intros.
surgery id_l ((f b (f (f e (f m (f (f (f e e) (f m m)) (f m m)))) m))) ((f b (f (f e (f m (f (f e (f m m)) (f m m)))) m))).
surgery id_r ((f b (f (f e (f m (f (f e (f m m)) (f m m)))) m))) ((f b (f (f e (f m (f (f e m) (f m m)))) m))).
surgery id_r ((f b (f (f e (f m (f (f e m) (f m m)))) m))) ((f b (f (f e (f m (f e (f m m)))) m))).
surgery id_l ((f b (f (f e (f m (f e (f m m)))) m))) ((f b (f (f e (f m (f m m))) m))).
surgery id_r ((f b (f (f e (f m (f m m))) m))) ((f b (f (f e (f m m)) m))).
surgery id_r ((f b (f (f e (f m m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_154: forall b: G, (((b <+> m) <+> (m <+> m)) <+> (((e <+> m) <+> m) <+> (m <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f m m)) (f (f (f e m) m) (f m (f m m))))) ((f (f b (f m m)) (f (f (f e m) m) (f m (f m m))))).
surgery id_r ((f (f b (f m m)) (f (f (f e m) m) (f m (f m m))))) ((f (f b m) (f (f (f e m) m) (f m (f m m))))).
surgery id_r ((f (f b m) (f (f (f e m) m) (f m (f m m))))) ((f b (f (f (f e m) m) (f m (f m m))))).
surgery id_r ((f b (f (f (f e m) m) (f m (f m m))))) ((f b (f (f e m) (f m (f m m))))).
surgery id_r ((f b (f (f e m) (f m (f m m))))) ((f b (f e (f m (f m m))))).
surgery id_l ((f b (f e (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_155: forall b: G, ((((e <+> e) <+> m) <+> b) <+> (e <+> ((m <+> m) <+> (e <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) b) (f e (f (f m m) (f e (f m m)))))) ((f (f (f e e) b) (f e (f (f m m) (f e (f m m)))))).
surgery id_l ((f (f (f e e) b) (f e (f (f m m) (f e (f m m)))))) ((f (f e b) (f e (f (f m m) (f e (f m m)))))).
surgery id_l ((f (f e b) (f e (f (f m m) (f e (f m m)))))) ((f b (f e (f (f m m) (f e (f m m)))))).
surgery id_l ((f b (f e (f (f m m) (f e (f m m)))))) ((f b (f (f m m) (f e (f m m))))).
surgery id_r ((f b (f (f m m) (f e (f m m))))) ((f b (f m (f e (f m m))))).
surgery id_l ((f b (f m (f e (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_156: forall b: G, ((e <+> (m <+> (((e <+> m) <+> m) <+> m))) <+> (b <+> ((e <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f m (f (f (f e m) m) m))) (f b (f (f e m) m)))) ((f (f e (f m (f (f e m) m))) (f b (f (f e m) m)))).
surgery id_r ((f (f e (f m (f (f e m) m))) (f b (f (f e m) m)))) ((f (f e (f m (f e m))) (f b (f (f e m) m)))).
surgery id_l ((f (f e (f m (f e m))) (f b (f (f e m) m)))) ((f (f e (f m m)) (f b (f (f e m) m)))).
surgery id_r ((f (f e (f m m)) (f b (f (f e m) m)))) ((f (f e m) (f b (f (f e m) m)))).
surgery id_r ((f (f e m) (f b (f (f e m) m)))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_157: forall b: G, ((e <+> m) <+> ((e <+> (((e <+> m) <+> b) <+> (m <+> m))) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f e (f (f (f e m) b) (f m m))) (f m m)))) ((f e (f (f e (f (f (f e m) b) (f m m))) (f m m)))).
surgery id_r ((f e (f (f e (f (f (f e m) b) (f m m))) (f m m)))) ((f e (f (f e (f (f e b) (f m m))) (f m m)))).
surgery id_l ((f e (f (f e (f (f e b) (f m m))) (f m m)))) ((f e (f (f e (f b (f m m))) (f m m)))).
surgery id_r ((f e (f (f e (f b (f m m))) (f m m)))) ((f e (f (f e (f b m)) (f m m)))).
surgery id_r ((f e (f (f e (f b m)) (f m m)))) ((f e (f (f e b) (f m m)))).
surgery id_l ((f e (f (f e b) (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_158: forall b: G, (((b <+> m) <+> (((e <+> e) <+> ((m <+> m) <+> m)) <+> m)) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f (f (f e e) (f (f m m) m)) m)) (f m m))) ((f (f b (f (f (f e e) (f (f m m) m)) m)) (f m m))).
surgery id_l ((f (f b (f (f (f e e) (f (f m m) m)) m)) (f m m))) ((f (f b (f (f e (f (f m m) m)) m)) (f m m))).
surgery id_r ((f (f b (f (f e (f (f m m) m)) m)) (f m m))) ((f (f b (f (f e (f m m)) m)) (f m m))).
surgery id_r ((f (f b (f (f e (f m m)) m)) (f m m))) ((f (f b (f (f e m) m)) (f m m))).
surgery id_r ((f (f b (f (f e m) m)) (f m m))) ((f (f b (f e m)) (f m m))).
surgery id_l ((f (f b (f e m)) (f m m))) ((f (f b m) (f m m))).
surgery id_r ((f (f b m) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_159: forall b: G, (((((e <+> m) <+> e) <+> e) <+> (e <+> ((e <+> e) <+> m))) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e m) e) e) (f e (f (f e e) m))) (f b m))) ((f (f (f (f e e) e) (f e (f (f e e) m))) (f b m))).
surgery id_l ((f (f (f (f e e) e) (f e (f (f e e) m))) (f b m))) ((f (f (f e e) (f e (f (f e e) m))) (f b m))).
surgery id_l ((f (f (f e e) (f e (f (f e e) m))) (f b m))) ((f (f e (f e (f (f e e) m))) (f b m))).
surgery id_l ((f (f e (f e (f (f e e) m))) (f b m))) ((f (f e (f (f e e) m)) (f b m))).
surgery id_l ((f (f e (f (f e e) m)) (f b m))) ((f (f e (f e m)) (f b m))).
surgery id_l ((f (f e (f e m)) (f b m))) ((f (f e m) (f b m))).
surgery id_r ((f (f e m) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_160: forall b: G, (((b <+> m) <+> ((e <+> m) <+> ((e <+> e) <+> m))) <+> (e <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f (f e m) (f (f e e) m))) (f e (f m m)))) ((f (f b (f (f e m) (f (f e e) m))) (f e (f m m)))).
surgery id_r ((f (f b (f (f e m) (f (f e e) m))) (f e (f m m)))) ((f (f b (f e (f (f e e) m))) (f e (f m m)))).
surgery id_l ((f (f b (f e (f (f e e) m))) (f e (f m m)))) ((f (f b (f (f e e) m)) (f e (f m m)))).
surgery id_l ((f (f b (f (f e e) m)) (f e (f m m)))) ((f (f b (f e m)) (f e (f m m)))).
surgery id_l ((f (f b (f e m)) (f e (f m m)))) ((f (f b m) (f e (f m m)))).
surgery id_r ((f (f b m) (f e (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_161: forall b: G, ((e <+> (e <+> ((e <+> m) <+> m))) <+> ((e <+> m) <+> ((e <+> b) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e (f (f e m) m))) (f (f e m) (f (f e b) m)))) ((f (f e (f (f e m) m)) (f (f e m) (f (f e b) m)))).
surgery id_r ((f (f e (f (f e m) m)) (f (f e m) (f (f e b) m)))) ((f (f e (f e m)) (f (f e m) (f (f e b) m)))).
surgery id_l ((f (f e (f e m)) (f (f e m) (f (f e b) m)))) ((f (f e m) (f (f e m) (f (f e b) m)))).
surgery id_r ((f (f e m) (f (f e m) (f (f e b) m)))) ((f e (f (f e m) (f (f e b) m)))).
surgery id_r ((f e (f (f e m) (f (f e b) m)))) ((f e (f e (f (f e b) m)))).
surgery id_l ((f e (f e (f (f e b) m)))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_162: forall b: G, ((((e <+> e) <+> e) <+> (e <+> e)) <+> ((e <+> m) <+> ((e <+> e) <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) e) (f e e)) (f (f e m) (f (f e e) b)))) ((f (f (f e e) (f e e)) (f (f e m) (f (f e e) b)))).
surgery id_l ((f (f (f e e) (f e e)) (f (f e m) (f (f e e) b)))) ((f (f e (f e e)) (f (f e m) (f (f e e) b)))).
surgery id_l ((f (f e (f e e)) (f (f e m) (f (f e e) b)))) ((f (f e e) (f (f e m) (f (f e e) b)))).
surgery id_l ((f (f e e) (f (f e m) (f (f e e) b)))) ((f e (f (f e m) (f (f e e) b)))).
surgery id_r ((f e (f (f e m) (f (f e e) b)))) ((f e (f e (f (f e e) b)))).
surgery id_l ((f e (f e (f (f e e) b)))) ((f e (f (f e e) b))).
surgery id_l ((f e (f (f e e) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_163: forall b: G, ((e <+> (e <+> ((e <+> e) <+> (((e <+> m) <+> m) <+> m)))) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f e (f e (f (f e e) (f (f (f e m) m) m)))) (f b m))) ((f (f e (f (f e e) (f (f (f e m) m) m))) (f b m))).
surgery id_l ((f (f e (f (f e e) (f (f (f e m) m) m))) (f b m))) ((f (f e (f e (f (f (f e m) m) m))) (f b m))).
surgery id_l ((f (f e (f e (f (f (f e m) m) m))) (f b m))) ((f (f e (f (f (f e m) m) m)) (f b m))).
surgery id_r ((f (f e (f (f (f e m) m) m)) (f b m))) ((f (f e (f (f e m) m)) (f b m))).
surgery id_r ((f (f e (f (f e m) m)) (f b m))) ((f (f e (f e m)) (f b m))).
surgery id_l ((f (f e (f e m)) (f b m))) ((f (f e m) (f b m))).
surgery id_r ((f (f e m) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_164: forall b: G, ((b <+> m) <+> ((((e <+> m) <+> (e <+> m)) <+> m) <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f (f (f e m) (f e m)) m) (f e (f e m))))) ((f b (f (f (f (f e m) (f e m)) m) (f e (f e m))))).
surgery id_r ((f b (f (f (f (f e m) (f e m)) m) (f e (f e m))))) ((f b (f (f (f e m) (f e m)) (f e (f e m))))).
surgery id_r ((f b (f (f (f e m) (f e m)) (f e (f e m))))) ((f b (f (f e (f e m)) (f e (f e m))))).
surgery id_l ((f b (f (f e (f e m)) (f e (f e m))))) ((f b (f (f e m) (f e (f e m))))).
surgery id_r ((f b (f (f e m) (f e (f e m))))) ((f b (f e (f e (f e m))))).
surgery id_l ((f b (f e (f e (f e m))))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_165: forall b: G, (((e <+> (e <+> m)) <+> (e <+> ((e <+> m) <+> m))) <+> (e <+> (e <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f e (f (f e m) m))) (f e (f e b)))) ((f (f (f e m) (f e (f (f e m) m))) (f e (f e b)))).
surgery id_r ((f (f (f e m) (f e (f (f e m) m))) (f e (f e b)))) ((f (f e (f e (f (f e m) m))) (f e (f e b)))).
surgery id_l ((f (f e (f e (f (f e m) m))) (f e (f e b)))) ((f (f e (f (f e m) m)) (f e (f e b)))).
surgery id_r ((f (f e (f (f e m) m)) (f e (f e b)))) ((f (f e (f e m)) (f e (f e b)))).
surgery id_l ((f (f e (f e m)) (f e (f e b)))) ((f (f e m) (f e (f e b)))).
surgery id_r ((f (f e m) (f e (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_166: forall b: G, ((e <+> b) <+> (((e <+> m) <+> m) <+> (m <+> ((e <+> m) <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f (f (f e m) m) (f m (f (f e m) (f m m)))))) ((f b (f (f (f e m) m) (f m (f (f e m) (f m m)))))).
surgery id_r ((f b (f (f (f e m) m) (f m (f (f e m) (f m m)))))) ((f b (f (f e m) (f m (f (f e m) (f m m)))))).
surgery id_r ((f b (f (f e m) (f m (f (f e m) (f m m)))))) ((f b (f e (f m (f (f e m) (f m m)))))).
surgery id_l ((f b (f e (f m (f (f e m) (f m m)))))) ((f b (f m (f (f e m) (f m m))))).
surgery id_r ((f b (f m (f (f e m) (f m m))))) ((f b (f m (f e (f m m))))).
surgery id_l ((f b (f m (f e (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_167: forall b: G, (b <+> (((e <+> m) <+> (m <+> (e <+> m))) <+> ((e <+> (e <+> e)) <+> m))) = b.
Proof.
intros.
surgery id_r ((f b (f (f (f e m) (f m (f e m))) (f (f e (f e e)) m)))) ((f b (f (f e (f m (f e m))) (f (f e (f e e)) m)))).
surgery id_l ((f b (f (f e (f m (f e m))) (f (f e (f e e)) m)))) ((f b (f (f e (f m m)) (f (f e (f e e)) m)))).
surgery id_r ((f b (f (f e (f m m)) (f (f e (f e e)) m)))) ((f b (f (f e m) (f (f e (f e e)) m)))).
surgery id_r ((f b (f (f e m) (f (f e (f e e)) m)))) ((f b (f e (f (f e (f e e)) m)))).
surgery id_l ((f b (f e (f (f e (f e e)) m)))) ((f b (f (f e (f e e)) m))).
surgery id_l ((f b (f (f e (f e e)) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_168: forall b: G, ((e <+> e) <+> ((b <+> m) <+> (m <+> ((e <+> (e <+> (m <+> m))) <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f b m) (f m (f (f e (f e (f m m))) m))))) ((f e (f (f b m) (f m (f (f e (f e (f m m))) m))))).
surgery id_r ((f e (f (f b m) (f m (f (f e (f e (f m m))) m))))) ((f e (f b (f m (f (f e (f e (f m m))) m))))).
surgery id_l ((f e (f b (f m (f (f e (f e (f m m))) m))))) ((f e (f b (f m (f (f e (f m m)) m))))).
surgery id_r ((f e (f b (f m (f (f e (f m m)) m))))) ((f e (f b (f m (f (f e m) m))))).
surgery id_r ((f e (f b (f m (f (f e m) m))))) ((f e (f b (f m (f e m))))).
surgery id_l ((f e (f b (f m (f e m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_169: forall b: G, ((e <+> m) <+> (((e <+> (e <+> (b <+> m))) <+> m) <+> (m <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f (f e (f e (f b m))) m) (f m (f m m))))) ((f e (f (f (f e (f e (f b m))) m) (f m (f m m))))).
surgery id_r ((f e (f (f (f e (f e (f b m))) m) (f m (f m m))))) ((f e (f (f e (f e (f b m))) (f m (f m m))))).
surgery id_l ((f e (f (f e (f e (f b m))) (f m (f m m))))) ((f e (f (f e (f b m)) (f m (f m m))))).
surgery id_r ((f e (f (f e (f b m)) (f m (f m m))))) ((f e (f (f e b) (f m (f m m))))).
surgery id_l ((f e (f (f e b) (f m (f m m))))) ((f e (f b (f m (f m m))))).
surgery id_r ((f e (f b (f m (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_170: forall b: G, (((e <+> e) <+> e) <+> (((e <+> (e <+> m)) <+> b) <+> ((e <+> m) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) e) (f (f (f e (f e m)) b) (f (f e m) m)))) ((f (f e e) (f (f (f e (f e m)) b) (f (f e m) m)))).
surgery id_l ((f (f e e) (f (f (f e (f e m)) b) (f (f e m) m)))) ((f e (f (f (f e (f e m)) b) (f (f e m) m)))).
surgery id_l ((f e (f (f (f e (f e m)) b) (f (f e m) m)))) ((f e (f (f (f e m) b) (f (f e m) m)))).
surgery id_r ((f e (f (f (f e m) b) (f (f e m) m)))) ((f e (f (f e b) (f (f e m) m)))).
surgery id_l ((f e (f (f e b) (f (f e m) m)))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_171: forall b: G, ((((b <+> m) <+> m) <+> (m <+> ((m <+> m) <+> m))) <+> (m <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f b m) m) (f m (f (f m m) m))) (f m (f m m)))) ((f (f (f b m) (f m (f (f m m) m))) (f m (f m m)))).
surgery id_r ((f (f (f b m) (f m (f (f m m) m))) (f m (f m m)))) ((f (f b (f m (f (f m m) m))) (f m (f m m)))).
surgery id_r ((f (f b (f m (f (f m m) m))) (f m (f m m)))) ((f (f b (f m (f m m))) (f m (f m m)))).
surgery id_r ((f (f b (f m (f m m))) (f m (f m m)))) ((f (f b (f m m)) (f m (f m m)))).
surgery id_r ((f (f b (f m m)) (f m (f m m)))) ((f (f b m) (f m (f m m)))).
surgery id_r ((f (f b m) (f m (f m m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_172: forall b: G, ((e <+> (((e <+> m) <+> m) <+> m)) <+> (e <+> (((e <+> e) <+> b) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f (f e m) m) m)) (f e (f (f (f e e) b) m)))) ((f (f e (f (f e m) m)) (f e (f (f (f e e) b) m)))).
surgery id_r ((f (f e (f (f e m) m)) (f e (f (f (f e e) b) m)))) ((f (f e (f e m)) (f e (f (f (f e e) b) m)))).
surgery id_l ((f (f e (f e m)) (f e (f (f (f e e) b) m)))) ((f (f e m) (f e (f (f (f e e) b) m)))).
surgery id_r ((f (f e m) (f e (f (f (f e e) b) m)))) ((f e (f e (f (f (f e e) b) m)))).
surgery id_l ((f e (f e (f (f (f e e) b) m)))) ((f e (f (f (f e e) b) m))).
surgery id_l ((f e (f (f (f e e) b) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_173: forall b: G, (b <+> (((e <+> e) <+> (e <+> m)) <+> ((m <+> m) <+> (m <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_l ((f b (f (f (f e e) (f e m)) (f (f m m) (f m (f m m)))))) ((f b (f (f e (f e m)) (f (f m m) (f m (f m m)))))).
surgery id_l ((f b (f (f e (f e m)) (f (f m m) (f m (f m m)))))) ((f b (f (f e m) (f (f m m) (f m (f m m)))))).
surgery id_r ((f b (f (f e m) (f (f m m) (f m (f m m)))))) ((f b (f e (f (f m m) (f m (f m m)))))).
surgery id_l ((f b (f e (f (f m m) (f m (f m m)))))) ((f b (f (f m m) (f m (f m m))))).
surgery id_r ((f b (f (f m m) (f m (f m m))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_174: forall b: G, ((e <+> ((e <+> m) <+> m)) <+> (e <+> ((b <+> m) <+> (e <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f e m) m)) (f e (f (f b m) (f e (f m m)))))) ((f (f e (f e m)) (f e (f (f b m) (f e (f m m)))))).
surgery id_l ((f (f e (f e m)) (f e (f (f b m) (f e (f m m)))))) ((f (f e m) (f e (f (f b m) (f e (f m m)))))).
surgery id_r ((f (f e m) (f e (f (f b m) (f e (f m m)))))) ((f e (f e (f (f b m) (f e (f m m)))))).
surgery id_l ((f e (f e (f (f b m) (f e (f m m)))))) ((f e (f (f b m) (f e (f m m))))).
surgery id_r ((f e (f (f b m) (f e (f m m))))) ((f e (f b (f e (f m m))))).
surgery id_l ((f e (f b (f e (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_175: forall b: G, ((e <+> e) <+> (((e <+> e) <+> (m <+> ((m <+> m) <+> (m <+> m)))) <+> b)) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f (f e e) (f m (f (f m m) (f m m)))) b))) ((f e (f (f (f e e) (f m (f (f m m) (f m m)))) b))).
surgery id_l ((f e (f (f (f e e) (f m (f (f m m) (f m m)))) b))) ((f e (f (f e (f m (f (f m m) (f m m)))) b))).
surgery id_r ((f e (f (f e (f m (f (f m m) (f m m)))) b))) ((f e (f (f e (f m (f m (f m m)))) b))).
surgery id_r ((f e (f (f e (f m (f m (f m m)))) b))) ((f e (f (f e (f m (f m m))) b))).
surgery id_r ((f e (f (f e (f m (f m m))) b))) ((f e (f (f e (f m m)) b))).
surgery id_r ((f e (f (f e (f m m)) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_176: forall b: G, ((((e <+> m) <+> (e <+> m)) <+> m) <+> (((e <+> b) <+> m) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f e m)) m) (f (f (f e b) m) (f e m)))) ((f (f (f e m) (f e m)) (f (f (f e b) m) (f e m)))).
surgery id_r ((f (f (f e m) (f e m)) (f (f (f e b) m) (f e m)))) ((f (f e (f e m)) (f (f (f e b) m) (f e m)))).
surgery id_l ((f (f e (f e m)) (f (f (f e b) m) (f e m)))) ((f (f e m) (f (f (f e b) m) (f e m)))).
surgery id_r ((f (f e m) (f (f (f e b) m) (f e m)))) ((f e (f (f (f e b) m) (f e m)))).
surgery id_r ((f e (f (f (f e b) m) (f e m)))) ((f e (f (f e b) (f e m)))).
surgery id_l ((f e (f (f e b) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_177: forall b: G, (((e <+> m) <+> (b <+> m)) <+> ((e <+> (e <+> m)) <+> (e <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f b m)) (f (f e (f e m)) (f e (f m m))))) ((f (f e (f b m)) (f (f e (f e m)) (f e (f m m))))).
surgery id_r ((f (f e (f b m)) (f (f e (f e m)) (f e (f m m))))) ((f (f e b) (f (f e (f e m)) (f e (f m m))))).
surgery id_l ((f (f e b) (f (f e (f e m)) (f e (f m m))))) ((f b (f (f e (f e m)) (f e (f m m))))).
surgery id_l ((f b (f (f e (f e m)) (f e (f m m))))) ((f b (f (f e m) (f e (f m m))))).
surgery id_r ((f b (f (f e m) (f e (f m m))))) ((f b (f e (f e (f m m))))).
surgery id_l ((f b (f e (f e (f m m))))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_178: forall b: G, (((b <+> m) <+> (((e <+> m) <+> (e <+> e)) <+> (m <+> m))) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f (f (f e m) (f e e)) (f m m))) (f m m))) ((f (f b (f (f (f e m) (f e e)) (f m m))) (f m m))).
surgery id_r ((f (f b (f (f (f e m) (f e e)) (f m m))) (f m m))) ((f (f b (f (f e (f e e)) (f m m))) (f m m))).
surgery id_l ((f (f b (f (f e (f e e)) (f m m))) (f m m))) ((f (f b (f (f e e) (f m m))) (f m m))).
surgery id_l ((f (f b (f (f e e) (f m m))) (f m m))) ((f (f b (f e (f m m))) (f m m))).
surgery id_l ((f (f b (f e (f m m))) (f m m))) ((f (f b (f m m)) (f m m))).
surgery id_r ((f (f b (f m m)) (f m m))) ((f (f b m) (f m m))).
surgery id_r ((f (f b m) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_179: forall b: G, ((((e <+> m) <+> (e <+> m)) <+> ((e <+> e) <+> ((e <+> e) <+> m))) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f e m)) (f (f e e) (f (f e e) m))) b)) ((f (f (f e (f e m)) (f (f e e) (f (f e e) m))) b)).
surgery id_l ((f (f (f e (f e m)) (f (f e e) (f (f e e) m))) b)) ((f (f (f e m) (f (f e e) (f (f e e) m))) b)).
surgery id_r ((f (f (f e m) (f (f e e) (f (f e e) m))) b)) ((f (f e (f (f e e) (f (f e e) m))) b)).
surgery id_l ((f (f e (f (f e e) (f (f e e) m))) b)) ((f (f e (f e (f (f e e) m))) b)).
surgery id_l ((f (f e (f e (f (f e e) m))) b)) ((f (f e (f (f e e) m)) b)).
surgery id_l ((f (f e (f (f e e) m)) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_180: forall b: G, (((e <+> e) <+> b) <+> ((m <+> ((e <+> (e <+> m)) <+> m)) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) b) (f (f m (f (f e (f e m)) m)) (f m m)))) ((f (f e b) (f (f m (f (f e (f e m)) m)) (f m m)))).
surgery id_l ((f (f e b) (f (f m (f (f e (f e m)) m)) (f m m)))) ((f b (f (f m (f (f e (f e m)) m)) (f m m)))).
surgery id_l ((f b (f (f m (f (f e (f e m)) m)) (f m m)))) ((f b (f (f m (f (f e m) m)) (f m m)))).
surgery id_r ((f b (f (f m (f (f e m) m)) (f m m)))) ((f b (f (f m (f e m)) (f m m)))).
surgery id_l ((f b (f (f m (f e m)) (f m m)))) ((f b (f (f m m) (f m m)))).
surgery id_r ((f b (f (f m m) (f m m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_181: forall b: G, ((((e <+> e) <+> (e <+> (e <+> m))) <+> (e <+> m)) <+> (e <+> (e <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) (f e (f e m))) (f e m)) (f e (f e b)))) ((f (f (f e (f e (f e m))) (f e m)) (f e (f e b)))).
surgery id_l ((f (f (f e (f e (f e m))) (f e m)) (f e (f e b)))) ((f (f (f e (f e m)) (f e m)) (f e (f e b)))).
surgery id_l ((f (f (f e (f e m)) (f e m)) (f e (f e b)))) ((f (f (f e m) (f e m)) (f e (f e b)))).
surgery id_r ((f (f (f e m) (f e m)) (f e (f e b)))) ((f (f e (f e m)) (f e (f e b)))).
surgery id_l ((f (f e (f e m)) (f e (f e b)))) ((f (f e m) (f e (f e b)))).
surgery id_r ((f (f e m) (f e (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_182: forall b: G, ((((e <+> e) <+> ((e <+> m) <+> (e <+> m))) <+> (e <+> b)) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) (f (f e m) (f e m))) (f e b)) (f m m))) ((f (f (f e (f (f e m) (f e m))) (f e b)) (f m m))).
surgery id_r ((f (f (f e (f (f e m) (f e m))) (f e b)) (f m m))) ((f (f (f e (f e (f e m))) (f e b)) (f m m))).
surgery id_l ((f (f (f e (f e (f e m))) (f e b)) (f m m))) ((f (f (f e (f e m)) (f e b)) (f m m))).
surgery id_l ((f (f (f e (f e m)) (f e b)) (f m m))) ((f (f (f e m) (f e b)) (f m m))).
surgery id_r ((f (f (f e m) (f e b)) (f m m))) ((f (f e (f e b)) (f m m))).
surgery id_l ((f (f e (f e b)) (f m m))) ((f (f e b) (f m m))).
surgery id_l ((f (f e b) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_183: forall b: G, ((((e <+> m) <+> ((e <+> b) <+> m)) <+> ((e <+> m) <+> m)) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f (f e b) m)) (f (f e m) m)) (f m m))) ((f (f (f e (f (f e b) m)) (f (f e m) m)) (f m m))).
surgery id_l ((f (f (f e (f (f e b) m)) (f (f e m) m)) (f m m))) ((f (f (f e (f b m)) (f (f e m) m)) (f m m))).
surgery id_r ((f (f (f e (f b m)) (f (f e m) m)) (f m m))) ((f (f (f e b) (f (f e m) m)) (f m m))).
surgery id_l ((f (f (f e b) (f (f e m) m)) (f m m))) ((f (f b (f (f e m) m)) (f m m))).
surgery id_r ((f (f b (f (f e m) m)) (f m m))) ((f (f b (f e m)) (f m m))).
surgery id_l ((f (f b (f e m)) (f m m))) ((f (f b m) (f m m))).
surgery id_r ((f (f b m) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_184: forall b: G, (((e <+> (e <+> m)) <+> e) <+> ((e <+> (e <+> (e <+> m))) <+> (b <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) e) (f (f e (f e (f e m))) (f b m)))) ((f (f (f e m) e) (f (f e (f e (f e m))) (f b m)))).
surgery id_r ((f (f (f e m) e) (f (f e (f e (f e m))) (f b m)))) ((f (f e e) (f (f e (f e (f e m))) (f b m)))).
surgery id_l ((f (f e e) (f (f e (f e (f e m))) (f b m)))) ((f e (f (f e (f e (f e m))) (f b m)))).
surgery id_l ((f e (f (f e (f e (f e m))) (f b m)))) ((f e (f (f e (f e m)) (f b m)))).
surgery id_l ((f e (f (f e (f e m)) (f b m)))) ((f e (f (f e m) (f b m)))).
surgery id_r ((f e (f (f e m) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_185: forall b: G, ((((e <+> (e <+> m)) <+> (e <+> ((e <+> m) <+> m))) <+> m) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e (f e m)) (f e (f (f e m) m))) m) (f e b))) ((f (f (f e (f e m)) (f e (f (f e m) m))) (f e b))).
surgery id_l ((f (f (f e (f e m)) (f e (f (f e m) m))) (f e b))) ((f (f (f e m) (f e (f (f e m) m))) (f e b))).
surgery id_r ((f (f (f e m) (f e (f (f e m) m))) (f e b))) ((f (f e (f e (f (f e m) m))) (f e b))).
surgery id_l ((f (f e (f e (f (f e m) m))) (f e b))) ((f (f e (f (f e m) m)) (f e b))).
surgery id_r ((f (f e (f (f e m) m)) (f e b))) ((f (f e (f e m)) (f e b))).
surgery id_l ((f (f e (f e m)) (f e b))) ((f (f e m) (f e b))).
surgery id_r ((f (f e m) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_186: forall b: G, (((e <+> m) <+> b) <+> (((m <+> m) <+> m) <+> ((m <+> m) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) b) (f (f (f m m) m) (f (f m m) (f m m))))) ((f (f e b) (f (f (f m m) m) (f (f m m) (f m m))))).
surgery id_l ((f (f e b) (f (f (f m m) m) (f (f m m) (f m m))))) ((f b (f (f (f m m) m) (f (f m m) (f m m))))).
surgery id_r ((f b (f (f (f m m) m) (f (f m m) (f m m))))) ((f b (f (f m m) (f (f m m) (f m m))))).
surgery id_r ((f b (f (f m m) (f (f m m) (f m m))))) ((f b (f m (f (f m m) (f m m))))).
surgery id_r ((f b (f m (f (f m m) (f m m))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_187: forall b: G, ((e <+> (e <+> m)) <+> (((e <+> m) <+> b) <+> ((e <+> m) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e m)) (f (f (f e m) b) (f (f e m) (f e m))))) ((f (f e m) (f (f (f e m) b) (f (f e m) (f e m))))).
surgery id_r ((f (f e m) (f (f (f e m) b) (f (f e m) (f e m))))) ((f e (f (f (f e m) b) (f (f e m) (f e m))))).
surgery id_r ((f e (f (f (f e m) b) (f (f e m) (f e m))))) ((f e (f (f e b) (f (f e m) (f e m))))).
surgery id_l ((f e (f (f e b) (f (f e m) (f e m))))) ((f e (f b (f (f e m) (f e m))))).
surgery id_r ((f e (f b (f (f e m) (f e m))))) ((f e (f b (f e (f e m))))).
surgery id_l ((f e (f b (f e (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_188: forall b: G, ((b <+> (((e <+> ((e <+> e) <+> e)) <+> e) <+> (e <+> m))) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f b (f (f (f e (f (f e e) e)) e) (f e m))) (f e m))) ((f (f b (f (f (f e (f e e)) e) (f e m))) (f e m))).
surgery id_l ((f (f b (f (f (f e (f e e)) e) (f e m))) (f e m))) ((f (f b (f (f (f e e) e) (f e m))) (f e m))).
surgery id_l ((f (f b (f (f (f e e) e) (f e m))) (f e m))) ((f (f b (f (f e e) (f e m))) (f e m))).
surgery id_l ((f (f b (f (f e e) (f e m))) (f e m))) ((f (f b (f e (f e m))) (f e m))).
surgery id_l ((f (f b (f e (f e m))) (f e m))) ((f (f b (f e m)) (f e m))).
surgery id_l ((f (f b (f e m)) (f e m))) ((f (f b m) (f e m))).
surgery id_r ((f (f b m) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_189: forall b: G, (((((e <+> m) <+> e) <+> (e <+> e)) <+> ((e <+> m) <+> e)) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e m) e) (f e e)) (f (f e m) e)) (f b m))) ((f (f (f (f e e) (f e e)) (f (f e m) e)) (f b m))).
surgery id_l ((f (f (f (f e e) (f e e)) (f (f e m) e)) (f b m))) ((f (f (f e (f e e)) (f (f e m) e)) (f b m))).
surgery id_l ((f (f (f e (f e e)) (f (f e m) e)) (f b m))) ((f (f (f e e) (f (f e m) e)) (f b m))).
surgery id_l ((f (f (f e e) (f (f e m) e)) (f b m))) ((f (f e (f (f e m) e)) (f b m))).
surgery id_r ((f (f e (f (f e m) e)) (f b m))) ((f (f e (f e e)) (f b m))).
surgery id_l ((f (f e (f e e)) (f b m))) ((f (f e e) (f b m))).
surgery id_l ((f (f e e) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_190: forall b: G, (((e <+> ((e <+> m) <+> m)) <+> (b <+> m)) <+> (m <+> (e <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f e m) m)) (f b m)) (f m (f e (f m m))))) ((f (f (f e (f e m)) (f b m)) (f m (f e (f m m))))).
surgery id_l ((f (f (f e (f e m)) (f b m)) (f m (f e (f m m))))) ((f (f (f e m) (f b m)) (f m (f e (f m m))))).
surgery id_r ((f (f (f e m) (f b m)) (f m (f e (f m m))))) ((f (f e (f b m)) (f m (f e (f m m))))).
surgery id_r ((f (f e (f b m)) (f m (f e (f m m))))) ((f (f e b) (f m (f e (f m m))))).
surgery id_l ((f (f e b) (f m (f e (f m m))))) ((f b (f m (f e (f m m))))).
surgery id_l ((f b (f m (f e (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_191: forall b: G, ((e <+> m) <+> ((e <+> (e <+> e)) <+> (e <+> ((e <+> m) <+> (b <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f e (f e e)) (f e (f (f e m) (f b m)))))) ((f e (f (f e (f e e)) (f e (f (f e m) (f b m)))))).
surgery id_l ((f e (f (f e (f e e)) (f e (f (f e m) (f b m)))))) ((f e (f (f e e) (f e (f (f e m) (f b m)))))).
surgery id_l ((f e (f (f e e) (f e (f (f e m) (f b m)))))) ((f e (f e (f e (f (f e m) (f b m)))))).
surgery id_l ((f e (f e (f e (f (f e m) (f b m)))))) ((f e (f e (f (f e m) (f b m))))).
surgery id_l ((f e (f e (f (f e m) (f b m))))) ((f e (f (f e m) (f b m)))).
surgery id_r ((f e (f (f e m) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_192: forall b: G, ((b <+> m) <+> (((e <+> m) <+> (m <+> (e <+> m))) <+> (m <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f (f e m) (f m (f e m))) (f m (f m m))))) ((f b (f (f (f e m) (f m (f e m))) (f m (f m m))))).
surgery id_r ((f b (f (f (f e m) (f m (f e m))) (f m (f m m))))) ((f b (f (f e (f m (f e m))) (f m (f m m))))).
surgery id_l ((f b (f (f e (f m (f e m))) (f m (f m m))))) ((f b (f (f e (f m m)) (f m (f m m))))).
surgery id_r ((f b (f (f e (f m m)) (f m (f m m))))) ((f b (f (f e m) (f m (f m m))))).
surgery id_r ((f b (f (f e m) (f m (f m m))))) ((f b (f e (f m (f m m))))).
surgery id_l ((f b (f e (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_193: forall b: G, (((e <+> b) <+> ((e <+> (e <+> m)) <+> m)) <+> ((e <+> e) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e b) (f (f e (f e m)) m)) (f (f e e) (f m m)))) ((f (f b (f (f e (f e m)) m)) (f (f e e) (f m m)))).
surgery id_l ((f (f b (f (f e (f e m)) m)) (f (f e e) (f m m)))) ((f (f b (f (f e m) m)) (f (f e e) (f m m)))).
surgery id_r ((f (f b (f (f e m) m)) (f (f e e) (f m m)))) ((f (f b (f e m)) (f (f e e) (f m m)))).
surgery id_l ((f (f b (f e m)) (f (f e e) (f m m)))) ((f (f b m) (f (f e e) (f m m)))).
surgery id_r ((f (f b m) (f (f e e) (f m m)))) ((f b (f (f e e) (f m m)))).
surgery id_l ((f b (f (f e e) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_194: forall b: G, ((((e <+> e) <+> m) <+> b) <+> ((e <+> (m <+> m)) <+> ((e <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) b) (f (f e (f m m)) (f (f e m) m)))) ((f (f (f e e) b) (f (f e (f m m)) (f (f e m) m)))).
surgery id_l ((f (f (f e e) b) (f (f e (f m m)) (f (f e m) m)))) ((f (f e b) (f (f e (f m m)) (f (f e m) m)))).
surgery id_l ((f (f e b) (f (f e (f m m)) (f (f e m) m)))) ((f b (f (f e (f m m)) (f (f e m) m)))).
surgery id_r ((f b (f (f e (f m m)) (f (f e m) m)))) ((f b (f (f e m) (f (f e m) m)))).
surgery id_r ((f b (f (f e m) (f (f e m) m)))) ((f b (f e (f (f e m) m)))).
surgery id_l ((f b (f e (f (f e m) m)))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_195: forall b: G, (b <+> (((e <+> e) <+> m) <+> ((e <+> ((e <+> m) <+> m)) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f b (f (f (f e e) m) (f (f e (f (f e m) m)) (f m m))))) ((f b (f (f e e) (f (f e (f (f e m) m)) (f m m))))).
surgery id_l ((f b (f (f e e) (f (f e (f (f e m) m)) (f m m))))) ((f b (f e (f (f e (f (f e m) m)) (f m m))))).
surgery id_l ((f b (f e (f (f e (f (f e m) m)) (f m m))))) ((f b (f (f e (f (f e m) m)) (f m m)))).
surgery id_r ((f b (f (f e (f (f e m) m)) (f m m)))) ((f b (f (f e (f e m)) (f m m)))).
surgery id_l ((f b (f (f e (f e m)) (f m m)))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_196: forall b: G, ((((((e <+> e) <+> (e <+> e)) <+> e) <+> m) <+> (e <+> (e <+> e))) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f (f e e) (f e e)) e) m) (f e (f e e))) b)) ((f (f (f (f (f e e) (f e e)) e) (f e (f e e))) b)).
surgery id_l ((f (f (f (f (f e e) (f e e)) e) (f e (f e e))) b)) ((f (f (f (f e (f e e)) e) (f e (f e e))) b)).
surgery id_l ((f (f (f (f e (f e e)) e) (f e (f e e))) b)) ((f (f (f (f e e) e) (f e (f e e))) b)).
surgery id_l ((f (f (f (f e e) e) (f e (f e e))) b)) ((f (f (f e e) (f e (f e e))) b)).
surgery id_l ((f (f (f e e) (f e (f e e))) b)) ((f (f e (f e (f e e))) b)).
surgery id_l ((f (f e (f e (f e e))) b)) ((f (f e (f e e)) b)).
surgery id_l ((f (f e (f e e)) b)) ((f (f e e) b)).
surgery id_l ((f (f e e) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_197: forall b: G, ((((e <+> e) <+> e) <+> (b <+> m)) <+> (((e <+> m) <+> m) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) e) (f b m)) (f (f (f e m) m) (f e m)))) ((f (f (f e e) (f b m)) (f (f (f e m) m) (f e m)))).
surgery id_l ((f (f (f e e) (f b m)) (f (f (f e m) m) (f e m)))) ((f (f e (f b m)) (f (f (f e m) m) (f e m)))).
surgery id_r ((f (f e (f b m)) (f (f (f e m) m) (f e m)))) ((f (f e b) (f (f (f e m) m) (f e m)))).
surgery id_l ((f (f e b) (f (f (f e m) m) (f e m)))) ((f b (f (f (f e m) m) (f e m)))).
surgery id_r ((f b (f (f (f e m) m) (f e m)))) ((f b (f (f e m) (f e m)))).
surgery id_r ((f b (f (f e m) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_198: forall b: G, (((e <+> ((b <+> m) <+> m)) <+> ((e <+> (m <+> m)) <+> (e <+> m))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f b m) m)) (f (f e (f m m)) (f e m))) m)) ((f (f e (f (f b m) m)) (f (f e (f m m)) (f e m)))).
surgery id_r ((f (f e (f (f b m) m)) (f (f e (f m m)) (f e m)))) ((f (f e (f b m)) (f (f e (f m m)) (f e m)))).
surgery id_r ((f (f e (f b m)) (f (f e (f m m)) (f e m)))) ((f (f e b) (f (f e (f m m)) (f e m)))).
surgery id_l ((f (f e b) (f (f e (f m m)) (f e m)))) ((f b (f (f e (f m m)) (f e m)))).
surgery id_r ((f b (f (f e (f m m)) (f e m)))) ((f b (f (f e m) (f e m)))).
surgery id_r ((f b (f (f e m) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_199: forall b: G, (b <+> ((((e <+> (e <+> e)) <+> e) <+> e) <+> ((e <+> m) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f b (f (f (f (f e (f e e)) e) e) (f (f e m) (f m m))))) ((f b (f (f (f (f e e) e) e) (f (f e m) (f m m))))).
surgery id_l ((f b (f (f (f (f e e) e) e) (f (f e m) (f m m))))) ((f b (f (f (f e e) e) (f (f e m) (f m m))))).
surgery id_l ((f b (f (f (f e e) e) (f (f e m) (f m m))))) ((f b (f (f e e) (f (f e m) (f m m))))).
surgery id_l ((f b (f (f e e) (f (f e m) (f m m))))) ((f b (f e (f (f e m) (f m m))))).
surgery id_l ((f b (f e (f (f e m) (f m m))))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_200: forall b: G, (((e <+> b) <+> (((e <+> e) <+> m) <+> ((e <+> m) <+> (m <+> m)))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f e b) (f (f (f e e) m) (f (f e m) (f m m)))) m)) ((f (f e b) (f (f (f e e) m) (f (f e m) (f m m))))).
surgery id_l ((f (f e b) (f (f (f e e) m) (f (f e m) (f m m))))) ((f b (f (f (f e e) m) (f (f e m) (f m m))))).
surgery id_r ((f b (f (f (f e e) m) (f (f e m) (f m m))))) ((f b (f (f e e) (f (f e m) (f m m))))).
surgery id_l ((f b (f (f e e) (f (f e m) (f m m))))) ((f b (f e (f (f e m) (f m m))))).
surgery id_l ((f b (f e (f (f e m) (f m m))))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_201: forall b: G, (((((e <+> m) <+> (e <+> (e <+> m))) <+> (e <+> (e <+> e))) <+> b) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e m) (f e (f e m))) (f e (f e e))) b) m)) ((f (f (f (f e m) (f e (f e m))) (f e (f e e))) b)).
surgery id_r ((f (f (f (f e m) (f e (f e m))) (f e (f e e))) b)) ((f (f (f e (f e (f e m))) (f e (f e e))) b)).
surgery id_l ((f (f (f e (f e (f e m))) (f e (f e e))) b)) ((f (f (f e (f e m)) (f e (f e e))) b)).
surgery id_l ((f (f (f e (f e m)) (f e (f e e))) b)) ((f (f (f e m) (f e (f e e))) b)).
surgery id_r ((f (f (f e m) (f e (f e e))) b)) ((f (f e (f e (f e e))) b)).
surgery id_l ((f (f e (f e (f e e))) b)) ((f (f e (f e e)) b)).
surgery id_l ((f (f e (f e e)) b)) ((f (f e e) b)).
surgery id_l ((f (f e e) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_202: forall b: G, ((b <+> (m <+> (m <+> (m <+> m)))) <+> (((e <+> m) <+> e) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b (f m (f m (f m m)))) (f (f (f e m) e) (f m m)))) ((f (f b (f m (f m m))) (f (f (f e m) e) (f m m)))).
surgery id_r ((f (f b (f m (f m m))) (f (f (f e m) e) (f m m)))) ((f (f b (f m m)) (f (f (f e m) e) (f m m)))).
surgery id_r ((f (f b (f m m)) (f (f (f e m) e) (f m m)))) ((f (f b m) (f (f (f e m) e) (f m m)))).
surgery id_r ((f (f b m) (f (f (f e m) e) (f m m)))) ((f b (f (f (f e m) e) (f m m)))).
surgery id_r ((f b (f (f (f e m) e) (f m m)))) ((f b (f (f e e) (f m m)))).
surgery id_l ((f b (f (f e e) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_203: forall b: G, ((((e <+> m) <+> e) <+> (m <+> (e <+> m))) <+> (((e <+> e) <+> b) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) e) (f m (f e m))) (f (f (f e e) b) m))) ((f (f (f e e) (f m (f e m))) (f (f (f e e) b) m))).
surgery id_l ((f (f (f e e) (f m (f e m))) (f (f (f e e) b) m))) ((f (f e (f m (f e m))) (f (f (f e e) b) m))).
surgery id_l ((f (f e (f m (f e m))) (f (f (f e e) b) m))) ((f (f e (f m m)) (f (f (f e e) b) m))).
surgery id_r ((f (f e (f m m)) (f (f (f e e) b) m))) ((f (f e m) (f (f (f e e) b) m))).
surgery id_r ((f (f e m) (f (f (f e e) b) m))) ((f e (f (f (f e e) b) m))).
surgery id_l ((f e (f (f (f e e) b) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_204: forall b: G, (((e <+> (e <+> (b <+> m))) <+> ((e <+> m) <+> (e <+> (m <+> m)))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f e (f b m))) (f (f e m) (f e (f m m)))) m)) ((f (f e (f e (f b m))) (f (f e m) (f e (f m m))))).
surgery id_l ((f (f e (f e (f b m))) (f (f e m) (f e (f m m))))) ((f (f e (f b m)) (f (f e m) (f e (f m m))))).
surgery id_r ((f (f e (f b m)) (f (f e m) (f e (f m m))))) ((f (f e b) (f (f e m) (f e (f m m))))).
surgery id_l ((f (f e b) (f (f e m) (f e (f m m))))) ((f b (f (f e m) (f e (f m m))))).
surgery id_r ((f b (f (f e m) (f e (f m m))))) ((f b (f e (f e (f m m))))).
surgery id_l ((f b (f e (f e (f m m))))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_205: forall b: G, ((((e <+> e) <+> e) <+> (m <+> (e <+> (m <+> (e <+> m))))) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) e) (f m (f e (f m (f e m))))) (f b m))) ((f (f (f e e) (f m (f e (f m (f e m))))) (f b m))).
surgery id_l ((f (f (f e e) (f m (f e (f m (f e m))))) (f b m))) ((f (f e (f m (f e (f m (f e m))))) (f b m))).
surgery id_l ((f (f e (f m (f e (f m (f e m))))) (f b m))) ((f (f e (f m (f m (f e m)))) (f b m))).
surgery id_l ((f (f e (f m (f m (f e m)))) (f b m))) ((f (f e (f m (f m m))) (f b m))).
surgery id_r ((f (f e (f m (f m m))) (f b m))) ((f (f e (f m m)) (f b m))).
surgery id_r ((f (f e (f m m)) (f b m))) ((f (f e m) (f b m))).
surgery id_r ((f (f e m) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_206: forall b: G, (((e <+> (b <+> ((e <+> (e <+> e)) <+> (e <+> m)))) <+> (e <+> m)) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f b (f (f e (f e e)) (f e m)))) (f e m)) m)) ((f (f e (f b (f (f e (f e e)) (f e m)))) (f e m))).
surgery id_l ((f (f e (f b (f (f e (f e e)) (f e m)))) (f e m))) ((f (f e (f b (f (f e e) (f e m)))) (f e m))).
surgery id_l ((f (f e (f b (f (f e e) (f e m)))) (f e m))) ((f (f e (f b (f e (f e m)))) (f e m))).
surgery id_l ((f (f e (f b (f e (f e m)))) (f e m))) ((f (f e (f b (f e m))) (f e m))).
surgery id_l ((f (f e (f b (f e m))) (f e m))) ((f (f e (f b m)) (f e m))).
surgery id_r ((f (f e (f b m)) (f e m))) ((f (f e b) (f e m))).
surgery id_l ((f (f e b) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_207: forall b: G, (((e <+> b) <+> (m <+> (m <+> m))) <+> (((e <+> m) <+> (e <+> e)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e b) (f m (f m m))) (f (f (f e m) (f e e)) m))) ((f (f b (f m (f m m))) (f (f (f e m) (f e e)) m))).
surgery id_r ((f (f b (f m (f m m))) (f (f (f e m) (f e e)) m))) ((f (f b (f m m)) (f (f (f e m) (f e e)) m))).
surgery id_r ((f (f b (f m m)) (f (f (f e m) (f e e)) m))) ((f (f b m) (f (f (f e m) (f e e)) m))).
surgery id_r ((f (f b m) (f (f (f e m) (f e e)) m))) ((f b (f (f (f e m) (f e e)) m))).
surgery id_r ((f b (f (f (f e m) (f e e)) m))) ((f b (f (f e (f e e)) m))).
surgery id_l ((f b (f (f e (f e e)) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_208: forall b: G, ((e <+> e) <+> (((e <+> (e <+> (e <+> m))) <+> m) <+> ((e <+> b) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f (f e (f e (f e m))) m) (f (f e b) m)))) ((f e (f (f (f e (f e (f e m))) m) (f (f e b) m)))).
surgery id_r ((f e (f (f (f e (f e (f e m))) m) (f (f e b) m)))) ((f e (f (f e (f e (f e m))) (f (f e b) m)))).
surgery id_l ((f e (f (f e (f e (f e m))) (f (f e b) m)))) ((f e (f (f e (f e m)) (f (f e b) m)))).
surgery id_l ((f e (f (f e (f e m)) (f (f e b) m)))) ((f e (f (f e m) (f (f e b) m)))).
surgery id_r ((f e (f (f e m) (f (f e b) m)))) ((f e (f e (f (f e b) m)))).
surgery id_l ((f e (f e (f (f e b) m)))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_209: forall b: G, ((e <+> (m <+> m)) <+> (e <+> (e <+> (((e <+> m) <+> b) <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f e (f m m)) (f e (f e (f (f (f e m) b) (f e m)))))) ((f (f e m) (f e (f e (f (f (f e m) b) (f e m)))))).
surgery id_r ((f (f e m) (f e (f e (f (f (f e m) b) (f e m)))))) ((f e (f e (f e (f (f (f e m) b) (f e m)))))).
surgery id_l ((f e (f e (f e (f (f (f e m) b) (f e m)))))) ((f e (f e (f (f (f e m) b) (f e m))))).
surgery id_l ((f e (f e (f (f (f e m) b) (f e m))))) ((f e (f (f (f e m) b) (f e m)))).
surgery id_r ((f e (f (f (f e m) b) (f e m)))) ((f e (f (f e b) (f e m)))).
surgery id_l ((f e (f (f e b) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_210: forall b: G, ((((e <+> b) <+> (e <+> m)) <+> (((e <+> m) <+> e) <+> (m <+> m))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e b) (f e m)) (f (f (f e m) e) (f m m))) m)) ((f (f (f e b) (f e m)) (f (f (f e m) e) (f m m)))).
surgery id_l ((f (f (f e b) (f e m)) (f (f (f e m) e) (f m m)))) ((f (f b (f e m)) (f (f (f e m) e) (f m m)))).
surgery id_l ((f (f b (f e m)) (f (f (f e m) e) (f m m)))) ((f (f b m) (f (f (f e m) e) (f m m)))).
surgery id_r ((f (f b m) (f (f (f e m) e) (f m m)))) ((f b (f (f (f e m) e) (f m m)))).
surgery id_r ((f b (f (f (f e m) e) (f m m)))) ((f b (f (f e e) (f m m)))).
surgery id_l ((f b (f (f e e) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_211: forall b: G, (((e <+> m) <+> (e <+> e)) <+> (((e <+> ((e <+> m) <+> m)) <+> b) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f e e)) (f (f (f e (f (f e m) m)) b) m))) ((f (f e (f e e)) (f (f (f e (f (f e m) m)) b) m))).
surgery id_l ((f (f e (f e e)) (f (f (f e (f (f e m) m)) b) m))) ((f (f e e) (f (f (f e (f (f e m) m)) b) m))).
surgery id_l ((f (f e e) (f (f (f e (f (f e m) m)) b) m))) ((f e (f (f (f e (f (f e m) m)) b) m))).
surgery id_r ((f e (f (f (f e (f (f e m) m)) b) m))) ((f e (f (f (f e (f e m)) b) m))).
surgery id_l ((f e (f (f (f e (f e m)) b) m))) ((f e (f (f (f e m) b) m))).
surgery id_r ((f e (f (f (f e m) b) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_212: forall b: G, ((e <+> (e <+> (e <+> m))) <+> (((e <+> m) <+> m) <+> ((b <+> m) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e (f e m))) (f (f (f e m) m) (f (f b m) m)))) ((f (f e (f e m)) (f (f (f e m) m) (f (f b m) m)))).
surgery id_l ((f (f e (f e m)) (f (f (f e m) m) (f (f b m) m)))) ((f (f e m) (f (f (f e m) m) (f (f b m) m)))).
surgery id_r ((f (f e m) (f (f (f e m) m) (f (f b m) m)))) ((f e (f (f (f e m) m) (f (f b m) m)))).
surgery id_r ((f e (f (f (f e m) m) (f (f b m) m)))) ((f e (f (f e m) (f (f b m) m)))).
surgery id_r ((f e (f (f e m) (f (f b m) m)))) ((f e (f e (f (f b m) m)))).
surgery id_l ((f e (f e (f (f b m) m)))) ((f e (f (f b m) m))).
surgery id_r ((f e (f (f b m) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_213: forall b: G, ((e <+> (e <+> (e <+> m))) <+> (b <+> ((e <+> (e <+> m)) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e (f e m))) (f b (f (f e (f e m)) (f e m))))) ((f (f e (f e m)) (f b (f (f e (f e m)) (f e m))))).
surgery id_l ((f (f e (f e m)) (f b (f (f e (f e m)) (f e m))))) ((f (f e m) (f b (f (f e (f e m)) (f e m))))).
surgery id_r ((f (f e m) (f b (f (f e (f e m)) (f e m))))) ((f e (f b (f (f e (f e m)) (f e m))))).
surgery id_l ((f e (f b (f (f e (f e m)) (f e m))))) ((f e (f b (f (f e m) (f e m))))).
surgery id_r ((f e (f b (f (f e m) (f e m))))) ((f e (f b (f e (f e m))))).
surgery id_l ((f e (f b (f e (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_214: forall b: G, ((e <+> m) <+> (((e <+> (e <+> m)) <+> (e <+> e)) <+> ((e <+> b) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f (f e (f e m)) (f e e)) (f (f e b) m)))) ((f e (f (f (f e (f e m)) (f e e)) (f (f e b) m)))).
surgery id_l ((f e (f (f (f e (f e m)) (f e e)) (f (f e b) m)))) ((f e (f (f (f e m) (f e e)) (f (f e b) m)))).
surgery id_r ((f e (f (f (f e m) (f e e)) (f (f e b) m)))) ((f e (f (f e (f e e)) (f (f e b) m)))).
surgery id_l ((f e (f (f e (f e e)) (f (f e b) m)))) ((f e (f (f e e) (f (f e b) m)))).
surgery id_l ((f e (f (f e e) (f (f e b) m)))) ((f e (f e (f (f e b) m)))).
surgery id_l ((f e (f e (f (f e b) m)))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_215: forall b: G, ((((e <+> m) <+> m) <+> (e <+> e)) <+> ((e <+> e) <+> (e <+> (e <+> b)))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) m) (f e e)) (f (f e e) (f e (f e b))))) ((f (f (f e m) (f e e)) (f (f e e) (f e (f e b))))).
surgery id_r ((f (f (f e m) (f e e)) (f (f e e) (f e (f e b))))) ((f (f e (f e e)) (f (f e e) (f e (f e b))))).
surgery id_l ((f (f e (f e e)) (f (f e e) (f e (f e b))))) ((f (f e e) (f (f e e) (f e (f e b))))).
surgery id_l ((f (f e e) (f (f e e) (f e (f e b))))) ((f e (f (f e e) (f e (f e b))))).
surgery id_l ((f e (f (f e e) (f e (f e b))))) ((f e (f e (f e (f e b))))).
surgery id_l ((f e (f e (f e (f e b))))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_216: forall b: G, (b <+> ((((e <+> e) <+> (m <+> m)) <+> m) <+> (m <+> ((e <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f b (f (f (f (f e e) (f m m)) m) (f m (f (f e m) m))))) ((f b (f (f (f e e) (f m m)) (f m (f (f e m) m))))).
surgery id_l ((f b (f (f (f e e) (f m m)) (f m (f (f e m) m))))) ((f b (f (f e (f m m)) (f m (f (f e m) m))))).
surgery id_r ((f b (f (f e (f m m)) (f m (f (f e m) m))))) ((f b (f (f e m) (f m (f (f e m) m))))).
surgery id_r ((f b (f (f e m) (f m (f (f e m) m))))) ((f b (f e (f m (f (f e m) m))))).
surgery id_l ((f b (f e (f m (f (f e m) m))))) ((f b (f m (f (f e m) m)))).
surgery id_r ((f b (f m (f (f e m) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_217: forall b: G, ((e <+> m) <+> (b <+> ((e <+> (e <+> (e <+> e))) <+> (m <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f b (f (f e (f e (f e e))) (f m (f e m)))))) ((f e (f b (f (f e (f e (f e e))) (f m (f e m)))))).
surgery id_l ((f e (f b (f (f e (f e (f e e))) (f m (f e m)))))) ((f e (f b (f (f e (f e e)) (f m (f e m)))))).
surgery id_l ((f e (f b (f (f e (f e e)) (f m (f e m)))))) ((f e (f b (f (f e e) (f m (f e m)))))).
surgery id_l ((f e (f b (f (f e e) (f m (f e m)))))) ((f e (f b (f e (f m (f e m)))))).
surgery id_l ((f e (f b (f e (f m (f e m)))))) ((f e (f b (f m (f e m))))).
surgery id_l ((f e (f b (f m (f e m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_218: forall b: G, ((((e <+> e) <+> m) <+> (e <+> ((e <+> m) <+> (m <+> m)))) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) (f e (f (f e m) (f m m)))) (f b m))) ((f (f (f e e) (f e (f (f e m) (f m m)))) (f b m))).
surgery id_l ((f (f (f e e) (f e (f (f e m) (f m m)))) (f b m))) ((f (f e (f e (f (f e m) (f m m)))) (f b m))).
surgery id_l ((f (f e (f e (f (f e m) (f m m)))) (f b m))) ((f (f e (f (f e m) (f m m))) (f b m))).
surgery id_r ((f (f e (f (f e m) (f m m))) (f b m))) ((f (f e (f e (f m m))) (f b m))).
surgery id_l ((f (f e (f e (f m m))) (f b m))) ((f (f e (f m m)) (f b m))).
surgery id_r ((f (f e (f m m)) (f b m))) ((f (f e m) (f b m))).
surgery id_r ((f (f e m) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_219: forall b: G, (((b <+> m) <+> m) <+> ((e <+> m) <+> ((m <+> m) <+> (e <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) m) (f (f e m) (f (f m m) (f e (f e m)))))) ((f (f b m) (f (f e m) (f (f m m) (f e (f e m)))))).
surgery id_r ((f (f b m) (f (f e m) (f (f m m) (f e (f e m)))))) ((f b (f (f e m) (f (f m m) (f e (f e m)))))).
surgery id_r ((f b (f (f e m) (f (f m m) (f e (f e m)))))) ((f b (f e (f (f m m) (f e (f e m)))))).
surgery id_l ((f b (f e (f (f m m) (f e (f e m)))))) ((f b (f (f m m) (f e (f e m))))).
surgery id_r ((f b (f (f m m) (f e (f e m))))) ((f b (f m (f e (f e m))))).
surgery id_l ((f b (f m (f e (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_220: forall b: G, ((((e <+> e) <+> m) <+> ((b <+> m) <+> m)) <+> ((e <+> m) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) (f (f b m) m)) (f (f e m) (f m m)))) ((f (f (f e e) (f (f b m) m)) (f (f e m) (f m m)))).
surgery id_l ((f (f (f e e) (f (f b m) m)) (f (f e m) (f m m)))) ((f (f e (f (f b m) m)) (f (f e m) (f m m)))).
surgery id_r ((f (f e (f (f b m) m)) (f (f e m) (f m m)))) ((f (f e (f b m)) (f (f e m) (f m m)))).
surgery id_r ((f (f e (f b m)) (f (f e m) (f m m)))) ((f (f e b) (f (f e m) (f m m)))).
surgery id_l ((f (f e b) (f (f e m) (f m m)))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_221: forall b: G, ((((e <+> (e <+> e)) <+> e) <+> ((e <+> m) <+> m)) <+> ((b <+> m) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e (f e e)) e) (f (f e m) m)) (f (f b m) m))) ((f (f (f (f e e) e) (f (f e m) m)) (f (f b m) m))).
surgery id_l ((f (f (f (f e e) e) (f (f e m) m)) (f (f b m) m))) ((f (f (f e e) (f (f e m) m)) (f (f b m) m))).
surgery id_l ((f (f (f e e) (f (f e m) m)) (f (f b m) m))) ((f (f e (f (f e m) m)) (f (f b m) m))).
surgery id_r ((f (f e (f (f e m) m)) (f (f b m) m))) ((f (f e (f e m)) (f (f b m) m))).
surgery id_l ((f (f e (f e m)) (f (f b m) m))) ((f (f e m) (f (f b m) m))).
surgery id_r ((f (f e m) (f (f b m) m))) ((f e (f (f b m) m))).
surgery id_r ((f e (f (f b m) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_222: forall b: G, (((((e <+> e) <+> e) <+> (m <+> (((e <+> m) <+> e) <+> m))) <+> m) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e e) e) (f m (f (f (f e m) e) m))) m) b)) ((f (f (f (f e e) e) (f m (f (f (f e m) e) m))) b)).
surgery id_l ((f (f (f (f e e) e) (f m (f (f (f e m) e) m))) b)) ((f (f (f e e) (f m (f (f (f e m) e) m))) b)).
surgery id_l ((f (f (f e e) (f m (f (f (f e m) e) m))) b)) ((f (f e (f m (f (f (f e m) e) m))) b)).
surgery id_r ((f (f e (f m (f (f (f e m) e) m))) b)) ((f (f e (f m (f (f e e) m))) b)).
surgery id_l ((f (f e (f m (f (f e e) m))) b)) ((f (f e (f m (f e m))) b)).
surgery id_l ((f (f e (f m (f e m))) b)) ((f (f e (f m m)) b)).
surgery id_r ((f (f e (f m m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_223: forall b: G, ((b <+> m) <+> ((e <+> (e <+> m)) <+> (m <+> ((e <+> e) <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f e (f e m)) (f m (f (f e e) (f e m)))))) ((f b (f (f e (f e m)) (f m (f (f e e) (f e m)))))).
surgery id_l ((f b (f (f e (f e m)) (f m (f (f e e) (f e m)))))) ((f b (f (f e m) (f m (f (f e e) (f e m)))))).
surgery id_r ((f b (f (f e m) (f m (f (f e e) (f e m)))))) ((f b (f e (f m (f (f e e) (f e m)))))).
surgery id_l ((f b (f e (f m (f (f e e) (f e m)))))) ((f b (f m (f (f e e) (f e m))))).
surgery id_l ((f b (f m (f (f e e) (f e m))))) ((f b (f m (f e (f e m))))).
surgery id_l ((f b (f m (f e (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_224: forall b: G, ((((b <+> m) <+> ((m <+> m) <+> (e <+> m))) <+> (e <+> (m <+> m))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f b m) (f (f m m) (f e m))) (f e (f m m))) m)) ((f (f (f b m) (f (f m m) (f e m))) (f e (f m m)))).
surgery id_r ((f (f (f b m) (f (f m m) (f e m))) (f e (f m m)))) ((f (f b (f (f m m) (f e m))) (f e (f m m)))).
surgery id_r ((f (f b (f (f m m) (f e m))) (f e (f m m)))) ((f (f b (f m (f e m))) (f e (f m m)))).
surgery id_l ((f (f b (f m (f e m))) (f e (f m m)))) ((f (f b (f m m)) (f e (f m m)))).
surgery id_r ((f (f b (f m m)) (f e (f m m)))) ((f (f b m) (f e (f m m)))).
surgery id_r ((f (f b m) (f e (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_225: forall b: G, ((((e <+> (((e <+> m) <+> e) <+> (e <+> e))) <+> e) <+> (e <+> m)) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e (f (f (f e m) e) (f e e))) e) (f e m)) b)) ((f (f (f (f e (f (f e e) (f e e))) e) (f e m)) b)).
surgery id_l ((f (f (f (f e (f (f e e) (f e e))) e) (f e m)) b)) ((f (f (f (f e (f e (f e e))) e) (f e m)) b)).
surgery id_l ((f (f (f (f e (f e (f e e))) e) (f e m)) b)) ((f (f (f (f e (f e e)) e) (f e m)) b)).
surgery id_l ((f (f (f (f e (f e e)) e) (f e m)) b)) ((f (f (f (f e e) e) (f e m)) b)).
surgery id_l ((f (f (f (f e e) e) (f e m)) b)) ((f (f (f e e) (f e m)) b)).
surgery id_l ((f (f (f e e) (f e m)) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_226: forall b: G, (((e <+> (e <+> b)) <+> ((e <+> m) <+> m)) <+> (m <+> (m <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e b)) (f (f e m) m)) (f m (f m (f e m))))) ((f (f (f e b) (f (f e m) m)) (f m (f m (f e m))))).
surgery id_l ((f (f (f e b) (f (f e m) m)) (f m (f m (f e m))))) ((f (f b (f (f e m) m)) (f m (f m (f e m))))).
surgery id_r ((f (f b (f (f e m) m)) (f m (f m (f e m))))) ((f (f b (f e m)) (f m (f m (f e m))))).
surgery id_l ((f (f b (f e m)) (f m (f m (f e m))))) ((f (f b m) (f m (f m (f e m))))).
surgery id_r ((f (f b m) (f m (f m (f e m))))) ((f b (f m (f m (f e m))))).
surgery id_l ((f b (f m (f m (f e m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_227: forall b: G, (((e <+> (e <+> m)) <+> ((e <+> m) <+> m)) <+> (e <+> ((e <+> m) <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f (f e m) m)) (f e (f (f e m) b)))) ((f (f (f e m) (f (f e m) m)) (f e (f (f e m) b)))).
surgery id_r ((f (f (f e m) (f (f e m) m)) (f e (f (f e m) b)))) ((f (f e (f (f e m) m)) (f e (f (f e m) b)))).
surgery id_r ((f (f e (f (f e m) m)) (f e (f (f e m) b)))) ((f (f e (f e m)) (f e (f (f e m) b)))).
surgery id_l ((f (f e (f e m)) (f e (f (f e m) b)))) ((f (f e m) (f e (f (f e m) b)))).
surgery id_r ((f (f e m) (f e (f (f e m) b)))) ((f e (f e (f (f e m) b)))).
surgery id_l ((f e (f e (f (f e m) b)))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_228: forall b: G, (((e <+> m) <+> (e <+> e)) <+> ((e <+> b) <+> ((m <+> m) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f e e)) (f (f e b) (f (f m m) (f m m))))) ((f (f e (f e e)) (f (f e b) (f (f m m) (f m m))))).
surgery id_l ((f (f e (f e e)) (f (f e b) (f (f m m) (f m m))))) ((f (f e e) (f (f e b) (f (f m m) (f m m))))).
surgery id_l ((f (f e e) (f (f e b) (f (f m m) (f m m))))) ((f e (f (f e b) (f (f m m) (f m m))))).
surgery id_l ((f e (f (f e b) (f (f m m) (f m m))))) ((f e (f b (f (f m m) (f m m))))).
surgery id_r ((f e (f b (f (f m m) (f m m))))) ((f e (f b (f m (f m m))))).
surgery id_r ((f e (f b (f m (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_229: forall b: G, ((e <+> ((m <+> (e <+> m)) <+> (m <+> m))) <+> (b <+> ((e <+> m) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f m (f e m)) (f m m))) (f b (f (f e m) m)))) ((f (f e (f (f m m) (f m m))) (f b (f (f e m) m)))).
surgery id_r ((f (f e (f (f m m) (f m m))) (f b (f (f e m) m)))) ((f (f e (f m (f m m))) (f b (f (f e m) m)))).
surgery id_r ((f (f e (f m (f m m))) (f b (f (f e m) m)))) ((f (f e (f m m)) (f b (f (f e m) m)))).
surgery id_r ((f (f e (f m m)) (f b (f (f e m) m)))) ((f (f e m) (f b (f (f e m) m)))).
surgery id_r ((f (f e m) (f b (f (f e m) m)))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_230: forall b: G, (((e <+> m) <+> m) <+> ((e <+> (e <+> m)) <+> ((e <+> m) <+> (b <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) m) (f (f e (f e m)) (f (f e m) (f b m))))) ((f (f e m) (f (f e (f e m)) (f (f e m) (f b m))))).
surgery id_r ((f (f e m) (f (f e (f e m)) (f (f e m) (f b m))))) ((f e (f (f e (f e m)) (f (f e m) (f b m))))).
surgery id_l ((f e (f (f e (f e m)) (f (f e m) (f b m))))) ((f e (f (f e m) (f (f e m) (f b m))))).
surgery id_r ((f e (f (f e m) (f (f e m) (f b m))))) ((f e (f e (f (f e m) (f b m))))).
surgery id_l ((f e (f e (f (f e m) (f b m))))) ((f e (f (f e m) (f b m)))).
surgery id_r ((f e (f (f e m) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_231: forall b: G, ((e <+> m) <+> (e <+> (((e <+> m) <+> (e <+> m)) <+> (b <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f e (f (f (f e m) (f e m)) (f b (f m m)))))) ((f e (f e (f (f (f e m) (f e m)) (f b (f m m)))))).
surgery id_l ((f e (f e (f (f (f e m) (f e m)) (f b (f m m)))))) ((f e (f (f (f e m) (f e m)) (f b (f m m))))).
surgery id_r ((f e (f (f (f e m) (f e m)) (f b (f m m))))) ((f e (f (f e (f e m)) (f b (f m m))))).
surgery id_l ((f e (f (f e (f e m)) (f b (f m m))))) ((f e (f (f e m) (f b (f m m))))).
surgery id_r ((f e (f (f e m) (f b (f m m))))) ((f e (f e (f b (f m m))))).
surgery id_l ((f e (f e (f b (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_232: forall b: G, (((e <+> b) <+> m) <+> (((e <+> m) <+> m) <+> ((e <+> m) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e b) m) (f (f (f e m) m) (f (f e m) (f m m))))) ((f (f e b) (f (f (f e m) m) (f (f e m) (f m m))))).
surgery id_l ((f (f e b) (f (f (f e m) m) (f (f e m) (f m m))))) ((f b (f (f (f e m) m) (f (f e m) (f m m))))).
surgery id_r ((f b (f (f (f e m) m) (f (f e m) (f m m))))) ((f b (f (f e m) (f (f e m) (f m m))))).
surgery id_r ((f b (f (f e m) (f (f e m) (f m m))))) ((f b (f e (f (f e m) (f m m))))).
surgery id_l ((f b (f e (f (f e m) (f m m))))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_233: forall b: G, (((e <+> (((e <+> e) <+> m) <+> (e <+> b))) <+> m) <+> (m <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f (f e e) m) (f e b))) m) (f m (f e m)))) ((f (f e (f (f (f e e) m) (f e b))) (f m (f e m)))).
surgery id_r ((f (f e (f (f (f e e) m) (f e b))) (f m (f e m)))) ((f (f e (f (f e e) (f e b))) (f m (f e m)))).
surgery id_l ((f (f e (f (f e e) (f e b))) (f m (f e m)))) ((f (f e (f e (f e b))) (f m (f e m)))).
surgery id_l ((f (f e (f e (f e b))) (f m (f e m)))) ((f (f e (f e b)) (f m (f e m)))).
surgery id_l ((f (f e (f e b)) (f m (f e m)))) ((f (f e b) (f m (f e m)))).
surgery id_l ((f (f e b) (f m (f e m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_234: forall b: G, ((b <+> (e <+> m)) <+> (((e <+> m) <+> ((e <+> m) <+> m)) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f b (f e m)) (f (f (f e m) (f (f e m) m)) (f e m)))) ((f (f b m) (f (f (f e m) (f (f e m) m)) (f e m)))).
surgery id_r ((f (f b m) (f (f (f e m) (f (f e m) m)) (f e m)))) ((f b (f (f (f e m) (f (f e m) m)) (f e m)))).
surgery id_r ((f b (f (f (f e m) (f (f e m) m)) (f e m)))) ((f b (f (f e (f (f e m) m)) (f e m)))).
surgery id_r ((f b (f (f e (f (f e m) m)) (f e m)))) ((f b (f (f e (f e m)) (f e m)))).
surgery id_l ((f b (f (f e (f e m)) (f e m)))) ((f b (f (f e m) (f e m)))).
surgery id_r ((f b (f (f e m) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_235: forall b: G, ((b <+> m) <+> ((e <+> m) <+> (e <+> (((e <+> m) <+> m) <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f e m) (f e (f (f (f e m) m) (f m m)))))) ((f b (f (f e m) (f e (f (f (f e m) m) (f m m)))))).
surgery id_r ((f b (f (f e m) (f e (f (f (f e m) m) (f m m)))))) ((f b (f e (f e (f (f (f e m) m) (f m m)))))).
surgery id_l ((f b (f e (f e (f (f (f e m) m) (f m m)))))) ((f b (f e (f (f (f e m) m) (f m m))))).
surgery id_l ((f b (f e (f (f (f e m) m) (f m m))))) ((f b (f (f (f e m) m) (f m m)))).
surgery id_r ((f b (f (f (f e m) m) (f m m)))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_236: forall b: G, (((((e <+> m) <+> (e <+> (e <+> e))) <+> (e <+> m)) <+> e) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e m) (f e (f e e))) (f e m)) e) (f b m))) ((f (f (f (f e (f e (f e e))) (f e m)) e) (f b m))).
surgery id_l ((f (f (f (f e (f e (f e e))) (f e m)) e) (f b m))) ((f (f (f (f e (f e e)) (f e m)) e) (f b m))).
surgery id_l ((f (f (f (f e (f e e)) (f e m)) e) (f b m))) ((f (f (f (f e e) (f e m)) e) (f b m))).
surgery id_l ((f (f (f (f e e) (f e m)) e) (f b m))) ((f (f (f e (f e m)) e) (f b m))).
surgery id_l ((f (f (f e (f e m)) e) (f b m))) ((f (f (f e m) e) (f b m))).
surgery id_r ((f (f (f e m) e) (f b m))) ((f (f e e) (f b m))).
surgery id_l ((f (f e e) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_237: forall b: G, (e <+> ((e <+> m) <+> (((e <+> e) <+> (e <+> (m <+> m))) <+> (e <+> b)))) = b.
Proof.
intros.
surgery id_r ((f e (f (f e m) (f (f (f e e) (f e (f m m))) (f e b))))) ((f e (f e (f (f (f e e) (f e (f m m))) (f e b))))).
surgery id_l ((f e (f e (f (f (f e e) (f e (f m m))) (f e b))))) ((f e (f (f (f e e) (f e (f m m))) (f e b)))).
surgery id_l ((f e (f (f (f e e) (f e (f m m))) (f e b)))) ((f e (f (f e (f e (f m m))) (f e b)))).
surgery id_l ((f e (f (f e (f e (f m m))) (f e b)))) ((f e (f (f e (f m m)) (f e b)))).
surgery id_r ((f e (f (f e (f m m)) (f e b)))) ((f e (f (f e m) (f e b)))).
surgery id_r ((f e (f (f e m) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_238: forall b: G, ((e <+> ((e <+> e) <+> (((e <+> m) <+> m) <+> m))) <+> (b <+> (e <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f e e) (f (f (f e m) m) m))) (f b (f e m)))) ((f (f e (f e (f (f (f e m) m) m))) (f b (f e m)))).
surgery id_l ((f (f e (f e (f (f (f e m) m) m))) (f b (f e m)))) ((f (f e (f (f (f e m) m) m)) (f b (f e m)))).
surgery id_r ((f (f e (f (f (f e m) m) m)) (f b (f e m)))) ((f (f e (f (f e m) m)) (f b (f e m)))).
surgery id_r ((f (f e (f (f e m) m)) (f b (f e m)))) ((f (f e (f e m)) (f b (f e m)))).
surgery id_l ((f (f e (f e m)) (f b (f e m)))) ((f (f e m) (f b (f e m)))).
surgery id_r ((f (f e m) (f b (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_239: forall b: G, (((e <+> (((e <+> m) <+> e) <+> m)) <+> (((e <+> e) <+> m) <+> m)) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f (f e m) e) m)) (f (f (f e e) m) m)) b)) ((f (f (f e (f (f e e) m)) (f (f (f e e) m) m)) b)).
surgery id_l ((f (f (f e (f (f e e) m)) (f (f (f e e) m) m)) b)) ((f (f (f e (f e m)) (f (f (f e e) m) m)) b)).
surgery id_l ((f (f (f e (f e m)) (f (f (f e e) m) m)) b)) ((f (f (f e m) (f (f (f e e) m) m)) b)).
surgery id_r ((f (f (f e m) (f (f (f e e) m) m)) b)) ((f (f e (f (f (f e e) m) m)) b)).
surgery id_r ((f (f e (f (f (f e e) m) m)) b)) ((f (f e (f (f e e) m)) b)).
surgery id_l ((f (f e (f (f e e) m)) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_240: forall b: G, ((e <+> e) <+> ((((e <+> e) <+> (e <+> m)) <+> (e <+> e)) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f (f (f e e) (f e m)) (f e e)) (f e b)))) ((f e (f (f (f (f e e) (f e m)) (f e e)) (f e b)))).
surgery id_l ((f e (f (f (f (f e e) (f e m)) (f e e)) (f e b)))) ((f e (f (f (f e (f e m)) (f e e)) (f e b)))).
surgery id_l ((f e (f (f (f e (f e m)) (f e e)) (f e b)))) ((f e (f (f (f e m) (f e e)) (f e b)))).
surgery id_r ((f e (f (f (f e m) (f e e)) (f e b)))) ((f e (f (f e (f e e)) (f e b)))).
surgery id_l ((f e (f (f e (f e e)) (f e b)))) ((f e (f (f e e) (f e b)))).
surgery id_l ((f e (f (f e e) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_241: forall b: G, ((b <+> ((m <+> m) <+> (e <+> m))) <+> ((m <+> m) <+> (e <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f b (f (f m m) (f e m))) (f (f m m) (f e (f m m))))) ((f (f b (f m (f e m))) (f (f m m) (f e (f m m))))).
surgery id_l ((f (f b (f m (f e m))) (f (f m m) (f e (f m m))))) ((f (f b (f m m)) (f (f m m) (f e (f m m))))).
surgery id_r ((f (f b (f m m)) (f (f m m) (f e (f m m))))) ((f (f b m) (f (f m m) (f e (f m m))))).
surgery id_r ((f (f b m) (f (f m m) (f e (f m m))))) ((f b (f (f m m) (f e (f m m))))).
surgery id_r ((f b (f (f m m) (f e (f m m))))) ((f b (f m (f e (f m m))))).
surgery id_l ((f b (f m (f e (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_242: forall b: G, (((e <+> b) <+> m) <+> (m <+> ((m <+> (m <+> (e <+> m))) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e b) m) (f m (f (f m (f m (f e m))) (f m m))))) ((f (f e b) (f m (f (f m (f m (f e m))) (f m m))))).
surgery id_l ((f (f e b) (f m (f (f m (f m (f e m))) (f m m))))) ((f b (f m (f (f m (f m (f e m))) (f m m))))).
surgery id_l ((f b (f m (f (f m (f m (f e m))) (f m m))))) ((f b (f m (f (f m (f m m)) (f m m))))).
surgery id_r ((f b (f m (f (f m (f m m)) (f m m))))) ((f b (f m (f (f m m) (f m m))))).
surgery id_r ((f b (f m (f (f m m) (f m m))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_243: forall b: G, (((((e <+> e) <+> (e <+> m)) <+> ((e <+> (e <+> m)) <+> m)) <+> e) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f (f (f e e) (f e m)) (f (f e (f e m)) m)) e) b)) ((f (f (f (f e (f e m)) (f (f e (f e m)) m)) e) b)).
surgery id_l ((f (f (f (f e (f e m)) (f (f e (f e m)) m)) e) b)) ((f (f (f (f e m) (f (f e (f e m)) m)) e) b)).
surgery id_r ((f (f (f (f e m) (f (f e (f e m)) m)) e) b)) ((f (f (f e (f (f e (f e m)) m)) e) b)).
surgery id_l ((f (f (f e (f (f e (f e m)) m)) e) b)) ((f (f (f e (f (f e m) m)) e) b)).
surgery id_r ((f (f (f e (f (f e m) m)) e) b)) ((f (f (f e (f e m)) e) b)).
surgery id_l ((f (f (f e (f e m)) e) b)) ((f (f (f e m) e) b)).
surgery id_r ((f (f (f e m) e) b)) ((f (f e e) b)).
surgery id_l ((f (f e e) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_244: forall b: G, (((e <+> (m <+> m)) <+> e) <+> (((e <+> (e <+> (e <+> m))) <+> e) <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f m m)) e) (f (f (f e (f e (f e m))) e) b))) ((f (f (f e m) e) (f (f (f e (f e (f e m))) e) b))).
surgery id_r ((f (f (f e m) e) (f (f (f e (f e (f e m))) e) b))) ((f (f e e) (f (f (f e (f e (f e m))) e) b))).
surgery id_l ((f (f e e) (f (f (f e (f e (f e m))) e) b))) ((f e (f (f (f e (f e (f e m))) e) b))).
surgery id_l ((f e (f (f (f e (f e (f e m))) e) b))) ((f e (f (f (f e (f e m)) e) b))).
surgery id_l ((f e (f (f (f e (f e m)) e) b))) ((f e (f (f (f e m) e) b))).
surgery id_r ((f e (f (f (f e m) e) b))) ((f e (f (f e e) b))).
surgery id_l ((f e (f (f e e) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_245: forall b: G, ((b <+> ((e <+> m) <+> m)) <+> (((e <+> e) <+> (e <+> (m <+> m))) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f b (f (f e m) m)) (f (f (f e e) (f e (f m m))) m))) ((f (f b (f e m)) (f (f (f e e) (f e (f m m))) m))).
surgery id_l ((f (f b (f e m)) (f (f (f e e) (f e (f m m))) m))) ((f (f b m) (f (f (f e e) (f e (f m m))) m))).
surgery id_r ((f (f b m) (f (f (f e e) (f e (f m m))) m))) ((f b (f (f (f e e) (f e (f m m))) m))).
surgery id_l ((f b (f (f (f e e) (f e (f m m))) m))) ((f b (f (f e (f e (f m m))) m))).
surgery id_l ((f b (f (f e (f e (f m m))) m))) ((f b (f (f e (f m m)) m))).
surgery id_r ((f b (f (f e (f m m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_246: forall b: G, ((b <+> ((((e <+> m) <+> m) <+> ((e <+> e) <+> m)) <+> (e <+> m))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f b (f (f (f (f e m) m) (f (f e e) m)) (f e m))) m)) ((f b (f (f (f (f e m) m) (f (f e e) m)) (f e m)))).
surgery id_r ((f b (f (f (f (f e m) m) (f (f e e) m)) (f e m)))) ((f b (f (f (f e m) (f (f e e) m)) (f e m)))).
surgery id_r ((f b (f (f (f e m) (f (f e e) m)) (f e m)))) ((f b (f (f e (f (f e e) m)) (f e m)))).
surgery id_l ((f b (f (f e (f (f e e) m)) (f e m)))) ((f b (f (f e (f e m)) (f e m)))).
surgery id_l ((f b (f (f e (f e m)) (f e m)))) ((f b (f (f e m) (f e m)))).
surgery id_r ((f b (f (f e m) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_247: forall b: G, (((e <+> (e <+> e)) <+> (m <+> m)) <+> ((b <+> m) <+> (e <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e e)) (f m m)) (f (f b m) (f e (f m m))))) ((f (f (f e e) (f m m)) (f (f b m) (f e (f m m))))).
surgery id_l ((f (f (f e e) (f m m)) (f (f b m) (f e (f m m))))) ((f (f e (f m m)) (f (f b m) (f e (f m m))))).
surgery id_r ((f (f e (f m m)) (f (f b m) (f e (f m m))))) ((f (f e m) (f (f b m) (f e (f m m))))).
surgery id_r ((f (f e m) (f (f b m) (f e (f m m))))) ((f e (f (f b m) (f e (f m m))))).
surgery id_r ((f e (f (f b m) (f e (f m m))))) ((f e (f b (f e (f m m))))).
surgery id_l ((f e (f b (f e (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_248: forall b: G, (((e <+> ((e <+> m) <+> (e <+> e))) <+> m) <+> ((e <+> b) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f e m) (f e e))) m) (f (f e b) (f m m)))) ((f (f e (f (f e m) (f e e))) (f (f e b) (f m m)))).
surgery id_r ((f (f e (f (f e m) (f e e))) (f (f e b) (f m m)))) ((f (f e (f e (f e e))) (f (f e b) (f m m)))).
surgery id_l ((f (f e (f e (f e e))) (f (f e b) (f m m)))) ((f (f e (f e e)) (f (f e b) (f m m)))).
surgery id_l ((f (f e (f e e)) (f (f e b) (f m m)))) ((f (f e e) (f (f e b) (f m m)))).
surgery id_l ((f (f e e) (f (f e b) (f m m)))) ((f e (f (f e b) (f m m)))).
surgery id_l ((f e (f (f e b) (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_249: forall b: G, (((e <+> e) <+> e) <+> ((((e <+> m) <+> (m <+> m)) <+> m) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) e) (f (f (f (f e m) (f m m)) m) (f e b)))) ((f (f e e) (f (f (f (f e m) (f m m)) m) (f e b)))).
surgery id_l ((f (f e e) (f (f (f (f e m) (f m m)) m) (f e b)))) ((f e (f (f (f (f e m) (f m m)) m) (f e b)))).
surgery id_r ((f e (f (f (f (f e m) (f m m)) m) (f e b)))) ((f e (f (f (f e m) (f m m)) (f e b)))).
surgery id_r ((f e (f (f (f e m) (f m m)) (f e b)))) ((f e (f (f e (f m m)) (f e b)))).
surgery id_r ((f e (f (f e (f m m)) (f e b)))) ((f e (f (f e m) (f e b)))).
surgery id_r ((f e (f (f e m) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_250: forall b: G, (((e <+> b) <+> m) <+> (((e <+> (m <+> m)) <+> (e <+> e)) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e b) m) (f (f (f e (f m m)) (f e e)) (f m m)))) ((f (f e b) (f (f (f e (f m m)) (f e e)) (f m m)))).
surgery id_l ((f (f e b) (f (f (f e (f m m)) (f e e)) (f m m)))) ((f b (f (f (f e (f m m)) (f e e)) (f m m)))).
surgery id_r ((f b (f (f (f e (f m m)) (f e e)) (f m m)))) ((f b (f (f (f e m) (f e e)) (f m m)))).
surgery id_r ((f b (f (f (f e m) (f e e)) (f m m)))) ((f b (f (f e (f e e)) (f m m)))).
surgery id_l ((f b (f (f e (f e e)) (f m m)))) ((f b (f (f e e) (f m m)))).
surgery id_l ((f b (f (f e e) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_251: forall b: G, ((b <+> ((((e <+> e) <+> m) <+> m) <+> (m <+> (m <+> (m <+> m))))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f b (f (f (f (f e e) m) m) (f m (f m (f m m))))) m)) ((f b (f (f (f (f e e) m) m) (f m (f m (f m m)))))).
surgery id_r ((f b (f (f (f (f e e) m) m) (f m (f m (f m m)))))) ((f b (f (f (f e e) m) (f m (f m (f m m)))))).
surgery id_r ((f b (f (f (f e e) m) (f m (f m (f m m)))))) ((f b (f (f e e) (f m (f m (f m m)))))).
surgery id_l ((f b (f (f e e) (f m (f m (f m m)))))) ((f b (f e (f m (f m (f m m)))))).
surgery id_l ((f b (f e (f m (f m (f m m)))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_252: forall b: G, (b <+> (e <+> ((((e <+> m) <+> e) <+> m) <+> ((e <+> m) <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_l ((f b (f e (f (f (f (f e m) e) m) (f (f e m) (f e m)))))) ((f b (f (f (f (f e m) e) m) (f (f e m) (f e m))))).
surgery id_r ((f b (f (f (f (f e m) e) m) (f (f e m) (f e m))))) ((f b (f (f (f e m) e) (f (f e m) (f e m))))).
surgery id_r ((f b (f (f (f e m) e) (f (f e m) (f e m))))) ((f b (f (f e e) (f (f e m) (f e m))))).
surgery id_l ((f b (f (f e e) (f (f e m) (f e m))))) ((f b (f e (f (f e m) (f e m))))).
surgery id_l ((f b (f e (f (f e m) (f e m))))) ((f b (f (f e m) (f e m)))).
surgery id_r ((f b (f (f e m) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_253: forall b: G, ((e <+> b) <+> (((e <+> e) <+> ((e <+> e) <+> m)) <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f (f (f e e) (f (f e e) m)) (f e (f e m))))) ((f b (f (f (f e e) (f (f e e) m)) (f e (f e m))))).
surgery id_l ((f b (f (f (f e e) (f (f e e) m)) (f e (f e m))))) ((f b (f (f e (f (f e e) m)) (f e (f e m))))).
surgery id_l ((f b (f (f e (f (f e e) m)) (f e (f e m))))) ((f b (f (f e (f e m)) (f e (f e m))))).
surgery id_l ((f b (f (f e (f e m)) (f e (f e m))))) ((f b (f (f e m) (f e (f e m))))).
surgery id_r ((f b (f (f e m) (f e (f e m))))) ((f b (f e (f e (f e m))))).
surgery id_l ((f b (f e (f e (f e m))))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_254: forall b: G, ((((e <+> e) <+> m) <+> e) <+> (((b <+> m) <+> m) <+> ((e <+> e) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) e) (f (f (f b m) m) (f (f e e) m)))) ((f (f (f e e) e) (f (f (f b m) m) (f (f e e) m)))).
surgery id_l ((f (f (f e e) e) (f (f (f b m) m) (f (f e e) m)))) ((f (f e e) (f (f (f b m) m) (f (f e e) m)))).
surgery id_l ((f (f e e) (f (f (f b m) m) (f (f e e) m)))) ((f e (f (f (f b m) m) (f (f e e) m)))).
surgery id_r ((f e (f (f (f b m) m) (f (f e e) m)))) ((f e (f (f b m) (f (f e e) m)))).
surgery id_r ((f e (f (f b m) (f (f e e) m)))) ((f e (f b (f (f e e) m)))).
surgery id_l ((f e (f b (f (f e e) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_255: forall b: G, (((e <+> (e <+> e)) <+> ((e <+> b) <+> m)) <+> (e <+> (m <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e e)) (f (f e b) m)) (f e (f m (f m m))))) ((f (f (f e e) (f (f e b) m)) (f e (f m (f m m))))).
surgery id_l ((f (f (f e e) (f (f e b) m)) (f e (f m (f m m))))) ((f (f e (f (f e b) m)) (f e (f m (f m m))))).
surgery id_l ((f (f e (f (f e b) m)) (f e (f m (f m m))))) ((f (f e (f b m)) (f e (f m (f m m))))).
surgery id_r ((f (f e (f b m)) (f e (f m (f m m))))) ((f (f e b) (f e (f m (f m m))))).
surgery id_l ((f (f e b) (f e (f m (f m m))))) ((f b (f e (f m (f m m))))).
surgery id_l ((f b (f e (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_256: forall b: G, (((e <+> e) <+> ((e <+> m) <+> (e <+> b))) <+> ((e <+> (e <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f e m) (f e b))) (f (f e (f e m)) m))) ((f (f e (f (f e m) (f e b))) (f (f e (f e m)) m))).
surgery id_r ((f (f e (f (f e m) (f e b))) (f (f e (f e m)) m))) ((f (f e (f e (f e b))) (f (f e (f e m)) m))).
surgery id_l ((f (f e (f e (f e b))) (f (f e (f e m)) m))) ((f (f e (f e b)) (f (f e (f e m)) m))).
surgery id_l ((f (f e (f e b)) (f (f e (f e m)) m))) ((f (f e b) (f (f e (f e m)) m))).
surgery id_l ((f (f e b) (f (f e (f e m)) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_257: forall b: G, ((((e <+> e) <+> ((e <+> m) <+> m)) <+> ((b <+> m) <+> (e <+> m))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) (f (f e m) m)) (f (f b m) (f e m))) m)) ((f (f (f e e) (f (f e m) m)) (f (f b m) (f e m)))).
surgery id_l ((f (f (f e e) (f (f e m) m)) (f (f b m) (f e m)))) ((f (f e (f (f e m) m)) (f (f b m) (f e m)))).
surgery id_r ((f (f e (f (f e m) m)) (f (f b m) (f e m)))) ((f (f e (f e m)) (f (f b m) (f e m)))).
surgery id_l ((f (f e (f e m)) (f (f b m) (f e m)))) ((f (f e m) (f (f b m) (f e m)))).
surgery id_r ((f (f e m) (f (f b m) (f e m)))) ((f e (f (f b m) (f e m)))).
surgery id_r ((f e (f (f b m) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_258: forall b: G, ((((e <+> m) <+> (e <+> ((m <+> (e <+> (e <+> m))) <+> m))) <+> b) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f e (f (f m (f e (f e m))) m))) b) m)) ((f (f (f e m) (f e (f (f m (f e (f e m))) m))) b)).
surgery id_r ((f (f (f e m) (f e (f (f m (f e (f e m))) m))) b)) ((f (f e (f e (f (f m (f e (f e m))) m))) b)).
surgery id_l ((f (f e (f e (f (f m (f e (f e m))) m))) b)) ((f (f e (f (f m (f e (f e m))) m)) b)).
surgery id_l ((f (f e (f (f m (f e (f e m))) m)) b)) ((f (f e (f (f m (f e m)) m)) b)).
surgery id_l ((f (f e (f (f m (f e m)) m)) b)) ((f (f e (f (f m m) m)) b)).
surgery id_r ((f (f e (f (f m m) m)) b)) ((f (f e (f m m)) b)).
surgery id_r ((f (f e (f m m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_259: forall b: G, ((((e <+> m) <+> e) <+> (e <+> e)) <+> ((e <+> m) <+> ((e <+> m) <+> b))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) e) (f e e)) (f (f e m) (f (f e m) b)))) ((f (f (f e e) (f e e)) (f (f e m) (f (f e m) b)))).
surgery id_l ((f (f (f e e) (f e e)) (f (f e m) (f (f e m) b)))) ((f (f e (f e e)) (f (f e m) (f (f e m) b)))).
surgery id_l ((f (f e (f e e)) (f (f e m) (f (f e m) b)))) ((f (f e e) (f (f e m) (f (f e m) b)))).
surgery id_l ((f (f e e) (f (f e m) (f (f e m) b)))) ((f e (f (f e m) (f (f e m) b)))).
surgery id_r ((f e (f (f e m) (f (f e m) b)))) ((f e (f e (f (f e m) b)))).
surgery id_l ((f e (f e (f (f e m) b)))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_260: forall b: G, ((e <+> (e <+> e)) <+> (((((e <+> e) <+> m) <+> (e <+> m)) <+> b) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f e (f e e)) (f (f (f (f (f e e) m) (f e m)) b) m))) ((f (f e e) (f (f (f (f (f e e) m) (f e m)) b) m))).
surgery id_l ((f (f e e) (f (f (f (f (f e e) m) (f e m)) b) m))) ((f e (f (f (f (f (f e e) m) (f e m)) b) m))).
surgery id_r ((f e (f (f (f (f (f e e) m) (f e m)) b) m))) ((f e (f (f (f (f e e) (f e m)) b) m))).
surgery id_l ((f e (f (f (f (f e e) (f e m)) b) m))) ((f e (f (f (f e (f e m)) b) m))).
surgery id_l ((f e (f (f (f e (f e m)) b) m))) ((f e (f (f (f e m) b) m))).
surgery id_r ((f e (f (f (f e m) b) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_261: forall b: G, (((e <+> (e <+> e)) <+> ((e <+> m) <+> (e <+> (e <+> m)))) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e e)) (f (f e m) (f e (f e m)))) (f b m))) ((f (f (f e e) (f (f e m) (f e (f e m)))) (f b m))).
surgery id_l ((f (f (f e e) (f (f e m) (f e (f e m)))) (f b m))) ((f (f e (f (f e m) (f e (f e m)))) (f b m))).
surgery id_r ((f (f e (f (f e m) (f e (f e m)))) (f b m))) ((f (f e (f e (f e (f e m)))) (f b m))).
surgery id_l ((f (f e (f e (f e (f e m)))) (f b m))) ((f (f e (f e (f e m))) (f b m))).
surgery id_l ((f (f e (f e (f e m))) (f b m))) ((f (f e (f e m)) (f b m))).
surgery id_l ((f (f e (f e m)) (f b m))) ((f (f e m) (f b m))).
surgery id_r ((f (f e m) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_262: forall b: G, (b <+> ((e <+> ((e <+> (m <+> (e <+> m))) <+> (m <+> m))) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f b (f (f e (f (f e (f m (f e m))) (f m m))) (f m m)))) ((f b (f (f e (f (f e (f m m)) (f m m))) (f m m)))).
surgery id_r ((f b (f (f e (f (f e (f m m)) (f m m))) (f m m)))) ((f b (f (f e (f (f e m) (f m m))) (f m m)))).
surgery id_r ((f b (f (f e (f (f e m) (f m m))) (f m m)))) ((f b (f (f e (f e (f m m))) (f m m)))).
surgery id_l ((f b (f (f e (f e (f m m))) (f m m)))) ((f b (f (f e (f m m)) (f m m)))).
surgery id_r ((f b (f (f e (f m m)) (f m m)))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_263: forall b: G, (((e <+> e) <+> (b <+> (m <+> ((m <+> m) <+> m)))) <+> (e <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f b (f m (f (f m m) m)))) (f e (f m m)))) ((f (f e (f b (f m (f (f m m) m)))) (f e (f m m)))).
surgery id_r ((f (f e (f b (f m (f (f m m) m)))) (f e (f m m)))) ((f (f e (f b (f m (f m m)))) (f e (f m m)))).
surgery id_r ((f (f e (f b (f m (f m m)))) (f e (f m m)))) ((f (f e (f b (f m m))) (f e (f m m)))).
surgery id_r ((f (f e (f b (f m m))) (f e (f m m)))) ((f (f e (f b m)) (f e (f m m)))).
surgery id_r ((f (f e (f b m)) (f e (f m m)))) ((f (f e b) (f e (f m m)))).
surgery id_l ((f (f e b) (f e (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_264: forall b: G, ((e <+> m) <+> ((b <+> (e <+> m)) <+> ((e <+> (e <+> (m <+> m))) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f b (f e m)) (f (f e (f e (f m m))) m)))) ((f e (f (f b (f e m)) (f (f e (f e (f m m))) m)))).
surgery id_l ((f e (f (f b (f e m)) (f (f e (f e (f m m))) m)))) ((f e (f (f b m) (f (f e (f e (f m m))) m)))).
surgery id_r ((f e (f (f b m) (f (f e (f e (f m m))) m)))) ((f e (f b (f (f e (f e (f m m))) m)))).
surgery id_l ((f e (f b (f (f e (f e (f m m))) m)))) ((f e (f b (f (f e (f m m)) m)))).
surgery id_r ((f e (f b (f (f e (f m m)) m)))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_265: forall b: G, ((e <+> (((e <+> e) <+> e) <+> b)) <+> ((e <+> ((e <+> e) <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f (f e e) e) b)) (f (f e (f (f e e) m)) m))) ((f (f e (f (f e e) b)) (f (f e (f (f e e) m)) m))).
surgery id_l ((f (f e (f (f e e) b)) (f (f e (f (f e e) m)) m))) ((f (f e (f e b)) (f (f e (f (f e e) m)) m))).
surgery id_l ((f (f e (f e b)) (f (f e (f (f e e) m)) m))) ((f (f e b) (f (f e (f (f e e) m)) m))).
surgery id_l ((f (f e b) (f (f e (f (f e e) m)) m))) ((f b (f (f e (f (f e e) m)) m))).
surgery id_l ((f b (f (f e (f (f e e) m)) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_266: forall b: G, ((e <+> ((((e <+> e) <+> (e <+> m)) <+> (e <+> e)) <+> (e <+> m))) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f (f (f e e) (f e m)) (f e e)) (f e m))) b)) ((f (f e (f (f (f e (f e m)) (f e e)) (f e m))) b)).
surgery id_l ((f (f e (f (f (f e (f e m)) (f e e)) (f e m))) b)) ((f (f e (f (f (f e m) (f e e)) (f e m))) b)).
surgery id_r ((f (f e (f (f (f e m) (f e e)) (f e m))) b)) ((f (f e (f (f e (f e e)) (f e m))) b)).
surgery id_l ((f (f e (f (f e (f e e)) (f e m))) b)) ((f (f e (f (f e e) (f e m))) b)).
surgery id_l ((f (f e (f (f e e) (f e m))) b)) ((f (f e (f e (f e m))) b)).
surgery id_l ((f (f e (f e (f e m))) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_267: forall b: G, (((e <+> (e <+> ((e <+> m) <+> m))) <+> ((e <+> e) <+> (e <+> m))) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e (f (f e m) m))) (f (f e e) (f e m))) b)) ((f (f (f e (f (f e m) m)) (f (f e e) (f e m))) b)).
surgery id_r ((f (f (f e (f (f e m) m)) (f (f e e) (f e m))) b)) ((f (f (f e (f e m)) (f (f e e) (f e m))) b)).
surgery id_l ((f (f (f e (f e m)) (f (f e e) (f e m))) b)) ((f (f (f e m) (f (f e e) (f e m))) b)).
surgery id_r ((f (f (f e m) (f (f e e) (f e m))) b)) ((f (f e (f (f e e) (f e m))) b)).
surgery id_l ((f (f e (f (f e e) (f e m))) b)) ((f (f e (f e (f e m))) b)).
surgery id_l ((f (f e (f e (f e m))) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_268: forall b: G, ((b <+> (e <+> m)) <+> (((e <+> e) <+> e) <+> ((e <+> m) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f b (f e m)) (f (f (f e e) e) (f (f e m) (f e m))))) ((f (f b m) (f (f (f e e) e) (f (f e m) (f e m))))).
surgery id_r ((f (f b m) (f (f (f e e) e) (f (f e m) (f e m))))) ((f b (f (f (f e e) e) (f (f e m) (f e m))))).
surgery id_l ((f b (f (f (f e e) e) (f (f e m) (f e m))))) ((f b (f (f e e) (f (f e m) (f e m))))).
surgery id_l ((f b (f (f e e) (f (f e m) (f e m))))) ((f b (f e (f (f e m) (f e m))))).
surgery id_l ((f b (f e (f (f e m) (f e m))))) ((f b (f (f e m) (f e m)))).
surgery id_r ((f b (f (f e m) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_269: forall b: G, ((e <+> ((e <+> e) <+> (e <+> m))) <+> ((e <+> m) <+> ((e <+> e) <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f e e) (f e m))) (f (f e m) (f (f e e) b)))) ((f (f e (f e (f e m))) (f (f e m) (f (f e e) b)))).
surgery id_l ((f (f e (f e (f e m))) (f (f e m) (f (f e e) b)))) ((f (f e (f e m)) (f (f e m) (f (f e e) b)))).
surgery id_l ((f (f e (f e m)) (f (f e m) (f (f e e) b)))) ((f (f e m) (f (f e m) (f (f e e) b)))).
surgery id_r ((f (f e m) (f (f e m) (f (f e e) b)))) ((f e (f (f e m) (f (f e e) b)))).
surgery id_r ((f e (f (f e m) (f (f e e) b)))) ((f e (f e (f (f e e) b)))).
surgery id_l ((f e (f e (f (f e e) b)))) ((f e (f (f e e) b))).
surgery id_l ((f e (f (f e e) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_270: forall b: G, ((e <+> ((e <+> m) <+> (m <+> m))) <+> (((e <+> m) <+> b) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f e m) (f m m))) (f (f (f e m) b) (f m m)))) ((f (f e (f e (f m m))) (f (f (f e m) b) (f m m)))).
surgery id_l ((f (f e (f e (f m m))) (f (f (f e m) b) (f m m)))) ((f (f e (f m m)) (f (f (f e m) b) (f m m)))).
surgery id_r ((f (f e (f m m)) (f (f (f e m) b) (f m m)))) ((f (f e m) (f (f (f e m) b) (f m m)))).
surgery id_r ((f (f e m) (f (f (f e m) b) (f m m)))) ((f e (f (f (f e m) b) (f m m)))).
surgery id_r ((f e (f (f (f e m) b) (f m m)))) ((f e (f (f e b) (f m m)))).
surgery id_l ((f e (f (f e b) (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_271: forall b: G, (((e <+> b) <+> ((e <+> e) <+> (e <+> m))) <+> ((e <+> (m <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e b) (f (f e e) (f e m))) (f (f e (f m m)) m))) ((f (f b (f (f e e) (f e m))) (f (f e (f m m)) m))).
surgery id_l ((f (f b (f (f e e) (f e m))) (f (f e (f m m)) m))) ((f (f b (f e (f e m))) (f (f e (f m m)) m))).
surgery id_l ((f (f b (f e (f e m))) (f (f e (f m m)) m))) ((f (f b (f e m)) (f (f e (f m m)) m))).
surgery id_l ((f (f b (f e m)) (f (f e (f m m)) m))) ((f (f b m) (f (f e (f m m)) m))).
surgery id_r ((f (f b m) (f (f e (f m m)) m))) ((f b (f (f e (f m m)) m))).
surgery id_r ((f b (f (f e (f m m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_272: forall b: G, (((e <+> m) <+> (b <+> m)) <+> (e <+> (m <+> ((m <+> (m <+> m)) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f b m)) (f e (f m (f (f m (f m m)) m))))) ((f (f e (f b m)) (f e (f m (f (f m (f m m)) m))))).
surgery id_r ((f (f e (f b m)) (f e (f m (f (f m (f m m)) m))))) ((f (f e b) (f e (f m (f (f m (f m m)) m))))).
surgery id_l ((f (f e b) (f e (f m (f (f m (f m m)) m))))) ((f b (f e (f m (f (f m (f m m)) m))))).
surgery id_l ((f b (f e (f m (f (f m (f m m)) m))))) ((f b (f m (f (f m (f m m)) m)))).
surgery id_r ((f b (f m (f (f m (f m m)) m)))) ((f b (f m (f (f m m) m)))).
surgery id_r ((f b (f m (f (f m m) m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_273: forall b: G, ((((e <+> e) <+> (e <+> (e <+> m))) <+> (e <+> m)) <+> ((b <+> m) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) (f e (f e m))) (f e m)) (f (f b m) m))) ((f (f (f e (f e (f e m))) (f e m)) (f (f b m) m))).
surgery id_l ((f (f (f e (f e (f e m))) (f e m)) (f (f b m) m))) ((f (f (f e (f e m)) (f e m)) (f (f b m) m))).
surgery id_l ((f (f (f e (f e m)) (f e m)) (f (f b m) m))) ((f (f (f e m) (f e m)) (f (f b m) m))).
surgery id_r ((f (f (f e m) (f e m)) (f (f b m) m))) ((f (f e (f e m)) (f (f b m) m))).
surgery id_l ((f (f e (f e m)) (f (f b m) m))) ((f (f e m) (f (f b m) m))).
surgery id_r ((f (f e m) (f (f b m) m))) ((f e (f (f b m) m))).
surgery id_r ((f e (f (f b m) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_274: forall b: G, (((e <+> m) <+> (e <+> m)) <+> ((b <+> m) <+> ((m <+> m) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f e m)) (f (f b m) (f (f m m) (f m m))))) ((f (f e (f e m)) (f (f b m) (f (f m m) (f m m))))).
surgery id_l ((f (f e (f e m)) (f (f b m) (f (f m m) (f m m))))) ((f (f e m) (f (f b m) (f (f m m) (f m m))))).
surgery id_r ((f (f e m) (f (f b m) (f (f m m) (f m m))))) ((f e (f (f b m) (f (f m m) (f m m))))).
surgery id_r ((f e (f (f b m) (f (f m m) (f m m))))) ((f e (f b (f (f m m) (f m m))))).
surgery id_r ((f e (f b (f (f m m) (f m m))))) ((f e (f b (f m (f m m))))).
surgery id_r ((f e (f b (f m (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_275: forall b: G, ((((e <+> e) <+> m) <+> m) <+> (((e <+> (e <+> m)) <+> (e <+> m)) <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) m) (f (f (f e (f e m)) (f e m)) b))) ((f (f (f e e) m) (f (f (f e (f e m)) (f e m)) b))).
surgery id_r ((f (f (f e e) m) (f (f (f e (f e m)) (f e m)) b))) ((f (f e e) (f (f (f e (f e m)) (f e m)) b))).
surgery id_l ((f (f e e) (f (f (f e (f e m)) (f e m)) b))) ((f e (f (f (f e (f e m)) (f e m)) b))).
surgery id_l ((f e (f (f (f e (f e m)) (f e m)) b))) ((f e (f (f (f e m) (f e m)) b))).
surgery id_r ((f e (f (f (f e m) (f e m)) b))) ((f e (f (f e (f e m)) b))).
surgery id_l ((f e (f (f e (f e m)) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_276: forall b: G, (((e <+> m) <+> (m <+> ((e <+> e) <+> (m <+> (m <+> m))))) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f m (f (f e e) (f m (f m m))))) (f e b))) ((f (f e (f m (f (f e e) (f m (f m m))))) (f e b))).
surgery id_l ((f (f e (f m (f (f e e) (f m (f m m))))) (f e b))) ((f (f e (f m (f e (f m (f m m))))) (f e b))).
surgery id_l ((f (f e (f m (f e (f m (f m m))))) (f e b))) ((f (f e (f m (f m (f m m)))) (f e b))).
surgery id_r ((f (f e (f m (f m (f m m)))) (f e b))) ((f (f e (f m (f m m))) (f e b))).
surgery id_r ((f (f e (f m (f m m))) (f e b))) ((f (f e (f m m)) (f e b))).
surgery id_r ((f (f e (f m m)) (f e b))) ((f (f e m) (f e b))).
surgery id_r ((f (f e m) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_277: forall b: G, (((e <+> e) <+> e) <+> (((b <+> m) <+> (m <+> (e <+> m))) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) e) (f (f (f b m) (f m (f e m))) (f e m)))) ((f (f e e) (f (f (f b m) (f m (f e m))) (f e m)))).
surgery id_l ((f (f e e) (f (f (f b m) (f m (f e m))) (f e m)))) ((f e (f (f (f b m) (f m (f e m))) (f e m)))).
surgery id_r ((f e (f (f (f b m) (f m (f e m))) (f e m)))) ((f e (f (f b (f m (f e m))) (f e m)))).
surgery id_l ((f e (f (f b (f m (f e m))) (f e m)))) ((f e (f (f b (f m m)) (f e m)))).
surgery id_r ((f e (f (f b (f m m)) (f e m)))) ((f e (f (f b m) (f e m)))).
surgery id_r ((f e (f (f b m) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_278: forall b: G, (((b <+> m) <+> ((e <+> ((e <+> m) <+> e)) <+> m)) <+> ((e <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f (f e (f (f e m) e)) m)) (f (f e m) m))) ((f (f b (f (f e (f (f e m) e)) m)) (f (f e m) m))).
surgery id_r ((f (f b (f (f e (f (f e m) e)) m)) (f (f e m) m))) ((f (f b (f (f e (f e e)) m)) (f (f e m) m))).
surgery id_l ((f (f b (f (f e (f e e)) m)) (f (f e m) m))) ((f (f b (f (f e e) m)) (f (f e m) m))).
surgery id_l ((f (f b (f (f e e) m)) (f (f e m) m))) ((f (f b (f e m)) (f (f e m) m))).
surgery id_l ((f (f b (f e m)) (f (f e m) m))) ((f (f b m) (f (f e m) m))).
surgery id_r ((f (f b m) (f (f e m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_279: forall b: G, ((e <+> m) <+> (((e <+> e) <+> (b <+> m)) <+> ((m <+> m) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f (f e e) (f b m)) (f (f m m) (f e m))))) ((f e (f (f (f e e) (f b m)) (f (f m m) (f e m))))).
surgery id_l ((f e (f (f (f e e) (f b m)) (f (f m m) (f e m))))) ((f e (f (f e (f b m)) (f (f m m) (f e m))))).
surgery id_r ((f e (f (f e (f b m)) (f (f m m) (f e m))))) ((f e (f (f e b) (f (f m m) (f e m))))).
surgery id_l ((f e (f (f e b) (f (f m m) (f e m))))) ((f e (f b (f (f m m) (f e m))))).
surgery id_r ((f e (f b (f (f m m) (f e m))))) ((f e (f b (f m (f e m))))).
surgery id_l ((f e (f b (f m (f e m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_280: forall b: G, (((e <+> b) <+> (((e <+> m) <+> (e <+> m)) <+> (m <+> m))) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e b) (f (f (f e m) (f e m)) (f m m))) (f e m))) ((f (f b (f (f (f e m) (f e m)) (f m m))) (f e m))).
surgery id_r ((f (f b (f (f (f e m) (f e m)) (f m m))) (f e m))) ((f (f b (f (f e (f e m)) (f m m))) (f e m))).
surgery id_l ((f (f b (f (f e (f e m)) (f m m))) (f e m))) ((f (f b (f (f e m) (f m m))) (f e m))).
surgery id_r ((f (f b (f (f e m) (f m m))) (f e m))) ((f (f b (f e (f m m))) (f e m))).
surgery id_l ((f (f b (f e (f m m))) (f e m))) ((f (f b (f m m)) (f e m))).
surgery id_r ((f (f b (f m m)) (f e m))) ((f (f b m) (f e m))).
surgery id_r ((f (f b m) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_281: forall b: G, ((e <+> (e <+> e)) <+> (((b <+> ((m <+> m) <+> m)) <+> m) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e e)) (f (f (f b (f (f m m) m)) m) (f e m)))) ((f (f e e) (f (f (f b (f (f m m) m)) m) (f e m)))).
surgery id_l ((f (f e e) (f (f (f b (f (f m m) m)) m) (f e m)))) ((f e (f (f (f b (f (f m m) m)) m) (f e m)))).
surgery id_r ((f e (f (f (f b (f (f m m) m)) m) (f e m)))) ((f e (f (f b (f (f m m) m)) (f e m)))).
surgery id_r ((f e (f (f b (f (f m m) m)) (f e m)))) ((f e (f (f b (f m m)) (f e m)))).
surgery id_r ((f e (f (f b (f m m)) (f e m)))) ((f e (f (f b m) (f e m)))).
surgery id_r ((f e (f (f b m) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_282: forall b: G, ((e <+> ((e <+> e) <+> m)) <+> (b <+> (e <+> (m <+> (m <+> (e <+> m)))))) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f e e) m)) (f b (f e (f m (f m (f e m))))))) ((f (f e (f e m)) (f b (f e (f m (f m (f e m))))))).
surgery id_l ((f (f e (f e m)) (f b (f e (f m (f m (f e m))))))) ((f (f e m) (f b (f e (f m (f m (f e m))))))).
surgery id_r ((f (f e m) (f b (f e (f m (f m (f e m))))))) ((f e (f b (f e (f m (f m (f e m))))))).
surgery id_l ((f e (f b (f e (f m (f m (f e m))))))) ((f e (f b (f m (f m (f e m)))))).
surgery id_l ((f e (f b (f m (f m (f e m)))))) ((f e (f b (f m (f m m))))).
surgery id_r ((f e (f b (f m (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_283: forall b: G, ((((((e <+> e) <+> m) <+> e) <+> m) <+> m) <+> ((e <+> (e <+> m)) <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f (f e e) m) e) m) m) (f (f e (f e m)) b))) ((f (f (f (f (f e e) m) e) m) (f (f e (f e m)) b))).
surgery id_r ((f (f (f (f (f e e) m) e) m) (f (f e (f e m)) b))) ((f (f (f (f e e) m) e) (f (f e (f e m)) b))).
surgery id_r ((f (f (f (f e e) m) e) (f (f e (f e m)) b))) ((f (f (f e e) e) (f (f e (f e m)) b))).
surgery id_l ((f (f (f e e) e) (f (f e (f e m)) b))) ((f (f e e) (f (f e (f e m)) b))).
surgery id_l ((f (f e e) (f (f e (f e m)) b))) ((f e (f (f e (f e m)) b))).
surgery id_l ((f e (f (f e (f e m)) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_284: forall b: G, ((e <+> (b <+> (e <+> m))) <+> ((e <+> e) <+> (((m <+> m) <+> m) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f b (f e m))) (f (f e e) (f (f (f m m) m) m)))) ((f (f e (f b m)) (f (f e e) (f (f (f m m) m) m)))).
surgery id_r ((f (f e (f b m)) (f (f e e) (f (f (f m m) m) m)))) ((f (f e b) (f (f e e) (f (f (f m m) m) m)))).
surgery id_l ((f (f e b) (f (f e e) (f (f (f m m) m) m)))) ((f b (f (f e e) (f (f (f m m) m) m)))).
surgery id_l ((f b (f (f e e) (f (f (f m m) m) m)))) ((f b (f e (f (f (f m m) m) m)))).
surgery id_l ((f b (f e (f (f (f m m) m) m)))) ((f b (f (f (f m m) m) m))).
surgery id_r ((f b (f (f (f m m) m) m))) ((f b (f (f m m) m))).
surgery id_r ((f b (f (f m m) m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_285: forall b: G, (((e <+> m) <+> (e <+> (e <+> m))) <+> ((((e <+> b) <+> m) <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f e (f e m))) (f (f (f (f e b) m) m) m))) ((f (f e (f e (f e m))) (f (f (f (f e b) m) m) m))).
surgery id_l ((f (f e (f e (f e m))) (f (f (f (f e b) m) m) m))) ((f (f e (f e m)) (f (f (f (f e b) m) m) m))).
surgery id_l ((f (f e (f e m)) (f (f (f (f e b) m) m) m))) ((f (f e m) (f (f (f (f e b) m) m) m))).
surgery id_r ((f (f e m) (f (f (f (f e b) m) m) m))) ((f e (f (f (f (f e b) m) m) m))).
surgery id_r ((f e (f (f (f (f e b) m) m) m))) ((f e (f (f (f e b) m) m))).
surgery id_r ((f e (f (f (f e b) m) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_286: forall b: G, ((e <+> (e <+> e)) <+> (((b <+> m) <+> m) <+> ((m <+> (e <+> m)) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e e)) (f (f (f b m) m) (f (f m (f e m)) m)))) ((f (f e e) (f (f (f b m) m) (f (f m (f e m)) m)))).
surgery id_l ((f (f e e) (f (f (f b m) m) (f (f m (f e m)) m)))) ((f e (f (f (f b m) m) (f (f m (f e m)) m)))).
surgery id_r ((f e (f (f (f b m) m) (f (f m (f e m)) m)))) ((f e (f (f b m) (f (f m (f e m)) m)))).
surgery id_r ((f e (f (f b m) (f (f m (f e m)) m)))) ((f e (f b (f (f m (f e m)) m)))).
surgery id_l ((f e (f b (f (f m (f e m)) m)))) ((f e (f b (f (f m m) m)))).
surgery id_r ((f e (f b (f (f m m) m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_287: forall b: G, (((e <+> b) <+> ((e <+> m) <+> m)) <+> (m <+> (((e <+> m) <+> m) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e b) (f (f e m) m)) (f m (f (f (f e m) m) m)))) ((f (f b (f (f e m) m)) (f m (f (f (f e m) m) m)))).
surgery id_r ((f (f b (f (f e m) m)) (f m (f (f (f e m) m) m)))) ((f (f b (f e m)) (f m (f (f (f e m) m) m)))).
surgery id_l ((f (f b (f e m)) (f m (f (f (f e m) m) m)))) ((f (f b m) (f m (f (f (f e m) m) m)))).
surgery id_r ((f (f b m) (f m (f (f (f e m) m) m)))) ((f b (f m (f (f (f e m) m) m)))).
surgery id_r ((f b (f m (f (f (f e m) m) m)))) ((f b (f m (f (f e m) m)))).
surgery id_r ((f b (f m (f (f e m) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_288: forall b: G, (((e <+> (e <+> m)) <+> (e <+> b)) <+> ((m <+> (e <+> m)) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f e b)) (f (f m (f e m)) (f e m)))) ((f (f (f e m) (f e b)) (f (f m (f e m)) (f e m)))).
surgery id_r ((f (f (f e m) (f e b)) (f (f m (f e m)) (f e m)))) ((f (f e (f e b)) (f (f m (f e m)) (f e m)))).
surgery id_l ((f (f e (f e b)) (f (f m (f e m)) (f e m)))) ((f (f e b) (f (f m (f e m)) (f e m)))).
surgery id_l ((f (f e b) (f (f m (f e m)) (f e m)))) ((f b (f (f m (f e m)) (f e m)))).
surgery id_l ((f b (f (f m (f e m)) (f e m)))) ((f b (f (f m m) (f e m)))).
surgery id_r ((f b (f (f m m) (f e m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_289: forall b: G, (((b <+> m) <+> (e <+> m)) <+> ((e <+> m) <+> (m <+> ((m <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f e m)) (f (f e m) (f m (f (f m m) m))))) ((f (f b (f e m)) (f (f e m) (f m (f (f m m) m))))).
surgery id_l ((f (f b (f e m)) (f (f e m) (f m (f (f m m) m))))) ((f (f b m) (f (f e m) (f m (f (f m m) m))))).
surgery id_r ((f (f b m) (f (f e m) (f m (f (f m m) m))))) ((f b (f (f e m) (f m (f (f m m) m))))).
surgery id_r ((f b (f (f e m) (f m (f (f m m) m))))) ((f b (f e (f m (f (f m m) m))))).
surgery id_l ((f b (f e (f m (f (f m m) m))))) ((f b (f m (f (f m m) m)))).
surgery id_r ((f b (f m (f (f m m) m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_290: forall b: G, (((e <+> b) <+> (e <+> (e <+> m))) <+> (e <+> (e <+> (e <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_l ((f (f (f e b) (f e (f e m))) (f e (f e (f e (f e m)))))) ((f (f b (f e (f e m))) (f e (f e (f e (f e m)))))).
surgery id_l ((f (f b (f e (f e m))) (f e (f e (f e (f e m)))))) ((f (f b (f e m)) (f e (f e (f e (f e m)))))).
surgery id_l ((f (f b (f e m)) (f e (f e (f e (f e m)))))) ((f (f b m) (f e (f e (f e (f e m)))))).
surgery id_r ((f (f b m) (f e (f e (f e (f e m)))))) ((f b (f e (f e (f e (f e m)))))).
surgery id_l ((f b (f e (f e (f e (f e m)))))) ((f b (f e (f e (f e m))))).
surgery id_l ((f b (f e (f e (f e m))))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_291: forall b: G, (((e <+> ((e <+> m) <+> ((e <+> e) <+> m))) <+> (e <+> m)) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f e m) (f (f e e) m))) (f e m)) (f e b))) ((f (f (f e (f e (f (f e e) m))) (f e m)) (f e b))).
surgery id_l ((f (f (f e (f e (f (f e e) m))) (f e m)) (f e b))) ((f (f (f e (f (f e e) m)) (f e m)) (f e b))).
surgery id_l ((f (f (f e (f (f e e) m)) (f e m)) (f e b))) ((f (f (f e (f e m)) (f e m)) (f e b))).
surgery id_l ((f (f (f e (f e m)) (f e m)) (f e b))) ((f (f (f e m) (f e m)) (f e b))).
surgery id_r ((f (f (f e m) (f e m)) (f e b))) ((f (f e (f e m)) (f e b))).
surgery id_l ((f (f e (f e m)) (f e b))) ((f (f e m) (f e b))).
surgery id_r ((f (f e m) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_292: forall b: G, ((b <+> m) <+> ((e <+> (m <+> m)) <+> ((m <+> (e <+> m)) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f e (f m m)) (f (f m (f e m)) (f m m))))) ((f b (f (f e (f m m)) (f (f m (f e m)) (f m m))))).
surgery id_r ((f b (f (f e (f m m)) (f (f m (f e m)) (f m m))))) ((f b (f (f e m) (f (f m (f e m)) (f m m))))).
surgery id_r ((f b (f (f e m) (f (f m (f e m)) (f m m))))) ((f b (f e (f (f m (f e m)) (f m m))))).
surgery id_l ((f b (f e (f (f m (f e m)) (f m m))))) ((f b (f (f m (f e m)) (f m m)))).
surgery id_l ((f b (f (f m (f e m)) (f m m)))) ((f b (f (f m m) (f m m)))).
surgery id_r ((f b (f (f m m) (f m m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_293: forall b: G, ((((e <+> e) <+> m) <+> (e <+> (e <+> (e <+> e)))) <+> ((e <+> b) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) (f e (f e (f e e)))) (f (f e b) m))) ((f (f (f e e) (f e (f e (f e e)))) (f (f e b) m))).
surgery id_l ((f (f (f e e) (f e (f e (f e e)))) (f (f e b) m))) ((f (f e (f e (f e (f e e)))) (f (f e b) m))).
surgery id_l ((f (f e (f e (f e (f e e)))) (f (f e b) m))) ((f (f e (f e (f e e))) (f (f e b) m))).
surgery id_l ((f (f e (f e (f e e))) (f (f e b) m))) ((f (f e (f e e)) (f (f e b) m))).
surgery id_l ((f (f e (f e e)) (f (f e b) m))) ((f (f e e) (f (f e b) m))).
surgery id_l ((f (f e e) (f (f e b) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_294: forall b: G, ((((e <+> b) <+> (e <+> m)) <+> (e <+> m)) <+> ((e <+> (m <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e b) (f e m)) (f e m)) (f (f e (f m m)) m))) ((f (f (f b (f e m)) (f e m)) (f (f e (f m m)) m))).
surgery id_l ((f (f (f b (f e m)) (f e m)) (f (f e (f m m)) m))) ((f (f (f b m) (f e m)) (f (f e (f m m)) m))).
surgery id_r ((f (f (f b m) (f e m)) (f (f e (f m m)) m))) ((f (f b (f e m)) (f (f e (f m m)) m))).
surgery id_l ((f (f b (f e m)) (f (f e (f m m)) m))) ((f (f b m) (f (f e (f m m)) m))).
surgery id_r ((f (f b m) (f (f e (f m m)) m))) ((f b (f (f e (f m m)) m))).
surgery id_r ((f b (f (f e (f m m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_295: forall b: G, (((((e <+> e) <+> m) <+> (e <+> m)) <+> (((m <+> m) <+> m) <+> m)) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e e) m) (f e m)) (f (f (f m m) m) m)) b)) ((f (f (f (f e e) (f e m)) (f (f (f m m) m) m)) b)).
surgery id_l ((f (f (f (f e e) (f e m)) (f (f (f m m) m) m)) b)) ((f (f (f e (f e m)) (f (f (f m m) m) m)) b)).
surgery id_l ((f (f (f e (f e m)) (f (f (f m m) m) m)) b)) ((f (f (f e m) (f (f (f m m) m) m)) b)).
surgery id_r ((f (f (f e m) (f (f (f m m) m) m)) b)) ((f (f e (f (f (f m m) m) m)) b)).
surgery id_r ((f (f e (f (f (f m m) m) m)) b)) ((f (f e (f (f m m) m)) b)).
surgery id_r ((f (f e (f (f m m) m)) b)) ((f (f e (f m m)) b)).
surgery id_r ((f (f e (f m m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_296: forall b: G, (((e <+> m) <+> e) <+> ((e <+> (e <+> e)) <+> ((e <+> b) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) e) (f (f e (f e e)) (f (f e b) (f e m))))) ((f (f e e) (f (f e (f e e)) (f (f e b) (f e m))))).
surgery id_l ((f (f e e) (f (f e (f e e)) (f (f e b) (f e m))))) ((f e (f (f e (f e e)) (f (f e b) (f e m))))).
surgery id_l ((f e (f (f e (f e e)) (f (f e b) (f e m))))) ((f e (f (f e e) (f (f e b) (f e m))))).
surgery id_l ((f e (f (f e e) (f (f e b) (f e m))))) ((f e (f e (f (f e b) (f e m))))).
surgery id_l ((f e (f e (f (f e b) (f e m))))) ((f e (f (f e b) (f e m)))).
surgery id_l ((f e (f (f e b) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_297: forall b: G, ((e <+> ((e <+> e) <+> b)) <+> (((e <+> e) <+> e) <+> (m <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f e e) b)) (f (f (f e e) e) (f m (f e m))))) ((f (f e (f e b)) (f (f (f e e) e) (f m (f e m))))).
surgery id_l ((f (f e (f e b)) (f (f (f e e) e) (f m (f e m))))) ((f (f e b) (f (f (f e e) e) (f m (f e m))))).
surgery id_l ((f (f e b) (f (f (f e e) e) (f m (f e m))))) ((f b (f (f (f e e) e) (f m (f e m))))).
surgery id_l ((f b (f (f (f e e) e) (f m (f e m))))) ((f b (f (f e e) (f m (f e m))))).
surgery id_l ((f b (f (f e e) (f m (f e m))))) ((f b (f e (f m (f e m))))).
surgery id_l ((f b (f e (f m (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_298: forall b: G, ((e <+> b) <+> (((m <+> (e <+> m)) <+> m) <+> (m <+> (m <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f (f (f m (f e m)) m) (f m (f m (f e m)))))) ((f b (f (f (f m (f e m)) m) (f m (f m (f e m)))))).
surgery id_r ((f b (f (f (f m (f e m)) m) (f m (f m (f e m)))))) ((f b (f (f m (f e m)) (f m (f m (f e m)))))).
surgery id_l ((f b (f (f m (f e m)) (f m (f m (f e m)))))) ((f b (f (f m m) (f m (f m (f e m)))))).
surgery id_r ((f b (f (f m m) (f m (f m (f e m)))))) ((f b (f m (f m (f m (f e m)))))).
surgery id_l ((f b (f m (f m (f m (f e m)))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_299: forall b: G, (((e <+> ((e <+> (e <+> e)) <+> m)) <+> (e <+> m)) <+> (e <+> (b <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f (f e (f e e)) m)) (f e m)) (f e (f b m)))) ((f (f (f e (f (f e e) m)) (f e m)) (f e (f b m)))).
surgery id_l ((f (f (f e (f (f e e) m)) (f e m)) (f e (f b m)))) ((f (f (f e (f e m)) (f e m)) (f e (f b m)))).
surgery id_l ((f (f (f e (f e m)) (f e m)) (f e (f b m)))) ((f (f (f e m) (f e m)) (f e (f b m)))).
surgery id_r ((f (f (f e m) (f e m)) (f e (f b m)))) ((f (f e (f e m)) (f e (f b m)))).
surgery id_l ((f (f e (f e m)) (f e (f b m)))) ((f (f e m) (f e (f b m)))).
surgery id_r ((f (f e m) (f e (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_300: forall b: G, (b <+> ((e <+> m) <+> (((e <+> (m <+> m)) <+> m) <+> (e <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_r ((f b (f (f e m) (f (f (f e (f m m)) m) (f e (f e m)))))) ((f b (f e (f (f (f e (f m m)) m) (f e (f e m)))))).
surgery id_l ((f b (f e (f (f (f e (f m m)) m) (f e (f e m)))))) ((f b (f (f (f e (f m m)) m) (f e (f e m))))).
surgery id_r ((f b (f (f (f e (f m m)) m) (f e (f e m))))) ((f b (f (f e (f m m)) (f e (f e m))))).
surgery id_r ((f b (f (f e (f m m)) (f e (f e m))))) ((f b (f (f e m) (f e (f e m))))).
surgery id_r ((f b (f (f e m) (f e (f e m))))) ((f b (f e (f e (f e m))))).
surgery id_l ((f b (f e (f e (f e m))))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_301: forall b: G, ((((e <+> e) <+> e) <+> ((e <+> m) <+> m)) <+> (e <+> (e <+> (b <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) e) (f (f e m) m)) (f e (f e (f b m))))) ((f (f (f e e) (f (f e m) m)) (f e (f e (f b m))))).
surgery id_l ((f (f (f e e) (f (f e m) m)) (f e (f e (f b m))))) ((f (f e (f (f e m) m)) (f e (f e (f b m))))).
surgery id_r ((f (f e (f (f e m) m)) (f e (f e (f b m))))) ((f (f e (f e m)) (f e (f e (f b m))))).
surgery id_l ((f (f e (f e m)) (f e (f e (f b m))))) ((f (f e m) (f e (f e (f b m))))).
surgery id_r ((f (f e m) (f e (f e (f b m))))) ((f e (f e (f e (f b m))))).
surgery id_l ((f e (f e (f e (f b m))))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_302: forall b: G, ((e <+> (((e <+> e) <+> (e <+> m)) <+> (e <+> (e <+> m)))) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f (f e e) (f e m)) (f e (f e m)))) (f e b))) ((f (f e (f (f e (f e m)) (f e (f e m)))) (f e b))).
surgery id_l ((f (f e (f (f e (f e m)) (f e (f e m)))) (f e b))) ((f (f e (f (f e m) (f e (f e m)))) (f e b))).
surgery id_r ((f (f e (f (f e m) (f e (f e m)))) (f e b))) ((f (f e (f e (f e (f e m)))) (f e b))).
surgery id_l ((f (f e (f e (f e (f e m)))) (f e b))) ((f (f e (f e (f e m))) (f e b))).
surgery id_l ((f (f e (f e (f e m))) (f e b))) ((f (f e (f e m)) (f e b))).
surgery id_l ((f (f e (f e m)) (f e b))) ((f (f e m) (f e b))).
surgery id_r ((f (f e m) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_303: forall b: G, (((e <+> m) <+> (e <+> e)) <+> (e <+> ((b <+> m) <+> (e <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f e e)) (f e (f (f b m) (f e (f e m)))))) ((f (f e (f e e)) (f e (f (f b m) (f e (f e m)))))).
surgery id_l ((f (f e (f e e)) (f e (f (f b m) (f e (f e m)))))) ((f (f e e) (f e (f (f b m) (f e (f e m)))))).
surgery id_l ((f (f e e) (f e (f (f b m) (f e (f e m)))))) ((f e (f e (f (f b m) (f e (f e m)))))).
surgery id_l ((f e (f e (f (f b m) (f e (f e m)))))) ((f e (f (f b m) (f e (f e m))))).
surgery id_r ((f e (f (f b m) (f e (f e m))))) ((f e (f b (f e (f e m))))).
surgery id_l ((f e (f b (f e (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_304: forall b: G, ((e <+> (e <+> ((e <+> m) <+> m))) <+> (((e <+> m) <+> e) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e (f (f e m) m))) (f (f (f e m) e) (f e b)))) ((f (f e (f (f e m) m)) (f (f (f e m) e) (f e b)))).
surgery id_r ((f (f e (f (f e m) m)) (f (f (f e m) e) (f e b)))) ((f (f e (f e m)) (f (f (f e m) e) (f e b)))).
surgery id_l ((f (f e (f e m)) (f (f (f e m) e) (f e b)))) ((f (f e m) (f (f (f e m) e) (f e b)))).
surgery id_r ((f (f e m) (f (f (f e m) e) (f e b)))) ((f e (f (f (f e m) e) (f e b)))).
surgery id_r ((f e (f (f (f e m) e) (f e b)))) ((f e (f (f e e) (f e b)))).
surgery id_l ((f e (f (f e e) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_305: forall b: G, ((e <+> (((b <+> m) <+> ((e <+> e) <+> m)) <+> m)) <+> (e <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f (f b m) (f (f e e) m)) m)) (f e (f m m)))) ((f (f e (f (f b (f (f e e) m)) m)) (f e (f m m)))).
surgery id_l ((f (f e (f (f b (f (f e e) m)) m)) (f e (f m m)))) ((f (f e (f (f b (f e m)) m)) (f e (f m m)))).
surgery id_l ((f (f e (f (f b (f e m)) m)) (f e (f m m)))) ((f (f e (f (f b m) m)) (f e (f m m)))).
surgery id_r ((f (f e (f (f b m) m)) (f e (f m m)))) ((f (f e (f b m)) (f e (f m m)))).
surgery id_r ((f (f e (f b m)) (f e (f m m)))) ((f (f e b) (f e (f m m)))).
surgery id_l ((f (f e b) (f e (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_306: forall b: G, (((b <+> m) <+> (m <+> (e <+> (e <+> m)))) <+> (((e <+> m) <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f m (f e (f e m)))) (f (f (f e m) m) m))) ((f (f b (f m (f e (f e m)))) (f (f (f e m) m) m))).
surgery id_l ((f (f b (f m (f e (f e m)))) (f (f (f e m) m) m))) ((f (f b (f m (f e m))) (f (f (f e m) m) m))).
surgery id_l ((f (f b (f m (f e m))) (f (f (f e m) m) m))) ((f (f b (f m m)) (f (f (f e m) m) m))).
surgery id_r ((f (f b (f m m)) (f (f (f e m) m) m))) ((f (f b m) (f (f (f e m) m) m))).
surgery id_r ((f (f b m) (f (f (f e m) m) m))) ((f b (f (f (f e m) m) m))).
surgery id_r ((f b (f (f (f e m) m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_307: forall b: G, (b <+> (((e <+> e) <+> (e <+> e)) <+> ((e <+> (e <+> (e <+> m))) <+> m))) = b.
Proof.
intros.
surgery id_l ((f b (f (f (f e e) (f e e)) (f (f e (f e (f e m))) m)))) ((f b (f (f e (f e e)) (f (f e (f e (f e m))) m)))).
surgery id_l ((f b (f (f e (f e e)) (f (f e (f e (f e m))) m)))) ((f b (f (f e e) (f (f e (f e (f e m))) m)))).
surgery id_l ((f b (f (f e e) (f (f e (f e (f e m))) m)))) ((f b (f e (f (f e (f e (f e m))) m)))).
surgery id_l ((f b (f e (f (f e (f e (f e m))) m)))) ((f b (f (f e (f e (f e m))) m))).
surgery id_l ((f b (f (f e (f e (f e m))) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_308: forall b: G, (b <+> ((((m <+> (e <+> (e <+> m))) <+> m) <+> m) <+> (m <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f b (f (f (f (f m (f e (f e m))) m) m) (f m (f m m))))) ((f b (f (f (f m (f e (f e m))) m) (f m (f m m))))).
surgery id_r ((f b (f (f (f m (f e (f e m))) m) (f m (f m m))))) ((f b (f (f m (f e (f e m))) (f m (f m m))))).
surgery id_l ((f b (f (f m (f e (f e m))) (f m (f m m))))) ((f b (f (f m (f e m)) (f m (f m m))))).
surgery id_l ((f b (f (f m (f e m)) (f m (f m m))))) ((f b (f (f m m) (f m (f m m))))).
surgery id_r ((f b (f (f m m) (f m (f m m))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_309: forall b: G, ((((e <+> (e <+> m)) <+> m) <+> ((e <+> (e <+> e)) <+> (e <+> e))) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e (f e m)) m) (f (f e (f e e)) (f e e))) b)) ((f (f (f e (f e m)) (f (f e (f e e)) (f e e))) b)).
surgery id_l ((f (f (f e (f e m)) (f (f e (f e e)) (f e e))) b)) ((f (f (f e m) (f (f e (f e e)) (f e e))) b)).
surgery id_r ((f (f (f e m) (f (f e (f e e)) (f e e))) b)) ((f (f e (f (f e (f e e)) (f e e))) b)).
surgery id_l ((f (f e (f (f e (f e e)) (f e e))) b)) ((f (f e (f (f e e) (f e e))) b)).
surgery id_l ((f (f e (f (f e e) (f e e))) b)) ((f (f e (f e (f e e))) b)).
surgery id_l ((f (f e (f e (f e e))) b)) ((f (f e (f e e)) b)).
surgery id_l ((f (f e (f e e)) b)) ((f (f e e) b)).
surgery id_l ((f (f e e) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_310: forall b: G, ((e <+> ((b <+> (m <+> m)) <+> m)) <+> (((m <+> m) <+> m) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f b (f m m)) m)) (f (f (f m m) m) (f m m)))) ((f (f e (f (f b m) m)) (f (f (f m m) m) (f m m)))).
surgery id_r ((f (f e (f (f b m) m)) (f (f (f m m) m) (f m m)))) ((f (f e (f b m)) (f (f (f m m) m) (f m m)))).
surgery id_r ((f (f e (f b m)) (f (f (f m m) m) (f m m)))) ((f (f e b) (f (f (f m m) m) (f m m)))).
surgery id_l ((f (f e b) (f (f (f m m) m) (f m m)))) ((f b (f (f (f m m) m) (f m m)))).
surgery id_r ((f b (f (f (f m m) m) (f m m)))) ((f b (f (f m m) (f m m)))).
surgery id_r ((f b (f (f m m) (f m m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_311: forall b: G, ((e <+> m) <+> ((((e <+> (m <+> m)) <+> e) <+> ((m <+> m) <+> m)) <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f (f (f e (f m m)) e) (f (f m m) m)) b))) ((f e (f (f (f (f e (f m m)) e) (f (f m m) m)) b))).
surgery id_r ((f e (f (f (f (f e (f m m)) e) (f (f m m) m)) b))) ((f e (f (f (f (f e m) e) (f (f m m) m)) b))).
surgery id_r ((f e (f (f (f (f e m) e) (f (f m m) m)) b))) ((f e (f (f (f e e) (f (f m m) m)) b))).
surgery id_l ((f e (f (f (f e e) (f (f m m) m)) b))) ((f e (f (f e (f (f m m) m)) b))).
surgery id_r ((f e (f (f e (f (f m m) m)) b))) ((f e (f (f e (f m m)) b))).
surgery id_r ((f e (f (f e (f m m)) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_312: forall b: G, ((((e <+> m) <+> (e <+> m)) <+> m) <+> (((e <+> (e <+> m)) <+> e) <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f e m)) m) (f (f (f e (f e m)) e) b))) ((f (f (f e m) (f e m)) (f (f (f e (f e m)) e) b))).
surgery id_r ((f (f (f e m) (f e m)) (f (f (f e (f e m)) e) b))) ((f (f e (f e m)) (f (f (f e (f e m)) e) b))).
surgery id_l ((f (f e (f e m)) (f (f (f e (f e m)) e) b))) ((f (f e m) (f (f (f e (f e m)) e) b))).
surgery id_r ((f (f e m) (f (f (f e (f e m)) e) b))) ((f e (f (f (f e (f e m)) e) b))).
surgery id_l ((f e (f (f (f e (f e m)) e) b))) ((f e (f (f (f e m) e) b))).
surgery id_r ((f e (f (f (f e m) e) b))) ((f e (f (f e e) b))).
surgery id_l ((f e (f (f e e) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_313: forall b: G, (((e <+> b) <+> ((((e <+> m) <+> m) <+> (e <+> m)) <+> m)) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e b) (f (f (f (f e m) m) (f e m)) m)) (f m m))) ((f (f b (f (f (f (f e m) m) (f e m)) m)) (f m m))).
surgery id_r ((f (f b (f (f (f (f e m) m) (f e m)) m)) (f m m))) ((f (f b (f (f (f e m) (f e m)) m)) (f m m))).
surgery id_r ((f (f b (f (f (f e m) (f e m)) m)) (f m m))) ((f (f b (f (f e (f e m)) m)) (f m m))).
surgery id_l ((f (f b (f (f e (f e m)) m)) (f m m))) ((f (f b (f (f e m) m)) (f m m))).
surgery id_r ((f (f b (f (f e m) m)) (f m m))) ((f (f b (f e m)) (f m m))).
surgery id_l ((f (f b (f e m)) (f m m))) ((f (f b m) (f m m))).
surgery id_r ((f (f b m) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_314: forall b: G, ((e <+> m) <+> ((e <+> ((e <+> ((m <+> m) <+> m)) <+> m)) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f e (f (f e (f (f m m) m)) m)) (f e b)))) ((f e (f (f e (f (f e (f (f m m) m)) m)) (f e b)))).
surgery id_r ((f e (f (f e (f (f e (f (f m m) m)) m)) (f e b)))) ((f e (f (f e (f (f e (f m m)) m)) (f e b)))).
surgery id_r ((f e (f (f e (f (f e (f m m)) m)) (f e b)))) ((f e (f (f e (f (f e m) m)) (f e b)))).
surgery id_r ((f e (f (f e (f (f e m) m)) (f e b)))) ((f e (f (f e (f e m)) (f e b)))).
surgery id_l ((f e (f (f e (f e m)) (f e b)))) ((f e (f (f e m) (f e b)))).
surgery id_r ((f e (f (f e m) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_315: forall b: G, (((e <+> (m <+> (e <+> m))) <+> e) <+> (((e <+> e) <+> m) <+> (b <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f m (f e m))) e) (f (f (f e e) m) (f b m)))) ((f (f (f e (f m m)) e) (f (f (f e e) m) (f b m)))).
surgery id_r ((f (f (f e (f m m)) e) (f (f (f e e) m) (f b m)))) ((f (f (f e m) e) (f (f (f e e) m) (f b m)))).
surgery id_r ((f (f (f e m) e) (f (f (f e e) m) (f b m)))) ((f (f e e) (f (f (f e e) m) (f b m)))).
surgery id_l ((f (f e e) (f (f (f e e) m) (f b m)))) ((f e (f (f (f e e) m) (f b m)))).
surgery id_r ((f e (f (f (f e e) m) (f b m)))) ((f e (f (f e e) (f b m)))).
surgery id_l ((f e (f (f e e) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_316: forall b: G, ((((e <+> (e <+> m)) <+> e) <+> e) <+> ((b <+> m) <+> (e <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e (f e m)) e) e) (f (f b m) (f e (f m m))))) ((f (f (f (f e m) e) e) (f (f b m) (f e (f m m))))).
surgery id_r ((f (f (f (f e m) e) e) (f (f b m) (f e (f m m))))) ((f (f (f e e) e) (f (f b m) (f e (f m m))))).
surgery id_l ((f (f (f e e) e) (f (f b m) (f e (f m m))))) ((f (f e e) (f (f b m) (f e (f m m))))).
surgery id_l ((f (f e e) (f (f b m) (f e (f m m))))) ((f e (f (f b m) (f e (f m m))))).
surgery id_r ((f e (f (f b m) (f e (f m m))))) ((f e (f b (f e (f m m))))).
surgery id_l ((f e (f b (f e (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_317: forall b: G, ((b <+> (((e <+> e) <+> (m <+> (e <+> m))) <+> (m <+> m))) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f b (f (f (f e e) (f m (f e m))) (f m m))) (f e m))) ((f (f b (f (f e (f m (f e m))) (f m m))) (f e m))).
surgery id_l ((f (f b (f (f e (f m (f e m))) (f m m))) (f e m))) ((f (f b (f (f e (f m m)) (f m m))) (f e m))).
surgery id_r ((f (f b (f (f e (f m m)) (f m m))) (f e m))) ((f (f b (f (f e m) (f m m))) (f e m))).
surgery id_r ((f (f b (f (f e m) (f m m))) (f e m))) ((f (f b (f e (f m m))) (f e m))).
surgery id_l ((f (f b (f e (f m m))) (f e m))) ((f (f b (f m m)) (f e m))).
surgery id_r ((f (f b (f m m)) (f e m))) ((f (f b m) (f e m))).
surgery id_r ((f (f b m) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_318: forall b: G, (((b <+> m) <+> ((e <+> (e <+> m)) <+> m)) <+> (((e <+> m) <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f (f e (f e m)) m)) (f (f (f e m) m) m))) ((f (f b (f (f e (f e m)) m)) (f (f (f e m) m) m))).
surgery id_l ((f (f b (f (f e (f e m)) m)) (f (f (f e m) m) m))) ((f (f b (f (f e m) m)) (f (f (f e m) m) m))).
surgery id_r ((f (f b (f (f e m) m)) (f (f (f e m) m) m))) ((f (f b (f e m)) (f (f (f e m) m) m))).
surgery id_l ((f (f b (f e m)) (f (f (f e m) m) m))) ((f (f b m) (f (f (f e m) m) m))).
surgery id_r ((f (f b m) (f (f (f e m) m) m))) ((f b (f (f (f e m) m) m))).
surgery id_r ((f b (f (f (f e m) m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_319: forall b: G, ((e <+> m) <+> (((e <+> e) <+> (e <+> e)) <+> (((e <+> e) <+> b) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f (f e e) (f e e)) (f (f (f e e) b) m)))) ((f e (f (f (f e e) (f e e)) (f (f (f e e) b) m)))).
surgery id_l ((f e (f (f (f e e) (f e e)) (f (f (f e e) b) m)))) ((f e (f (f e (f e e)) (f (f (f e e) b) m)))).
surgery id_l ((f e (f (f e (f e e)) (f (f (f e e) b) m)))) ((f e (f (f e e) (f (f (f e e) b) m)))).
surgery id_l ((f e (f (f e e) (f (f (f e e) b) m)))) ((f e (f e (f (f (f e e) b) m)))).
surgery id_l ((f e (f e (f (f (f e e) b) m)))) ((f e (f (f (f e e) b) m))).
surgery id_l ((f e (f (f (f e e) b) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_320: forall b: G, ((b <+> (e <+> (m <+> (e <+> (e <+> m))))) <+> ((e <+> m) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f b (f e (f m (f e (f e m))))) (f (f e m) (f m m)))) ((f (f b (f m (f e (f e m)))) (f (f e m) (f m m)))).
surgery id_l ((f (f b (f m (f e (f e m)))) (f (f e m) (f m m)))) ((f (f b (f m (f e m))) (f (f e m) (f m m)))).
surgery id_l ((f (f b (f m (f e m))) (f (f e m) (f m m)))) ((f (f b (f m m)) (f (f e m) (f m m)))).
surgery id_r ((f (f b (f m m)) (f (f e m) (f m m)))) ((f (f b m) (f (f e m) (f m m)))).
surgery id_r ((f (f b m) (f (f e m) (f m m)))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_321: forall b: G, ((e <+> m) <+> ((((e <+> m) <+> (e <+> m)) <+> b) <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f (f (f e m) (f e m)) b) (f e (f e m))))) ((f e (f (f (f (f e m) (f e m)) b) (f e (f e m))))).
surgery id_r ((f e (f (f (f (f e m) (f e m)) b) (f e (f e m))))) ((f e (f (f (f e (f e m)) b) (f e (f e m))))).
surgery id_l ((f e (f (f (f e (f e m)) b) (f e (f e m))))) ((f e (f (f (f e m) b) (f e (f e m))))).
surgery id_r ((f e (f (f (f e m) b) (f e (f e m))))) ((f e (f (f e b) (f e (f e m))))).
surgery id_l ((f e (f (f e b) (f e (f e m))))) ((f e (f b (f e (f e m))))).
surgery id_l ((f e (f b (f e (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_322: forall b: G, (((e <+> e) <+> ((e <+> m) <+> (m <+> (m <+> m)))) <+> ((e <+> m) <+> b)) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f e m) (f m (f m m)))) (f (f e m) b))) ((f (f e (f (f e m) (f m (f m m)))) (f (f e m) b))).
surgery id_r ((f (f e (f (f e m) (f m (f m m)))) (f (f e m) b))) ((f (f e (f e (f m (f m m)))) (f (f e m) b))).
surgery id_l ((f (f e (f e (f m (f m m)))) (f (f e m) b))) ((f (f e (f m (f m m))) (f (f e m) b))).
surgery id_r ((f (f e (f m (f m m))) (f (f e m) b))) ((f (f e (f m m)) (f (f e m) b))).
surgery id_r ((f (f e (f m m)) (f (f e m) b))) ((f (f e m) (f (f e m) b))).
surgery id_r ((f (f e m) (f (f e m) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_323: forall b: G, (((e <+> (e <+> m)) <+> (e <+> e)) <+> ((b <+> m) <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f e e)) (f (f b m) (f e (f e m))))) ((f (f (f e m) (f e e)) (f (f b m) (f e (f e m))))).
surgery id_r ((f (f (f e m) (f e e)) (f (f b m) (f e (f e m))))) ((f (f e (f e e)) (f (f b m) (f e (f e m))))).
surgery id_l ((f (f e (f e e)) (f (f b m) (f e (f e m))))) ((f (f e e) (f (f b m) (f e (f e m))))).
surgery id_l ((f (f e e) (f (f b m) (f e (f e m))))) ((f e (f (f b m) (f e (f e m))))).
surgery id_r ((f e (f (f b m) (f e (f e m))))) ((f e (f b (f e (f e m))))).
surgery id_l ((f e (f b (f e (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_324: forall b: G, ((((e <+> m) <+> e) <+> ((e <+> (m <+> m)) <+> ((m <+> m) <+> m))) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) e) (f (f e (f m m)) (f (f m m) m))) b)) ((f (f (f e e) (f (f e (f m m)) (f (f m m) m))) b)).
surgery id_l ((f (f (f e e) (f (f e (f m m)) (f (f m m) m))) b)) ((f (f e (f (f e (f m m)) (f (f m m) m))) b)).
surgery id_r ((f (f e (f (f e (f m m)) (f (f m m) m))) b)) ((f (f e (f (f e m) (f (f m m) m))) b)).
surgery id_r ((f (f e (f (f e m) (f (f m m) m))) b)) ((f (f e (f e (f (f m m) m))) b)).
surgery id_l ((f (f e (f e (f (f m m) m))) b)) ((f (f e (f (f m m) m)) b)).
surgery id_r ((f (f e (f (f m m) m)) b)) ((f (f e (f m m)) b)).
surgery id_r ((f (f e (f m m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_325: forall b: G, (((e <+> e) <+> (((e <+> e) <+> e) <+> b)) <+> ((m <+> m) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f (f e e) e) b)) (f (f m m) (f e m)))) ((f (f e (f (f (f e e) e) b)) (f (f m m) (f e m)))).
surgery id_l ((f (f e (f (f (f e e) e) b)) (f (f m m) (f e m)))) ((f (f e (f (f e e) b)) (f (f m m) (f e m)))).
surgery id_l ((f (f e (f (f e e) b)) (f (f m m) (f e m)))) ((f (f e (f e b)) (f (f m m) (f e m)))).
surgery id_l ((f (f e (f e b)) (f (f m m) (f e m)))) ((f (f e b) (f (f m m) (f e m)))).
surgery id_l ((f (f e b) (f (f m m) (f e m)))) ((f b (f (f m m) (f e m)))).
surgery id_r ((f b (f (f m m) (f e m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_326: forall b: G, ((e <+> ((m <+> m) <+> (m <+> (e <+> m)))) <+> ((b <+> m) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f m m) (f m (f e m)))) (f (f b m) (f e m)))) ((f (f e (f m (f m (f e m)))) (f (f b m) (f e m)))).
surgery id_l ((f (f e (f m (f m (f e m)))) (f (f b m) (f e m)))) ((f (f e (f m (f m m))) (f (f b m) (f e m)))).
surgery id_r ((f (f e (f m (f m m))) (f (f b m) (f e m)))) ((f (f e (f m m)) (f (f b m) (f e m)))).
surgery id_r ((f (f e (f m m)) (f (f b m) (f e m)))) ((f (f e m) (f (f b m) (f e m)))).
surgery id_r ((f (f e m) (f (f b m) (f e m)))) ((f e (f (f b m) (f e m)))).
surgery id_r ((f e (f (f b m) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_327: forall b: G, ((e <+> (e <+> b)) <+> (((e <+> e) <+> ((m <+> m) <+> (e <+> m))) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f e (f e b)) (f (f (f e e) (f (f m m) (f e m))) m))) ((f (f e b) (f (f (f e e) (f (f m m) (f e m))) m))).
surgery id_l ((f (f e b) (f (f (f e e) (f (f m m) (f e m))) m))) ((f b (f (f (f e e) (f (f m m) (f e m))) m))).
surgery id_l ((f b (f (f (f e e) (f (f m m) (f e m))) m))) ((f b (f (f e (f (f m m) (f e m))) m))).
surgery id_r ((f b (f (f e (f (f m m) (f e m))) m))) ((f b (f (f e (f m (f e m))) m))).
surgery id_l ((f b (f (f e (f m (f e m))) m))) ((f b (f (f e (f m m)) m))).
surgery id_r ((f b (f (f e (f m m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_328: forall b: G, (((e <+> (e <+> (m <+> m))) <+> ((e <+> m) <+> (m <+> m))) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e (f m m))) (f (f e m) (f m m))) (f e b))) ((f (f (f e (f m m)) (f (f e m) (f m m))) (f e b))).
surgery id_r ((f (f (f e (f m m)) (f (f e m) (f m m))) (f e b))) ((f (f (f e m) (f (f e m) (f m m))) (f e b))).
surgery id_r ((f (f (f e m) (f (f e m) (f m m))) (f e b))) ((f (f e (f (f e m) (f m m))) (f e b))).
surgery id_r ((f (f e (f (f e m) (f m m))) (f e b))) ((f (f e (f e (f m m))) (f e b))).
surgery id_l ((f (f e (f e (f m m))) (f e b))) ((f (f e (f m m)) (f e b))).
surgery id_r ((f (f e (f m m)) (f e b))) ((f (f e m) (f e b))).
surgery id_r ((f (f e m) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_329: forall b: G, (((e <+> ((e <+> e) <+> e)) <+> (e <+> (e <+> ((e <+> m) <+> e)))) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f (f e e) e)) (f e (f e (f (f e m) e)))) b)) ((f (f (f e (f e e)) (f e (f e (f (f e m) e)))) b)).
surgery id_l ((f (f (f e (f e e)) (f e (f e (f (f e m) e)))) b)) ((f (f (f e e) (f e (f e (f (f e m) e)))) b)).
surgery id_l ((f (f (f e e) (f e (f e (f (f e m) e)))) b)) ((f (f e (f e (f e (f (f e m) e)))) b)).
surgery id_l ((f (f e (f e (f e (f (f e m) e)))) b)) ((f (f e (f e (f (f e m) e))) b)).
surgery id_l ((f (f e (f e (f (f e m) e))) b)) ((f (f e (f (f e m) e)) b)).
surgery id_r ((f (f e (f (f e m) e)) b)) ((f (f e (f e e)) b)).
surgery id_l ((f (f e (f e e)) b)) ((f (f e e) b)).
surgery id_l ((f (f e e) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_330: forall b: G, (((e <+> m) <+> (e <+> ((m <+> (m <+> (e <+> m))) <+> m))) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f e (f (f m (f m (f e m))) m))) (f e b))) ((f (f e (f e (f (f m (f m (f e m))) m))) (f e b))).
surgery id_l ((f (f e (f e (f (f m (f m (f e m))) m))) (f e b))) ((f (f e (f (f m (f m (f e m))) m)) (f e b))).
surgery id_l ((f (f e (f (f m (f m (f e m))) m)) (f e b))) ((f (f e (f (f m (f m m)) m)) (f e b))).
surgery id_r ((f (f e (f (f m (f m m)) m)) (f e b))) ((f (f e (f (f m m) m)) (f e b))).
surgery id_r ((f (f e (f (f m m) m)) (f e b))) ((f (f e (f m m)) (f e b))).
surgery id_r ((f (f e (f m m)) (f e b))) ((f (f e m) (f e b))).
surgery id_r ((f (f e m) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_331: forall b: G, ((b <+> m) <+> ((e <+> e) <+> ((e <+> ((e <+> m) <+> (e <+> m))) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f e e) (f (f e (f (f e m) (f e m))) m)))) ((f b (f (f e e) (f (f e (f (f e m) (f e m))) m)))).
surgery id_l ((f b (f (f e e) (f (f e (f (f e m) (f e m))) m)))) ((f b (f e (f (f e (f (f e m) (f e m))) m)))).
surgery id_l ((f b (f e (f (f e (f (f e m) (f e m))) m)))) ((f b (f (f e (f (f e m) (f e m))) m))).
surgery id_r ((f b (f (f e (f (f e m) (f e m))) m))) ((f b (f (f e (f e (f e m))) m))).
surgery id_l ((f b (f (f e (f e (f e m))) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_332: forall b: G, (((e <+> m) <+> m) <+> (((e <+> ((e <+> e) <+> m)) <+> e) <+> (b <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) m) (f (f (f e (f (f e e) m)) e) (f b m)))) ((f (f e m) (f (f (f e (f (f e e) m)) e) (f b m)))).
surgery id_r ((f (f e m) (f (f (f e (f (f e e) m)) e) (f b m)))) ((f e (f (f (f e (f (f e e) m)) e) (f b m)))).
surgery id_l ((f e (f (f (f e (f (f e e) m)) e) (f b m)))) ((f e (f (f (f e (f e m)) e) (f b m)))).
surgery id_l ((f e (f (f (f e (f e m)) e) (f b m)))) ((f e (f (f (f e m) e) (f b m)))).
surgery id_r ((f e (f (f (f e m) e) (f b m)))) ((f e (f (f e e) (f b m)))).
surgery id_l ((f e (f (f e e) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_333: forall b: G, (((e <+> m) <+> e) <+> (b <+> (m <+> ((e <+> m) <+> ((m <+> m) <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) e) (f b (f m (f (f e m) (f (f m m) m)))))) ((f (f e e) (f b (f m (f (f e m) (f (f m m) m)))))).
surgery id_l ((f (f e e) (f b (f m (f (f e m) (f (f m m) m)))))) ((f e (f b (f m (f (f e m) (f (f m m) m)))))).
surgery id_r ((f e (f b (f m (f (f e m) (f (f m m) m)))))) ((f e (f b (f m (f e (f (f m m) m)))))).
surgery id_l ((f e (f b (f m (f e (f (f m m) m)))))) ((f e (f b (f m (f (f m m) m))))).
surgery id_r ((f e (f b (f m (f (f m m) m))))) ((f e (f b (f m (f m m))))).
surgery id_r ((f e (f b (f m (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_334: forall b: G, (((e <+> (m <+> m)) <+> b) <+> ((e <+> (e <+> (e <+> m))) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f m m)) b) (f (f e (f e (f e m))) (f m m)))) ((f (f (f e m) b) (f (f e (f e (f e m))) (f m m)))).
surgery id_r ((f (f (f e m) b) (f (f e (f e (f e m))) (f m m)))) ((f (f e b) (f (f e (f e (f e m))) (f m m)))).
surgery id_l ((f (f e b) (f (f e (f e (f e m))) (f m m)))) ((f b (f (f e (f e (f e m))) (f m m)))).
surgery id_l ((f b (f (f e (f e (f e m))) (f m m)))) ((f b (f (f e (f e m)) (f m m)))).
surgery id_l ((f b (f (f e (f e m)) (f m m)))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_335: forall b: G, ((b <+> (e <+> (e <+> m))) <+> ((e <+> (((e <+> e) <+> e) <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f b (f e (f e m))) (f (f e (f (f (f e e) e) m)) m))) ((f (f b (f e m)) (f (f e (f (f (f e e) e) m)) m))).
surgery id_l ((f (f b (f e m)) (f (f e (f (f (f e e) e) m)) m))) ((f (f b m) (f (f e (f (f (f e e) e) m)) m))).
surgery id_r ((f (f b m) (f (f e (f (f (f e e) e) m)) m))) ((f b (f (f e (f (f (f e e) e) m)) m))).
surgery id_l ((f b (f (f e (f (f (f e e) e) m)) m))) ((f b (f (f e (f (f e e) m)) m))).
surgery id_l ((f b (f (f e (f (f e e) m)) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_336: forall b: G, ((b <+> m) <+> (m <+> (((((e <+> (e <+> m)) <+> e) <+> e) <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f m (f (f (f (f (f e (f e m)) e) e) m) m)))) ((f b (f m (f (f (f (f (f e (f e m)) e) e) m) m)))).
surgery id_r ((f b (f m (f (f (f (f (f e (f e m)) e) e) m) m)))) ((f b (f m (f (f (f (f e (f e m)) e) e) m)))).
surgery id_l ((f b (f m (f (f (f (f e (f e m)) e) e) m)))) ((f b (f m (f (f (f (f e m) e) e) m)))).
surgery id_r ((f b (f m (f (f (f (f e m) e) e) m)))) ((f b (f m (f (f (f e e) e) m)))).
surgery id_l ((f b (f m (f (f (f e e) e) m)))) ((f b (f m (f (f e e) m)))).
surgery id_l ((f b (f m (f (f e e) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_337: forall b: G, (((e <+> m) <+> (m <+> m)) <+> ((((e <+> e) <+> (e <+> e)) <+> e) <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f m m)) (f (f (f (f e e) (f e e)) e) b))) ((f (f e (f m m)) (f (f (f (f e e) (f e e)) e) b))).
surgery id_r ((f (f e (f m m)) (f (f (f (f e e) (f e e)) e) b))) ((f (f e m) (f (f (f (f e e) (f e e)) e) b))).
surgery id_r ((f (f e m) (f (f (f (f e e) (f e e)) e) b))) ((f e (f (f (f (f e e) (f e e)) e) b))).
surgery id_l ((f e (f (f (f (f e e) (f e e)) e) b))) ((f e (f (f (f e (f e e)) e) b))).
surgery id_l ((f e (f (f (f e (f e e)) e) b))) ((f e (f (f (f e e) e) b))).
surgery id_l ((f e (f (f (f e e) e) b))) ((f e (f (f e e) b))).
surgery id_l ((f e (f (f e e) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_338: forall b: G, (((e <+> e) <+> (((e <+> b) <+> (m <+> m)) <+> ((e <+> e) <+> m))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f e e) (f (f (f e b) (f m m)) (f (f e e) m))) m)) ((f (f e e) (f (f (f e b) (f m m)) (f (f e e) m)))).
surgery id_l ((f (f e e) (f (f (f e b) (f m m)) (f (f e e) m)))) ((f e (f (f (f e b) (f m m)) (f (f e e) m)))).
surgery id_l ((f e (f (f (f e b) (f m m)) (f (f e e) m)))) ((f e (f (f b (f m m)) (f (f e e) m)))).
surgery id_r ((f e (f (f b (f m m)) (f (f e e) m)))) ((f e (f (f b m) (f (f e e) m)))).
surgery id_r ((f e (f (f b m) (f (f e e) m)))) ((f e (f b (f (f e e) m)))).
surgery id_l ((f e (f b (f (f e e) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_339: forall b: G, (((b <+> m) <+> (((e <+> m) <+> m) <+> m)) <+> (e <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f (f (f e m) m) m)) (f e (f e (f e m))))) ((f (f b (f (f (f e m) m) m)) (f e (f e (f e m))))).
surgery id_r ((f (f b (f (f (f e m) m) m)) (f e (f e (f e m))))) ((f (f b (f (f e m) m)) (f e (f e (f e m))))).
surgery id_r ((f (f b (f (f e m) m)) (f e (f e (f e m))))) ((f (f b (f e m)) (f e (f e (f e m))))).
surgery id_l ((f (f b (f e m)) (f e (f e (f e m))))) ((f (f b m) (f e (f e (f e m))))).
surgery id_r ((f (f b m) (f e (f e (f e m))))) ((f b (f e (f e (f e m))))).
surgery id_l ((f b (f e (f e (f e m))))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_340: forall b: G, ((e <+> b) <+> (e <+> (((e <+> m) <+> ((e <+> m) <+> m)) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f e (f (f (f e m) (f (f e m) m)) (f m m))))) ((f b (f e (f (f (f e m) (f (f e m) m)) (f m m))))).
surgery id_l ((f b (f e (f (f (f e m) (f (f e m) m)) (f m m))))) ((f b (f (f (f e m) (f (f e m) m)) (f m m)))).
surgery id_r ((f b (f (f (f e m) (f (f e m) m)) (f m m)))) ((f b (f (f e (f (f e m) m)) (f m m)))).
surgery id_r ((f b (f (f e (f (f e m) m)) (f m m)))) ((f b (f (f e (f e m)) (f m m)))).
surgery id_l ((f b (f (f e (f e m)) (f m m)))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_341: forall b: G, ((e <+> ((e <+> ((e <+> e) <+> (m <+> m))) <+> m)) <+> ((b <+> m) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f e (f (f e e) (f m m))) m)) (f (f b m) m))) ((f (f e (f (f e (f e (f m m))) m)) (f (f b m) m))).
surgery id_l ((f (f e (f (f e (f e (f m m))) m)) (f (f b m) m))) ((f (f e (f (f e (f m m)) m)) (f (f b m) m))).
surgery id_r ((f (f e (f (f e (f m m)) m)) (f (f b m) m))) ((f (f e (f (f e m) m)) (f (f b m) m))).
surgery id_r ((f (f e (f (f e m) m)) (f (f b m) m))) ((f (f e (f e m)) (f (f b m) m))).
surgery id_l ((f (f e (f e m)) (f (f b m) m))) ((f (f e m) (f (f b m) m))).
surgery id_r ((f (f e m) (f (f b m) m))) ((f e (f (f b m) m))).
surgery id_r ((f e (f (f b m) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_342: forall b: G, (b <+> ((m <+> m) <+> ((e <+> (m <+> (e <+> m))) <+> (e <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_r ((f b (f (f m m) (f (f e (f m (f e m))) (f e (f m m)))))) ((f b (f m (f (f e (f m (f e m))) (f e (f m m)))))).
surgery id_l ((f b (f m (f (f e (f m (f e m))) (f e (f m m)))))) ((f b (f m (f (f e (f m m)) (f e (f m m)))))).
surgery id_r ((f b (f m (f (f e (f m m)) (f e (f m m)))))) ((f b (f m (f (f e m) (f e (f m m)))))).
surgery id_r ((f b (f m (f (f e m) (f e (f m m)))))) ((f b (f m (f e (f e (f m m)))))).
surgery id_l ((f b (f m (f e (f e (f m m)))))) ((f b (f m (f e (f m m))))).
surgery id_l ((f b (f m (f e (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_343: forall b: G, ((((e <+> b) <+> m) <+> (m <+> (m <+> m))) <+> (m <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e b) m) (f m (f m m))) (f m (f e (f e m))))) ((f (f (f e b) (f m (f m m))) (f m (f e (f e m))))).
surgery id_l ((f (f (f e b) (f m (f m m))) (f m (f e (f e m))))) ((f (f b (f m (f m m))) (f m (f e (f e m))))).
surgery id_r ((f (f b (f m (f m m))) (f m (f e (f e m))))) ((f (f b (f m m)) (f m (f e (f e m))))).
surgery id_r ((f (f b (f m m)) (f m (f e (f e m))))) ((f (f b m) (f m (f e (f e m))))).
surgery id_r ((f (f b m) (f m (f e (f e m))))) ((f b (f m (f e (f e m))))).
surgery id_l ((f b (f m (f e (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_344: forall b: G, (((e <+> (e <+> m)) <+> (m <+> m)) <+> (e <+> (e <+> (b <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f m m)) (f e (f e (f b (f m m)))))) ((f (f (f e m) (f m m)) (f e (f e (f b (f m m)))))).
surgery id_r ((f (f (f e m) (f m m)) (f e (f e (f b (f m m)))))) ((f (f e (f m m)) (f e (f e (f b (f m m)))))).
surgery id_r ((f (f e (f m m)) (f e (f e (f b (f m m)))))) ((f (f e m) (f e (f e (f b (f m m)))))).
surgery id_r ((f (f e m) (f e (f e (f b (f m m)))))) ((f e (f e (f e (f b (f m m)))))).
surgery id_l ((f e (f e (f e (f b (f m m)))))) ((f e (f e (f b (f m m))))).
surgery id_l ((f e (f e (f b (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_345: forall b: G, ((b <+> ((e <+> m) <+> m)) <+> ((e <+> (e <+> m)) <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f b (f (f e m) m)) (f (f e (f e m)) (f e (f e m))))) ((f (f b (f e m)) (f (f e (f e m)) (f e (f e m))))).
surgery id_l ((f (f b (f e m)) (f (f e (f e m)) (f e (f e m))))) ((f (f b m) (f (f e (f e m)) (f e (f e m))))).
surgery id_r ((f (f b m) (f (f e (f e m)) (f e (f e m))))) ((f b (f (f e (f e m)) (f e (f e m))))).
surgery id_l ((f b (f (f e (f e m)) (f e (f e m))))) ((f b (f (f e m) (f e (f e m))))).
surgery id_r ((f b (f (f e m) (f e (f e m))))) ((f b (f e (f e (f e m))))).
surgery id_l ((f b (f e (f e (f e m))))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_346: forall b: G, ((((e <+> e) <+> (m <+> m)) <+> (((e <+> m) <+> m) <+> (b <+> m))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) (f m m)) (f (f (f e m) m) (f b m))) m)) ((f (f (f e e) (f m m)) (f (f (f e m) m) (f b m)))).
surgery id_l ((f (f (f e e) (f m m)) (f (f (f e m) m) (f b m)))) ((f (f e (f m m)) (f (f (f e m) m) (f b m)))).
surgery id_r ((f (f e (f m m)) (f (f (f e m) m) (f b m)))) ((f (f e m) (f (f (f e m) m) (f b m)))).
surgery id_r ((f (f e m) (f (f (f e m) m) (f b m)))) ((f e (f (f (f e m) m) (f b m)))).
surgery id_r ((f e (f (f (f e m) m) (f b m)))) ((f e (f (f e m) (f b m)))).
surgery id_r ((f e (f (f e m) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_347: forall b: G, (((e <+> m) <+> (((e <+> (e <+> e)) <+> (e <+> m)) <+> b)) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f (f (f e (f e e)) (f e m)) b)) (f m m))) ((f (f e (f (f (f e (f e e)) (f e m)) b)) (f m m))).
surgery id_l ((f (f e (f (f (f e (f e e)) (f e m)) b)) (f m m))) ((f (f e (f (f (f e e) (f e m)) b)) (f m m))).
surgery id_l ((f (f e (f (f (f e e) (f e m)) b)) (f m m))) ((f (f e (f (f e (f e m)) b)) (f m m))).
surgery id_l ((f (f e (f (f e (f e m)) b)) (f m m))) ((f (f e (f (f e m) b)) (f m m))).
surgery id_r ((f (f e (f (f e m) b)) (f m m))) ((f (f e (f e b)) (f m m))).
surgery id_l ((f (f e (f e b)) (f m m))) ((f (f e b) (f m m))).
surgery id_l ((f (f e b) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_348: forall b: G, ((b <+> (e <+> m)) <+> ((m <+> ((e <+> m) <+> m)) <+> (m <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f b (f e m)) (f (f m (f (f e m) m)) (f m (f m m))))) ((f (f b m) (f (f m (f (f e m) m)) (f m (f m m))))).
surgery id_r ((f (f b m) (f (f m (f (f e m) m)) (f m (f m m))))) ((f b (f (f m (f (f e m) m)) (f m (f m m))))).
surgery id_r ((f b (f (f m (f (f e m) m)) (f m (f m m))))) ((f b (f (f m (f e m)) (f m (f m m))))).
surgery id_l ((f b (f (f m (f e m)) (f m (f m m))))) ((f b (f (f m m) (f m (f m m))))).
surgery id_r ((f b (f (f m m) (f m (f m m))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_349: forall b: G, ((e <+> m) <+> (b <+> (e <+> ((((m <+> m) <+> m) <+> m) <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f b (f e (f (f (f (f m m) m) m) (f e m)))))) ((f e (f b (f e (f (f (f (f m m) m) m) (f e m)))))).
surgery id_l ((f e (f b (f e (f (f (f (f m m) m) m) (f e m)))))) ((f e (f b (f (f (f (f m m) m) m) (f e m))))).
surgery id_r ((f e (f b (f (f (f (f m m) m) m) (f e m))))) ((f e (f b (f (f (f m m) m) (f e m))))).
surgery id_r ((f e (f b (f (f (f m m) m) (f e m))))) ((f e (f b (f (f m m) (f e m))))).
surgery id_r ((f e (f b (f (f m m) (f e m))))) ((f e (f b (f m (f e m))))).
surgery id_l ((f e (f b (f m (f e m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_350: forall b: G, ((e <+> m) <+> (b <+> (((((e <+> e) <+> m) <+> (e <+> m)) <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f b (f (f (f (f (f e e) m) (f e m)) m) m)))) ((f e (f b (f (f (f (f (f e e) m) (f e m)) m) m)))).
surgery id_r ((f e (f b (f (f (f (f (f e e) m) (f e m)) m) m)))) ((f e (f b (f (f (f (f e e) m) (f e m)) m)))).
surgery id_r ((f e (f b (f (f (f (f e e) m) (f e m)) m)))) ((f e (f b (f (f (f e e) (f e m)) m)))).
surgery id_l ((f e (f b (f (f (f e e) (f e m)) m)))) ((f e (f b (f (f e (f e m)) m)))).
surgery id_l ((f e (f b (f (f e (f e m)) m)))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_351: forall b: G, (((e <+> (((e <+> m) <+> m) <+> (m <+> m))) <+> m) <+> ((e <+> b) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f (f e m) m) (f m m))) m) (f (f e b) m))) ((f (f e (f (f (f e m) m) (f m m))) (f (f e b) m))).
surgery id_r ((f (f e (f (f (f e m) m) (f m m))) (f (f e b) m))) ((f (f e (f (f e m) (f m m))) (f (f e b) m))).
surgery id_r ((f (f e (f (f e m) (f m m))) (f (f e b) m))) ((f (f e (f e (f m m))) (f (f e b) m))).
surgery id_l ((f (f e (f e (f m m))) (f (f e b) m))) ((f (f e (f m m)) (f (f e b) m))).
surgery id_r ((f (f e (f m m)) (f (f e b) m))) ((f (f e m) (f (f e b) m))).
surgery id_r ((f (f e m) (f (f e b) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_352: forall b: G, ((b <+> m) <+> ((e <+> (m <+> m)) <+> ((((e <+> m) <+> e) <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f e (f m m)) (f (f (f (f e m) e) m) m)))) ((f b (f (f e (f m m)) (f (f (f (f e m) e) m) m)))).
surgery id_r ((f b (f (f e (f m m)) (f (f (f (f e m) e) m) m)))) ((f b (f (f e m) (f (f (f (f e m) e) m) m)))).
surgery id_r ((f b (f (f e m) (f (f (f (f e m) e) m) m)))) ((f b (f e (f (f (f (f e m) e) m) m)))).
surgery id_l ((f b (f e (f (f (f (f e m) e) m) m)))) ((f b (f (f (f (f e m) e) m) m))).
surgery id_r ((f b (f (f (f (f e m) e) m) m))) ((f b (f (f (f e m) e) m))).
surgery id_r ((f b (f (f (f e m) e) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_353: forall b: G, ((e <+> (e <+> b)) <+> (((m <+> m) <+> (m <+> m)) <+> ((m <+> m) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e b)) (f (f (f m m) (f m m)) (f (f m m) m)))) ((f (f e b) (f (f (f m m) (f m m)) (f (f m m) m)))).
surgery id_l ((f (f e b) (f (f (f m m) (f m m)) (f (f m m) m)))) ((f b (f (f (f m m) (f m m)) (f (f m m) m)))).
surgery id_r ((f b (f (f (f m m) (f m m)) (f (f m m) m)))) ((f b (f (f m (f m m)) (f (f m m) m)))).
surgery id_r ((f b (f (f m (f m m)) (f (f m m) m)))) ((f b (f (f m m) (f (f m m) m)))).
surgery id_r ((f b (f (f m m) (f (f m m) m)))) ((f b (f m (f (f m m) m)))).
surgery id_r ((f b (f m (f (f m m) m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_354: forall b: G, (((e <+> m) <+> (m <+> ((e <+> e) <+> m))) <+> (e <+> (b <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f m (f (f e e) m))) (f e (f b (f e m))))) ((f (f e (f m (f (f e e) m))) (f e (f b (f e m))))).
surgery id_l ((f (f e (f m (f (f e e) m))) (f e (f b (f e m))))) ((f (f e (f m (f e m))) (f e (f b (f e m))))).
surgery id_l ((f (f e (f m (f e m))) (f e (f b (f e m))))) ((f (f e (f m m)) (f e (f b (f e m))))).
surgery id_r ((f (f e (f m m)) (f e (f b (f e m))))) ((f (f e m) (f e (f b (f e m))))).
surgery id_r ((f (f e m) (f e (f b (f e m))))) ((f e (f e (f b (f e m))))).
surgery id_l ((f e (f e (f b (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_355: forall b: G, ((e <+> (e <+> (e <+> e))) <+> (e <+> (b <+> ((e <+> (e <+> m)) <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e (f e e))) (f e (f b (f (f e (f e m)) m))))) ((f (f e (f e e)) (f e (f b (f (f e (f e m)) m))))).
surgery id_l ((f (f e (f e e)) (f e (f b (f (f e (f e m)) m))))) ((f (f e e) (f e (f b (f (f e (f e m)) m))))).
surgery id_l ((f (f e e) (f e (f b (f (f e (f e m)) m))))) ((f e (f e (f b (f (f e (f e m)) m))))).
surgery id_l ((f e (f e (f b (f (f e (f e m)) m))))) ((f e (f b (f (f e (f e m)) m)))).
surgery id_l ((f e (f b (f (f e (f e m)) m)))) ((f e (f b (f (f e m) m)))).
surgery id_r ((f e (f b (f (f e m) m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_356: forall b: G, (((e <+> (e <+> m)) <+> b) <+> ((e <+> m) <+> ((e <+> (e <+> m)) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) b) (f (f e m) (f (f e (f e m)) m)))) ((f (f (f e m) b) (f (f e m) (f (f e (f e m)) m)))).
surgery id_r ((f (f (f e m) b) (f (f e m) (f (f e (f e m)) m)))) ((f (f e b) (f (f e m) (f (f e (f e m)) m)))).
surgery id_l ((f (f e b) (f (f e m) (f (f e (f e m)) m)))) ((f b (f (f e m) (f (f e (f e m)) m)))).
surgery id_r ((f b (f (f e m) (f (f e (f e m)) m)))) ((f b (f e (f (f e (f e m)) m)))).
surgery id_l ((f b (f e (f (f e (f e m)) m)))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_357: forall b: G, ((e <+> (e <+> b)) <+> (((m <+> m) <+> ((e <+> m) <+> m)) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e b)) (f (f (f m m) (f (f e m) m)) (f e m)))) ((f (f e b) (f (f (f m m) (f (f e m) m)) (f e m)))).
surgery id_l ((f (f e b) (f (f (f m m) (f (f e m) m)) (f e m)))) ((f b (f (f (f m m) (f (f e m) m)) (f e m)))).
surgery id_r ((f b (f (f (f m m) (f (f e m) m)) (f e m)))) ((f b (f (f m (f (f e m) m)) (f e m)))).
surgery id_r ((f b (f (f m (f (f e m) m)) (f e m)))) ((f b (f (f m (f e m)) (f e m)))).
surgery id_l ((f b (f (f m (f e m)) (f e m)))) ((f b (f (f m m) (f e m)))).
surgery id_r ((f b (f (f m m) (f e m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_358: forall b: G, ((e <+> e) <+> ((e <+> (e <+> (((e <+> (m <+> m)) <+> m) <+> m))) <+> b)) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f e (f e (f (f (f e (f m m)) m) m))) b))) ((f e (f (f e (f e (f (f (f e (f m m)) m) m))) b))).
surgery id_l ((f e (f (f e (f e (f (f (f e (f m m)) m) m))) b))) ((f e (f (f e (f (f (f e (f m m)) m) m)) b))).
surgery id_r ((f e (f (f e (f (f (f e (f m m)) m) m)) b))) ((f e (f (f e (f (f e (f m m)) m)) b))).
surgery id_r ((f e (f (f e (f (f e (f m m)) m)) b))) ((f e (f (f e (f (f e m) m)) b))).
surgery id_r ((f e (f (f e (f (f e m) m)) b))) ((f e (f (f e (f e m)) b))).
surgery id_l ((f e (f (f e (f e m)) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_359: forall b: G, (((e <+> ((e <+> m) <+> e)) <+> e) <+> ((e <+> (m <+> m)) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f e m) e)) e) (f (f e (f m m)) (f e b)))) ((f (f (f e (f e e)) e) (f (f e (f m m)) (f e b)))).
surgery id_l ((f (f (f e (f e e)) e) (f (f e (f m m)) (f e b)))) ((f (f (f e e) e) (f (f e (f m m)) (f e b)))).
surgery id_l ((f (f (f e e) e) (f (f e (f m m)) (f e b)))) ((f (f e e) (f (f e (f m m)) (f e b)))).
surgery id_l ((f (f e e) (f (f e (f m m)) (f e b)))) ((f e (f (f e (f m m)) (f e b)))).
surgery id_r ((f e (f (f e (f m m)) (f e b)))) ((f e (f (f e m) (f e b)))).
surgery id_r ((f e (f (f e m) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_360: forall b: G, ((((e <+> e) <+> m) <+> e) <+> ((((e <+> m) <+> m) <+> (e <+> e)) <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) e) (f (f (f (f e m) m) (f e e)) b))) ((f (f (f e e) e) (f (f (f (f e m) m) (f e e)) b))).
surgery id_l ((f (f (f e e) e) (f (f (f (f e m) m) (f e e)) b))) ((f (f e e) (f (f (f (f e m) m) (f e e)) b))).
surgery id_l ((f (f e e) (f (f (f (f e m) m) (f e e)) b))) ((f e (f (f (f (f e m) m) (f e e)) b))).
surgery id_r ((f e (f (f (f (f e m) m) (f e e)) b))) ((f e (f (f (f e m) (f e e)) b))).
surgery id_r ((f e (f (f (f e m) (f e e)) b))) ((f e (f (f e (f e e)) b))).
surgery id_l ((f e (f (f e (f e e)) b))) ((f e (f (f e e) b))).
surgery id_l ((f e (f (f e e) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_361: forall b: G, ((((e <+> m) <+> ((e <+> e) <+> e)) <+> m) <+> ((e <+> b) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f (f e e) e)) m) (f (f e b) (f e m)))) ((f (f (f e m) (f (f e e) e)) (f (f e b) (f e m)))).
surgery id_r ((f (f (f e m) (f (f e e) e)) (f (f e b) (f e m)))) ((f (f e (f (f e e) e)) (f (f e b) (f e m)))).
surgery id_l ((f (f e (f (f e e) e)) (f (f e b) (f e m)))) ((f (f e (f e e)) (f (f e b) (f e m)))).
surgery id_l ((f (f e (f e e)) (f (f e b) (f e m)))) ((f (f e e) (f (f e b) (f e m)))).
surgery id_l ((f (f e e) (f (f e b) (f e m)))) ((f e (f (f e b) (f e m)))).
surgery id_l ((f e (f (f e b) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_362: forall b: G, ((b <+> ((e <+> m) <+> m)) <+> (((m <+> m) <+> m) <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f b (f (f e m) m)) (f (f (f m m) m) (f e (f e m))))) ((f (f b (f e m)) (f (f (f m m) m) (f e (f e m))))).
surgery id_l ((f (f b (f e m)) (f (f (f m m) m) (f e (f e m))))) ((f (f b m) (f (f (f m m) m) (f e (f e m))))).
surgery id_r ((f (f b m) (f (f (f m m) m) (f e (f e m))))) ((f b (f (f (f m m) m) (f e (f e m))))).
surgery id_r ((f b (f (f (f m m) m) (f e (f e m))))) ((f b (f (f m m) (f e (f e m))))).
surgery id_r ((f b (f (f m m) (f e (f e m))))) ((f b (f m (f e (f e m))))).
surgery id_l ((f b (f m (f e (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_363: forall b: G, ((e <+> ((((e <+> e) <+> m) <+> e) <+> (b <+> m))) <+> ((e <+> e) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f (f (f e e) m) e) (f b m))) (f (f e e) m))) ((f (f e (f (f (f e e) e) (f b m))) (f (f e e) m))).
surgery id_l ((f (f e (f (f (f e e) e) (f b m))) (f (f e e) m))) ((f (f e (f (f e e) (f b m))) (f (f e e) m))).
surgery id_l ((f (f e (f (f e e) (f b m))) (f (f e e) m))) ((f (f e (f e (f b m))) (f (f e e) m))).
surgery id_l ((f (f e (f e (f b m))) (f (f e e) m))) ((f (f e (f b m)) (f (f e e) m))).
surgery id_r ((f (f e (f b m)) (f (f e e) m))) ((f (f e b) (f (f e e) m))).
surgery id_l ((f (f e b) (f (f e e) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_364: forall b: G, (((e <+> (e <+> m)) <+> e) <+> ((e <+> m) <+> ((e <+> e) <+> (e <+> b)))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) e) (f (f e m) (f (f e e) (f e b))))) ((f (f (f e m) e) (f (f e m) (f (f e e) (f e b))))).
surgery id_r ((f (f (f e m) e) (f (f e m) (f (f e e) (f e b))))) ((f (f e e) (f (f e m) (f (f e e) (f e b))))).
surgery id_l ((f (f e e) (f (f e m) (f (f e e) (f e b))))) ((f e (f (f e m) (f (f e e) (f e b))))).
surgery id_r ((f e (f (f e m) (f (f e e) (f e b))))) ((f e (f e (f (f e e) (f e b))))).
surgery id_l ((f e (f e (f (f e e) (f e b))))) ((f e (f (f e e) (f e b)))).
surgery id_l ((f e (f (f e e) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_365: forall b: G, (((e <+> m) <+> (b <+> ((m <+> m) <+> (m <+> m)))) <+> (e <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f b (f (f m m) (f m m)))) (f e (f e m)))) ((f (f e (f b (f (f m m) (f m m)))) (f e (f e m)))).
surgery id_r ((f (f e (f b (f (f m m) (f m m)))) (f e (f e m)))) ((f (f e (f b (f m (f m m)))) (f e (f e m)))).
surgery id_r ((f (f e (f b (f m (f m m)))) (f e (f e m)))) ((f (f e (f b (f m m))) (f e (f e m)))).
surgery id_r ((f (f e (f b (f m m))) (f e (f e m)))) ((f (f e (f b m)) (f e (f e m)))).
surgery id_r ((f (f e (f b m)) (f e (f e m)))) ((f (f e b) (f e (f e m)))).
surgery id_l ((f (f e b) (f e (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_366: forall b: G, (((((e <+> e) <+> e) <+> ((e <+> e) <+> (e <+> m))) <+> (e <+> m)) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f (f (f e e) e) (f (f e e) (f e m))) (f e m)) b)) ((f (f (f (f e e) (f (f e e) (f e m))) (f e m)) b)).
surgery id_l ((f (f (f (f e e) (f (f e e) (f e m))) (f e m)) b)) ((f (f (f e (f (f e e) (f e m))) (f e m)) b)).
surgery id_l ((f (f (f e (f (f e e) (f e m))) (f e m)) b)) ((f (f (f e (f e (f e m))) (f e m)) b)).
surgery id_l ((f (f (f e (f e (f e m))) (f e m)) b)) ((f (f (f e (f e m)) (f e m)) b)).
surgery id_l ((f (f (f e (f e m)) (f e m)) b)) ((f (f (f e m) (f e m)) b)).
surgery id_r ((f (f (f e m) (f e m)) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_367: forall b: G, ((e <+> e) <+> ((((e <+> m) <+> e) <+> ((e <+> e) <+> m)) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f (f (f e m) e) (f (f e e) m)) (f e b)))) ((f e (f (f (f (f e m) e) (f (f e e) m)) (f e b)))).
surgery id_r ((f e (f (f (f (f e m) e) (f (f e e) m)) (f e b)))) ((f e (f (f (f e e) (f (f e e) m)) (f e b)))).
surgery id_l ((f e (f (f (f e e) (f (f e e) m)) (f e b)))) ((f e (f (f e (f (f e e) m)) (f e b)))).
surgery id_l ((f e (f (f e (f (f e e) m)) (f e b)))) ((f e (f (f e (f e m)) (f e b)))).
surgery id_l ((f e (f (f e (f e m)) (f e b)))) ((f e (f (f e m) (f e b)))).
surgery id_r ((f e (f (f e m) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_368: forall b: G, ((b <+> m) <+> ((m <+> (e <+> m)) <+> ((m <+> (e <+> m)) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f m (f e m)) (f (f m (f e m)) (f e m))))) ((f b (f (f m (f e m)) (f (f m (f e m)) (f e m))))).
surgery id_l ((f b (f (f m (f e m)) (f (f m (f e m)) (f e m))))) ((f b (f (f m m) (f (f m (f e m)) (f e m))))).
surgery id_r ((f b (f (f m m) (f (f m (f e m)) (f e m))))) ((f b (f m (f (f m (f e m)) (f e m))))).
surgery id_l ((f b (f m (f (f m (f e m)) (f e m))))) ((f b (f m (f (f m m) (f e m))))).
surgery id_r ((f b (f m (f (f m m) (f e m))))) ((f b (f m (f m (f e m))))).
surgery id_l ((f b (f m (f m (f e m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_369: forall b: G, ((e <+> e) <+> ((e <+> (e <+> m)) <+> (((e <+> e) <+> b) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f e (f e m)) (f (f (f e e) b) (f m m))))) ((f e (f (f e (f e m)) (f (f (f e e) b) (f m m))))).
surgery id_l ((f e (f (f e (f e m)) (f (f (f e e) b) (f m m))))) ((f e (f (f e m) (f (f (f e e) b) (f m m))))).
surgery id_r ((f e (f (f e m) (f (f (f e e) b) (f m m))))) ((f e (f e (f (f (f e e) b) (f m m))))).
surgery id_l ((f e (f e (f (f (f e e) b) (f m m))))) ((f e (f (f (f e e) b) (f m m)))).
surgery id_l ((f e (f (f (f e e) b) (f m m)))) ((f e (f (f e b) (f m m)))).
surgery id_l ((f e (f (f e b) (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_370: forall b: G, ((e <+> ((e <+> (e <+> m)) <+> m)) <+> (e <+> ((e <+> m) <+> (e <+> b)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f e (f e m)) m)) (f e (f (f e m) (f e b))))) ((f (f e (f (f e m) m)) (f e (f (f e m) (f e b))))).
surgery id_r ((f (f e (f (f e m) m)) (f e (f (f e m) (f e b))))) ((f (f e (f e m)) (f e (f (f e m) (f e b))))).
surgery id_l ((f (f e (f e m)) (f e (f (f e m) (f e b))))) ((f (f e m) (f e (f (f e m) (f e b))))).
surgery id_r ((f (f e m) (f e (f (f e m) (f e b))))) ((f e (f e (f (f e m) (f e b))))).
surgery id_l ((f e (f e (f (f e m) (f e b))))) ((f e (f (f e m) (f e b)))).
surgery id_r ((f e (f (f e m) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_371: forall b: G, (((e <+> e) <+> m) <+> (((b <+> m) <+> m) <+> ((m <+> m) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f e e) m) (f (f (f b m) m) (f (f m m) (f e m))))) ((f (f e e) (f (f (f b m) m) (f (f m m) (f e m))))).
surgery id_l ((f (f e e) (f (f (f b m) m) (f (f m m) (f e m))))) ((f e (f (f (f b m) m) (f (f m m) (f e m))))).
surgery id_r ((f e (f (f (f b m) m) (f (f m m) (f e m))))) ((f e (f (f b m) (f (f m m) (f e m))))).
surgery id_r ((f e (f (f b m) (f (f m m) (f e m))))) ((f e (f b (f (f m m) (f e m))))).
surgery id_r ((f e (f b (f (f m m) (f e m))))) ((f e (f b (f m (f e m))))).
surgery id_l ((f e (f b (f m (f e m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_372: forall b: G, ((((e <+> (m <+> m)) <+> b) <+> m) <+> (m <+> (m <+> (e <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e (f m m)) b) m) (f m (f m (f e (f e m)))))) ((f (f (f e (f m m)) b) (f m (f m (f e (f e m)))))).
surgery id_r ((f (f (f e (f m m)) b) (f m (f m (f e (f e m)))))) ((f (f (f e m) b) (f m (f m (f e (f e m)))))).
surgery id_r ((f (f (f e m) b) (f m (f m (f e (f e m)))))) ((f (f e b) (f m (f m (f e (f e m)))))).
surgery id_l ((f (f e b) (f m (f m (f e (f e m)))))) ((f b (f m (f m (f e (f e m)))))).
surgery id_l ((f b (f m (f m (f e (f e m)))))) ((f b (f m (f m (f e m))))).
surgery id_l ((f b (f m (f m (f e m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_373: forall b: G, ((((e <+> m) <+> (m <+> m)) <+> b) <+> (e <+> ((m <+> m) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f m m)) b) (f e (f (f m m) (f e m))))) ((f (f (f e (f m m)) b) (f e (f (f m m) (f e m))))).
surgery id_r ((f (f (f e (f m m)) b) (f e (f (f m m) (f e m))))) ((f (f (f e m) b) (f e (f (f m m) (f e m))))).
surgery id_r ((f (f (f e m) b) (f e (f (f m m) (f e m))))) ((f (f e b) (f e (f (f m m) (f e m))))).
surgery id_l ((f (f e b) (f e (f (f m m) (f e m))))) ((f b (f e (f (f m m) (f e m))))).
surgery id_l ((f b (f e (f (f m m) (f e m))))) ((f b (f (f m m) (f e m)))).
surgery id_r ((f b (f (f m m) (f e m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_374: forall b: G, ((e <+> ((e <+> m) <+> (m <+> m))) <+> (b <+> ((e <+> e) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f e m) (f m m))) (f b (f (f e e) (f m m))))) ((f (f e (f e (f m m))) (f b (f (f e e) (f m m))))).
surgery id_l ((f (f e (f e (f m m))) (f b (f (f e e) (f m m))))) ((f (f e (f m m)) (f b (f (f e e) (f m m))))).
surgery id_r ((f (f e (f m m)) (f b (f (f e e) (f m m))))) ((f (f e m) (f b (f (f e e) (f m m))))).
surgery id_r ((f (f e m) (f b (f (f e e) (f m m))))) ((f e (f b (f (f e e) (f m m))))).
surgery id_l ((f e (f b (f (f e e) (f m m))))) ((f e (f b (f e (f m m))))).
surgery id_l ((f e (f b (f e (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_375: forall b: G, ((e <+> m) <+> ((((e <+> (e <+> m)) <+> m) <+> ((e <+> m) <+> m)) <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f (f (f e (f e m)) m) (f (f e m) m)) b))) ((f e (f (f (f (f e (f e m)) m) (f (f e m) m)) b))).
surgery id_r ((f e (f (f (f (f e (f e m)) m) (f (f e m) m)) b))) ((f e (f (f (f e (f e m)) (f (f e m) m)) b))).
surgery id_l ((f e (f (f (f e (f e m)) (f (f e m) m)) b))) ((f e (f (f (f e m) (f (f e m) m)) b))).
surgery id_r ((f e (f (f (f e m) (f (f e m) m)) b))) ((f e (f (f e (f (f e m) m)) b))).
surgery id_r ((f e (f (f e (f (f e m) m)) b))) ((f e (f (f e (f e m)) b))).
surgery id_l ((f e (f (f e (f e m)) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_376: forall b: G, (((e <+> (e <+> m)) <+> (e <+> b)) <+> (m <+> (e <+> (m <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f e b)) (f m (f e (f m (f e m)))))) ((f (f (f e m) (f e b)) (f m (f e (f m (f e m)))))).
surgery id_r ((f (f (f e m) (f e b)) (f m (f e (f m (f e m)))))) ((f (f e (f e b)) (f m (f e (f m (f e m)))))).
surgery id_l ((f (f e (f e b)) (f m (f e (f m (f e m)))))) ((f (f e b) (f m (f e (f m (f e m)))))).
surgery id_l ((f (f e b) (f m (f e (f m (f e m)))))) ((f b (f m (f e (f m (f e m)))))).
surgery id_l ((f b (f m (f e (f m (f e m)))))) ((f b (f m (f m (f e m))))).
surgery id_l ((f b (f m (f m (f e m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_377: forall b: G, ((((e <+> e) <+> m) <+> ((e <+> e) <+> ((e <+> e) <+> e))) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) (f (f e e) (f (f e e) e))) (f e b))) ((f (f (f e e) (f (f e e) (f (f e e) e))) (f e b))).
surgery id_l ((f (f (f e e) (f (f e e) (f (f e e) e))) (f e b))) ((f (f e (f (f e e) (f (f e e) e))) (f e b))).
surgery id_l ((f (f e (f (f e e) (f (f e e) e))) (f e b))) ((f (f e (f e (f (f e e) e))) (f e b))).
surgery id_l ((f (f e (f e (f (f e e) e))) (f e b))) ((f (f e (f (f e e) e)) (f e b))).
surgery id_l ((f (f e (f (f e e) e)) (f e b))) ((f (f e (f e e)) (f e b))).
surgery id_l ((f (f e (f e e)) (f e b))) ((f (f e e) (f e b))).
surgery id_l ((f (f e e) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_378: forall b: G, (b <+> (((e <+> m) <+> (e <+> (e <+> (m <+> m)))) <+> ((e <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f b (f (f (f e m) (f e (f e (f m m)))) (f (f e m) m)))) ((f b (f (f e (f e (f e (f m m)))) (f (f e m) m)))).
surgery id_l ((f b (f (f e (f e (f e (f m m)))) (f (f e m) m)))) ((f b (f (f e (f e (f m m))) (f (f e m) m)))).
surgery id_l ((f b (f (f e (f e (f m m))) (f (f e m) m)))) ((f b (f (f e (f m m)) (f (f e m) m)))).
surgery id_r ((f b (f (f e (f m m)) (f (f e m) m)))) ((f b (f (f e m) (f (f e m) m)))).
surgery id_r ((f b (f (f e m) (f (f e m) m)))) ((f b (f e (f (f e m) m)))).
surgery id_l ((f b (f e (f (f e m) m)))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_379: forall b: G, (((e <+> (e <+> ((e <+> b) <+> (e <+> m)))) <+> (m <+> m)) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e (f (f e b) (f e m)))) (f m m)) (f e m))) ((f (f (f e (f (f e b) (f e m))) (f m m)) (f e m))).
surgery id_l ((f (f (f e (f (f e b) (f e m))) (f m m)) (f e m))) ((f (f (f e (f b (f e m))) (f m m)) (f e m))).
surgery id_l ((f (f (f e (f b (f e m))) (f m m)) (f e m))) ((f (f (f e (f b m)) (f m m)) (f e m))).
surgery id_r ((f (f (f e (f b m)) (f m m)) (f e m))) ((f (f (f e b) (f m m)) (f e m))).
surgery id_l ((f (f (f e b) (f m m)) (f e m))) ((f (f b (f m m)) (f e m))).
surgery id_r ((f (f b (f m m)) (f e m))) ((f (f b m) (f e m))).
surgery id_r ((f (f b m) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_380: forall b: G, (b <+> ((e <+> e) <+> ((e <+> (m <+> (m <+> m))) <+> ((e <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_l ((f b (f (f e e) (f (f e (f m (f m m))) (f (f e m) m))))) ((f b (f e (f (f e (f m (f m m))) (f (f e m) m))))).
surgery id_l ((f b (f e (f (f e (f m (f m m))) (f (f e m) m))))) ((f b (f (f e (f m (f m m))) (f (f e m) m)))).
surgery id_r ((f b (f (f e (f m (f m m))) (f (f e m) m)))) ((f b (f (f e (f m m)) (f (f e m) m)))).
surgery id_r ((f b (f (f e (f m m)) (f (f e m) m)))) ((f b (f (f e m) (f (f e m) m)))).
surgery id_r ((f b (f (f e m) (f (f e m) m)))) ((f b (f e (f (f e m) m)))).
surgery id_l ((f b (f e (f (f e m) m)))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_381: forall b: G, (((e <+> e) <+> ((e <+> m) <+> (e <+> (e <+> b)))) <+> (e <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f e m) (f e (f e b)))) (f e (f m m)))) ((f (f e (f (f e m) (f e (f e b)))) (f e (f m m)))).
surgery id_r ((f (f e (f (f e m) (f e (f e b)))) (f e (f m m)))) ((f (f e (f e (f e (f e b)))) (f e (f m m)))).
surgery id_l ((f (f e (f e (f e (f e b)))) (f e (f m m)))) ((f (f e (f e (f e b))) (f e (f m m)))).
surgery id_l ((f (f e (f e (f e b))) (f e (f m m)))) ((f (f e (f e b)) (f e (f m m)))).
surgery id_l ((f (f e (f e b)) (f e (f m m)))) ((f (f e b) (f e (f m m)))).
surgery id_l ((f (f e b) (f e (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_382: forall b: G, ((((e <+> b) <+> ((e <+> (e <+> (e <+> m))) <+> (m <+> m))) <+> m) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e b) (f (f e (f e (f e m))) (f m m))) m) m)) ((f (f (f e b) (f (f e (f e (f e m))) (f m m))) m)).
surgery id_r ((f (f (f e b) (f (f e (f e (f e m))) (f m m))) m)) ((f (f e b) (f (f e (f e (f e m))) (f m m)))).
surgery id_l ((f (f e b) (f (f e (f e (f e m))) (f m m)))) ((f b (f (f e (f e (f e m))) (f m m)))).
surgery id_l ((f b (f (f e (f e (f e m))) (f m m)))) ((f b (f (f e (f e m)) (f m m)))).
surgery id_l ((f b (f (f e (f e m)) (f m m)))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_383: forall b: G, (b <+> ((m <+> (e <+> m)) <+> (m <+> (((e <+> m) <+> m) <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_l ((f b (f (f m (f e m)) (f m (f (f (f e m) m) (f m m)))))) ((f b (f (f m m) (f m (f (f (f e m) m) (f m m)))))).
surgery id_r ((f b (f (f m m) (f m (f (f (f e m) m) (f m m)))))) ((f b (f m (f m (f (f (f e m) m) (f m m)))))).
surgery id_r ((f b (f m (f m (f (f (f e m) m) (f m m)))))) ((f b (f m (f m (f (f e m) (f m m)))))).
surgery id_r ((f b (f m (f m (f (f e m) (f m m)))))) ((f b (f m (f m (f e (f m m)))))).
surgery id_l ((f b (f m (f m (f e (f m m)))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_384: forall b: G, (((e <+> m) <+> ((b <+> m) <+> m)) <+> (e <+> (((e <+> e) <+> e) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f (f b m) m)) (f e (f (f (f e e) e) m)))) ((f (f e (f (f b m) m)) (f e (f (f (f e e) e) m)))).
surgery id_r ((f (f e (f (f b m) m)) (f e (f (f (f e e) e) m)))) ((f (f e (f b m)) (f e (f (f (f e e) e) m)))).
surgery id_r ((f (f e (f b m)) (f e (f (f (f e e) e) m)))) ((f (f e b) (f e (f (f (f e e) e) m)))).
surgery id_l ((f (f e b) (f e (f (f (f e e) e) m)))) ((f b (f e (f (f (f e e) e) m)))).
surgery id_l ((f b (f e (f (f (f e e) e) m)))) ((f b (f (f (f e e) e) m))).
surgery id_l ((f b (f (f (f e e) e) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_385: forall b: G, ((e <+> ((b <+> m) <+> ((m <+> m) <+> (((e <+> m) <+> m) <+> m)))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f b m) (f (f m m) (f (f (f e m) m) m)))) m)) ((f e (f (f b m) (f (f m m) (f (f (f e m) m) m))))).
surgery id_r ((f e (f (f b m) (f (f m m) (f (f (f e m) m) m))))) ((f e (f b (f (f m m) (f (f (f e m) m) m))))).
surgery id_r ((f e (f b (f (f m m) (f (f (f e m) m) m))))) ((f e (f b (f m (f (f (f e m) m) m))))).
surgery id_r ((f e (f b (f m (f (f (f e m) m) m))))) ((f e (f b (f m (f (f e m) m))))).
surgery id_r ((f e (f b (f m (f (f e m) m))))) ((f e (f b (f m (f e m))))).
surgery id_l ((f e (f b (f m (f e m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_386: forall b: G, ((b <+> (((e <+> e) <+> e) <+> (e <+> ((m <+> m) <+> m)))) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f b (f (f (f e e) e) (f e (f (f m m) m)))) (f e m))) ((f (f b (f (f e e) (f e (f (f m m) m)))) (f e m))).
surgery id_l ((f (f b (f (f e e) (f e (f (f m m) m)))) (f e m))) ((f (f b (f e (f e (f (f m m) m)))) (f e m))).
surgery id_l ((f (f b (f e (f e (f (f m m) m)))) (f e m))) ((f (f b (f e (f (f m m) m))) (f e m))).
surgery id_l ((f (f b (f e (f (f m m) m))) (f e m))) ((f (f b (f (f m m) m)) (f e m))).
surgery id_r ((f (f b (f (f m m) m)) (f e m))) ((f (f b (f m m)) (f e m))).
surgery id_r ((f (f b (f m m)) (f e m))) ((f (f b m) (f e m))).
surgery id_r ((f (f b m) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_387: forall b: G, (e <+> (((((e <+> m) <+> e) <+> (e <+> m)) <+> (e <+> b)) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f e (f (f (f (f (f e m) e) (f e m)) (f e b)) (f m m)))) ((f e (f (f (f (f e e) (f e m)) (f e b)) (f m m)))).
surgery id_l ((f e (f (f (f (f e e) (f e m)) (f e b)) (f m m)))) ((f e (f (f (f e (f e m)) (f e b)) (f m m)))).
surgery id_l ((f e (f (f (f e (f e m)) (f e b)) (f m m)))) ((f e (f (f (f e m) (f e b)) (f m m)))).
surgery id_r ((f e (f (f (f e m) (f e b)) (f m m)))) ((f e (f (f e (f e b)) (f m m)))).
surgery id_l ((f e (f (f e (f e b)) (f m m)))) ((f e (f (f e b) (f m m)))).
surgery id_l ((f e (f (f e b) (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_388: forall b: G, ((((e <+> (e <+> (b <+> m))) <+> (e <+> m)) <+> m) <+> (e <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e (f e (f b m))) (f e m)) m) (f e (f m m)))) ((f (f (f e (f e (f b m))) (f e m)) (f e (f m m)))).
surgery id_l ((f (f (f e (f e (f b m))) (f e m)) (f e (f m m)))) ((f (f (f e (f b m)) (f e m)) (f e (f m m)))).
surgery id_r ((f (f (f e (f b m)) (f e m)) (f e (f m m)))) ((f (f (f e b) (f e m)) (f e (f m m)))).
surgery id_l ((f (f (f e b) (f e m)) (f e (f m m)))) ((f (f b (f e m)) (f e (f m m)))).
surgery id_l ((f (f b (f e m)) (f e (f m m)))) ((f (f b m) (f e (f m m)))).
surgery id_r ((f (f b m) (f e (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_389: forall b: G, ((b <+> ((e <+> (e <+> e)) <+> ((e <+> (e <+> m)) <+> m))) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f b (f (f e (f e e)) (f (f e (f e m)) m))) (f m m))) ((f (f b (f (f e e) (f (f e (f e m)) m))) (f m m))).
surgery id_l ((f (f b (f (f e e) (f (f e (f e m)) m))) (f m m))) ((f (f b (f e (f (f e (f e m)) m))) (f m m))).
surgery id_l ((f (f b (f e (f (f e (f e m)) m))) (f m m))) ((f (f b (f (f e (f e m)) m)) (f m m))).
surgery id_l ((f (f b (f (f e (f e m)) m)) (f m m))) ((f (f b (f (f e m) m)) (f m m))).
surgery id_r ((f (f b (f (f e m) m)) (f m m))) ((f (f b (f e m)) (f m m))).
surgery id_l ((f (f b (f e m)) (f m m))) ((f (f b m) (f m m))).
surgery id_r ((f (f b m) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_390: forall b: G, (((((e <+> m) <+> (e <+> (m <+> m))) <+> (m <+> m)) <+> e) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e m) (f e (f m m))) (f m m)) e) (f e b))) ((f (f (f (f e (f e (f m m))) (f m m)) e) (f e b))).
surgery id_l ((f (f (f (f e (f e (f m m))) (f m m)) e) (f e b))) ((f (f (f (f e (f m m)) (f m m)) e) (f e b))).
surgery id_r ((f (f (f (f e (f m m)) (f m m)) e) (f e b))) ((f (f (f (f e m) (f m m)) e) (f e b))).
surgery id_r ((f (f (f (f e m) (f m m)) e) (f e b))) ((f (f (f e (f m m)) e) (f e b))).
surgery id_r ((f (f (f e (f m m)) e) (f e b))) ((f (f (f e m) e) (f e b))).
surgery id_r ((f (f (f e m) e) (f e b))) ((f (f e e) (f e b))).
surgery id_l ((f (f e e) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_391: forall b: G, (((e <+> ((e <+> m) <+> b)) <+> (m <+> (m <+> m))) <+> ((e <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f e m) b)) (f m (f m m))) (f (f e m) m))) ((f (f (f e (f e b)) (f m (f m m))) (f (f e m) m))).
surgery id_l ((f (f (f e (f e b)) (f m (f m m))) (f (f e m) m))) ((f (f (f e b) (f m (f m m))) (f (f e m) m))).
surgery id_l ((f (f (f e b) (f m (f m m))) (f (f e m) m))) ((f (f b (f m (f m m))) (f (f e m) m))).
surgery id_r ((f (f b (f m (f m m))) (f (f e m) m))) ((f (f b (f m m)) (f (f e m) m))).
surgery id_r ((f (f b (f m m)) (f (f e m) m))) ((f (f b m) (f (f e m) m))).
surgery id_r ((f (f b m) (f (f e m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_392: forall b: G, ((((e <+> m) <+> (e <+> m)) <+> ((e <+> m) <+> b)) <+> (m <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f e m)) (f (f e m) b)) (f m (f m m)))) ((f (f (f e (f e m)) (f (f e m) b)) (f m (f m m)))).
surgery id_l ((f (f (f e (f e m)) (f (f e m) b)) (f m (f m m)))) ((f (f (f e m) (f (f e m) b)) (f m (f m m)))).
surgery id_r ((f (f (f e m) (f (f e m) b)) (f m (f m m)))) ((f (f e (f (f e m) b)) (f m (f m m)))).
surgery id_r ((f (f e (f (f e m) b)) (f m (f m m)))) ((f (f e (f e b)) (f m (f m m)))).
surgery id_l ((f (f e (f e b)) (f m (f m m)))) ((f (f e b) (f m (f m m)))).
surgery id_l ((f (f e b) (f m (f m m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_393: forall b: G, ((e <+> (e <+> m)) <+> ((e <+> ((e <+> m) <+> e)) <+> ((e <+> b) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e m)) (f (f e (f (f e m) e)) (f (f e b) m)))) ((f (f e m) (f (f e (f (f e m) e)) (f (f e b) m)))).
surgery id_r ((f (f e m) (f (f e (f (f e m) e)) (f (f e b) m)))) ((f e (f (f e (f (f e m) e)) (f (f e b) m)))).
surgery id_r ((f e (f (f e (f (f e m) e)) (f (f e b) m)))) ((f e (f (f e (f e e)) (f (f e b) m)))).
surgery id_l ((f e (f (f e (f e e)) (f (f e b) m)))) ((f e (f (f e e) (f (f e b) m)))).
surgery id_l ((f e (f (f e e) (f (f e b) m)))) ((f e (f e (f (f e b) m)))).
surgery id_l ((f e (f e (f (f e b) m)))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_394: forall b: G, ((e <+> (e <+> e)) <+> ((b <+> (m <+> m)) <+> (e <+> (e <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e e)) (f (f b (f m m)) (f e (f e (f m m)))))) ((f (f e e) (f (f b (f m m)) (f e (f e (f m m)))))).
surgery id_l ((f (f e e) (f (f b (f m m)) (f e (f e (f m m)))))) ((f e (f (f b (f m m)) (f e (f e (f m m)))))).
surgery id_r ((f e (f (f b (f m m)) (f e (f e (f m m)))))) ((f e (f (f b m) (f e (f e (f m m)))))).
surgery id_r ((f e (f (f b m) (f e (f e (f m m)))))) ((f e (f b (f e (f e (f m m)))))).
surgery id_l ((f e (f b (f e (f e (f m m)))))) ((f e (f b (f e (f m m))))).
surgery id_l ((f e (f b (f e (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_395: forall b: G, (((e <+> ((e <+> m) <+> (((e <+> m) <+> e) <+> b))) <+> m) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f e m) (f (f (f e m) e) b))) m) (f m m))) ((f (f e (f (f e m) (f (f (f e m) e) b))) (f m m))).
surgery id_r ((f (f e (f (f e m) (f (f (f e m) e) b))) (f m m))) ((f (f e (f e (f (f (f e m) e) b))) (f m m))).
surgery id_l ((f (f e (f e (f (f (f e m) e) b))) (f m m))) ((f (f e (f (f (f e m) e) b)) (f m m))).
surgery id_r ((f (f e (f (f (f e m) e) b)) (f m m))) ((f (f e (f (f e e) b)) (f m m))).
surgery id_l ((f (f e (f (f e e) b)) (f m m))) ((f (f e (f e b)) (f m m))).
surgery id_l ((f (f e (f e b)) (f m m))) ((f (f e b) (f m m))).
surgery id_l ((f (f e b) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_396: forall b: G, (((e <+> (b <+> m)) <+> ((((e <+> m) <+> m) <+> m) <+> m)) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f b m)) (f (f (f (f e m) m) m) m)) (f m m))) ((f (f (f e b) (f (f (f (f e m) m) m) m)) (f m m))).
surgery id_l ((f (f (f e b) (f (f (f (f e m) m) m) m)) (f m m))) ((f (f b (f (f (f (f e m) m) m) m)) (f m m))).
surgery id_r ((f (f b (f (f (f (f e m) m) m) m)) (f m m))) ((f (f b (f (f (f e m) m) m)) (f m m))).
surgery id_r ((f (f b (f (f (f e m) m) m)) (f m m))) ((f (f b (f (f e m) m)) (f m m))).
surgery id_r ((f (f b (f (f e m) m)) (f m m))) ((f (f b (f e m)) (f m m))).
surgery id_l ((f (f b (f e m)) (f m m))) ((f (f b m) (f m m))).
surgery id_r ((f (f b m) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_397: forall b: G, (((e <+> e) <+> (e <+> m)) <+> (((b <+> m) <+> ((e <+> e) <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f e m)) (f (f (f b m) (f (f e e) m)) m))) ((f (f e (f e m)) (f (f (f b m) (f (f e e) m)) m))).
surgery id_l ((f (f e (f e m)) (f (f (f b m) (f (f e e) m)) m))) ((f (f e m) (f (f (f b m) (f (f e e) m)) m))).
surgery id_r ((f (f e m) (f (f (f b m) (f (f e e) m)) m))) ((f e (f (f (f b m) (f (f e e) m)) m))).
surgery id_r ((f e (f (f (f b m) (f (f e e) m)) m))) ((f e (f (f b (f (f e e) m)) m))).
surgery id_l ((f e (f (f b (f (f e e) m)) m))) ((f e (f (f b (f e m)) m))).
surgery id_l ((f e (f (f b (f e m)) m))) ((f e (f (f b m) m))).
surgery id_r ((f e (f (f b m) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_398: forall b: G, (e <+> ((e <+> (b <+> m)) <+> (m <+> ((e <+> m) <+> ((e <+> m) <+> m))))) = b.
Proof.
intros.
surgery id_r ((f e (f (f e (f b m)) (f m (f (f e m) (f (f e m) m)))))) ((f e (f (f e b) (f m (f (f e m) (f (f e m) m)))))).
surgery id_l ((f e (f (f e b) (f m (f (f e m) (f (f e m) m)))))) ((f e (f b (f m (f (f e m) (f (f e m) m)))))).
surgery id_r ((f e (f b (f m (f (f e m) (f (f e m) m)))))) ((f e (f b (f m (f e (f (f e m) m)))))).
surgery id_l ((f e (f b (f m (f e (f (f e m) m)))))) ((f e (f b (f m (f (f e m) m))))).
surgery id_r ((f e (f b (f m (f (f e m) m))))) ((f e (f b (f m (f e m))))).
surgery id_l ((f e (f b (f m (f e m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_399: forall b: G, ((b <+> (e <+> m)) <+> (((e <+> m) <+> ((e <+> m) <+> (m <+> m))) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f b (f e m)) (f (f (f e m) (f (f e m) (f m m))) m))) ((f (f b m) (f (f (f e m) (f (f e m) (f m m))) m))).
surgery id_r ((f (f b m) (f (f (f e m) (f (f e m) (f m m))) m))) ((f b (f (f (f e m) (f (f e m) (f m m))) m))).
surgery id_r ((f b (f (f (f e m) (f (f e m) (f m m))) m))) ((f b (f (f e (f (f e m) (f m m))) m))).
surgery id_r ((f b (f (f e (f (f e m) (f m m))) m))) ((f b (f (f e (f e (f m m))) m))).
surgery id_l ((f b (f (f e (f e (f m m))) m))) ((f b (f (f e (f m m)) m))).
surgery id_r ((f b (f (f e (f m m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_400: forall b: G, (b <+> ((((e <+> m) <+> ((e <+> (e <+> m)) <+> m)) <+> (e <+> e)) <+> m)) = b.
Proof.
intros.
surgery id_r ((f b (f (f (f (f e m) (f (f e (f e m)) m)) (f e e)) m))) ((f b (f (f (f e (f (f e (f e m)) m)) (f e e)) m))).
surgery id_l ((f b (f (f (f e (f (f e (f e m)) m)) (f e e)) m))) ((f b (f (f (f e (f (f e m) m)) (f e e)) m))).
surgery id_r ((f b (f (f (f e (f (f e m) m)) (f e e)) m))) ((f b (f (f (f e (f e m)) (f e e)) m))).
surgery id_l ((f b (f (f (f e (f e m)) (f e e)) m))) ((f b (f (f (f e m) (f e e)) m))).
surgery id_r ((f b (f (f (f e m) (f e e)) m))) ((f b (f (f e (f e e)) m))).
surgery id_l ((f b (f (f e (f e e)) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_401: forall b: G, ((((e <+> e) <+> (e <+> (e <+> m))) <+> (e <+> m)) <+> (b <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) (f e (f e m))) (f e m)) (f b (f m m)))) ((f (f (f e (f e (f e m))) (f e m)) (f b (f m m)))).
surgery id_l ((f (f (f e (f e (f e m))) (f e m)) (f b (f m m)))) ((f (f (f e (f e m)) (f e m)) (f b (f m m)))).
surgery id_l ((f (f (f e (f e m)) (f e m)) (f b (f m m)))) ((f (f (f e m) (f e m)) (f b (f m m)))).
surgery id_r ((f (f (f e m) (f e m)) (f b (f m m)))) ((f (f e (f e m)) (f b (f m m)))).
surgery id_l ((f (f e (f e m)) (f b (f m m)))) ((f (f e m) (f b (f m m)))).
surgery id_r ((f (f e m) (f b (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_402: forall b: G, (b <+> (((e <+> e) <+> m) <+> ((((e <+> m) <+> e) <+> (m <+> m)) <+> m))) = b.
Proof.
intros.
surgery id_r ((f b (f (f (f e e) m) (f (f (f (f e m) e) (f m m)) m)))) ((f b (f (f e e) (f (f (f (f e m) e) (f m m)) m)))).
surgery id_l ((f b (f (f e e) (f (f (f (f e m) e) (f m m)) m)))) ((f b (f e (f (f (f (f e m) e) (f m m)) m)))).
surgery id_l ((f b (f e (f (f (f (f e m) e) (f m m)) m)))) ((f b (f (f (f (f e m) e) (f m m)) m))).
surgery id_r ((f b (f (f (f (f e m) e) (f m m)) m))) ((f b (f (f (f e e) (f m m)) m))).
surgery id_l ((f b (f (f (f e e) (f m m)) m))) ((f b (f (f e (f m m)) m))).
surgery id_r ((f b (f (f e (f m m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_403: forall b: G, ((((e <+> e) <+> ((e <+> m) <+> (b <+> m))) <+> m) <+> (m <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) (f (f e m) (f b m))) m) (f m (f e m)))) ((f (f (f e e) (f (f e m) (f b m))) (f m (f e m)))).
surgery id_l ((f (f (f e e) (f (f e m) (f b m))) (f m (f e m)))) ((f (f e (f (f e m) (f b m))) (f m (f e m)))).
surgery id_r ((f (f e (f (f e m) (f b m))) (f m (f e m)))) ((f (f e (f e (f b m))) (f m (f e m)))).
surgery id_l ((f (f e (f e (f b m))) (f m (f e m)))) ((f (f e (f b m)) (f m (f e m)))).
surgery id_r ((f (f e (f b m)) (f m (f e m)))) ((f (f e b) (f m (f e m)))).
surgery id_l ((f (f e b) (f m (f e m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_404: forall b: G, (((e <+> e) <+> ((e <+> e) <+> (b <+> m))) <+> ((e <+> m) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f e e) (f b m))) (f (f e m) (f m m)))) ((f (f e (f (f e e) (f b m))) (f (f e m) (f m m)))).
surgery id_l ((f (f e (f (f e e) (f b m))) (f (f e m) (f m m)))) ((f (f e (f e (f b m))) (f (f e m) (f m m)))).
surgery id_l ((f (f e (f e (f b m))) (f (f e m) (f m m)))) ((f (f e (f b m)) (f (f e m) (f m m)))).
surgery id_r ((f (f e (f b m)) (f (f e m) (f m m)))) ((f (f e b) (f (f e m) (f m m)))).
surgery id_l ((f (f e b) (f (f e m) (f m m)))) ((f b (f (f e m) (f m m)))).
surgery id_r ((f b (f (f e m) (f m m)))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_405: forall b: G, (((e <+> (e <+> m)) <+> ((e <+> ((e <+> e) <+> e)) <+> (e <+> m))) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f (f e (f (f e e) e)) (f e m))) b)) ((f (f (f e m) (f (f e (f (f e e) e)) (f e m))) b)).
surgery id_r ((f (f (f e m) (f (f e (f (f e e) e)) (f e m))) b)) ((f (f e (f (f e (f (f e e) e)) (f e m))) b)).
surgery id_l ((f (f e (f (f e (f (f e e) e)) (f e m))) b)) ((f (f e (f (f e (f e e)) (f e m))) b)).
surgery id_l ((f (f e (f (f e (f e e)) (f e m))) b)) ((f (f e (f (f e e) (f e m))) b)).
surgery id_l ((f (f e (f (f e e) (f e m))) b)) ((f (f e (f e (f e m))) b)).
surgery id_l ((f (f e (f e (f e m))) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_406: forall b: G, (((e <+> (e <+> (e <+> m))) <+> (m <+> m)) <+> ((e <+> b) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e (f e m))) (f m m)) (f (f e b) (f m m)))) ((f (f (f e (f e m)) (f m m)) (f (f e b) (f m m)))).
surgery id_l ((f (f (f e (f e m)) (f m m)) (f (f e b) (f m m)))) ((f (f (f e m) (f m m)) (f (f e b) (f m m)))).
surgery id_r ((f (f (f e m) (f m m)) (f (f e b) (f m m)))) ((f (f e (f m m)) (f (f e b) (f m m)))).
surgery id_r ((f (f e (f m m)) (f (f e b) (f m m)))) ((f (f e m) (f (f e b) (f m m)))).
surgery id_r ((f (f e m) (f (f e b) (f m m)))) ((f e (f (f e b) (f m m)))).
surgery id_l ((f e (f (f e b) (f m m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_407: forall b: G, ((b <+> ((m <+> m) <+> (m <+> (e <+> (m <+> m))))) <+> (m <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b (f (f m m) (f m (f e (f m m))))) (f m (f m m)))) ((f (f b (f m (f m (f e (f m m))))) (f m (f m m)))).
surgery id_l ((f (f b (f m (f m (f e (f m m))))) (f m (f m m)))) ((f (f b (f m (f m (f m m)))) (f m (f m m)))).
surgery id_r ((f (f b (f m (f m (f m m)))) (f m (f m m)))) ((f (f b (f m (f m m))) (f m (f m m)))).
surgery id_r ((f (f b (f m (f m m))) (f m (f m m)))) ((f (f b (f m m)) (f m (f m m)))).
surgery id_r ((f (f b (f m m)) (f m (f m m)))) ((f (f b m) (f m (f m m)))).
surgery id_r ((f (f b m) (f m (f m m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_408: forall b: G, ((((e <+> m) <+> ((e <+> e) <+> (e <+> b))) <+> (m <+> m)) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f (f e e) (f e b))) (f m m)) (f e m))) ((f (f (f e (f (f e e) (f e b))) (f m m)) (f e m))).
surgery id_l ((f (f (f e (f (f e e) (f e b))) (f m m)) (f e m))) ((f (f (f e (f e (f e b))) (f m m)) (f e m))).
surgery id_l ((f (f (f e (f e (f e b))) (f m m)) (f e m))) ((f (f (f e (f e b)) (f m m)) (f e m))).
surgery id_l ((f (f (f e (f e b)) (f m m)) (f e m))) ((f (f (f e b) (f m m)) (f e m))).
surgery id_l ((f (f (f e b) (f m m)) (f e m))) ((f (f b (f m m)) (f e m))).
surgery id_r ((f (f b (f m m)) (f e m))) ((f (f b m) (f e m))).
surgery id_r ((f (f b m) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_409: forall b: G, ((b <+> (m <+> (e <+> m))) <+> (((((e <+> m) <+> e) <+> m) <+> e) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f b (f m (f e m))) (f (f (f (f (f e m) e) m) e) m))) ((f (f b (f m m)) (f (f (f (f (f e m) e) m) e) m))).
surgery id_r ((f (f b (f m m)) (f (f (f (f (f e m) e) m) e) m))) ((f (f b m) (f (f (f (f (f e m) e) m) e) m))).
surgery id_r ((f (f b m) (f (f (f (f (f e m) e) m) e) m))) ((f b (f (f (f (f (f e m) e) m) e) m))).
surgery id_r ((f b (f (f (f (f (f e m) e) m) e) m))) ((f b (f (f (f (f e m) e) e) m))).
surgery id_r ((f b (f (f (f (f e m) e) e) m))) ((f b (f (f (f e e) e) m))).
surgery id_l ((f b (f (f (f e e) e) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_410: forall b: G, ((b <+> (m <+> m)) <+> ((e <+> m) <+> (((e <+> e) <+> m) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f b (f m m)) (f (f e m) (f (f (f e e) m) (f e m))))) ((f (f b m) (f (f e m) (f (f (f e e) m) (f e m))))).
surgery id_r ((f (f b m) (f (f e m) (f (f (f e e) m) (f e m))))) ((f b (f (f e m) (f (f (f e e) m) (f e m))))).
surgery id_r ((f b (f (f e m) (f (f (f e e) m) (f e m))))) ((f b (f e (f (f (f e e) m) (f e m))))).
surgery id_l ((f b (f e (f (f (f e e) m) (f e m))))) ((f b (f (f (f e e) m) (f e m)))).
surgery id_r ((f b (f (f (f e e) m) (f e m)))) ((f b (f (f e e) (f e m)))).
surgery id_l ((f b (f (f e e) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_411: forall b: G, ((((e <+> m) <+> m) <+> ((m <+> m) <+> m)) <+> (e <+> ((e <+> m) <+> b))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) m) (f (f m m) m)) (f e (f (f e m) b)))) ((f (f (f e m) (f (f m m) m)) (f e (f (f e m) b)))).
surgery id_r ((f (f (f e m) (f (f m m) m)) (f e (f (f e m) b)))) ((f (f e (f (f m m) m)) (f e (f (f e m) b)))).
surgery id_r ((f (f e (f (f m m) m)) (f e (f (f e m) b)))) ((f (f e (f m m)) (f e (f (f e m) b)))).
surgery id_r ((f (f e (f m m)) (f e (f (f e m) b)))) ((f (f e m) (f e (f (f e m) b)))).
surgery id_r ((f (f e m) (f e (f (f e m) b)))) ((f e (f e (f (f e m) b)))).
surgery id_l ((f e (f e (f (f e m) b)))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_412: forall b: G, ((((e <+> m) <+> (m <+> m)) <+> b) <+> ((e <+> m) <+> ((e <+> e) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) (f m m)) b) (f (f e m) (f (f e e) m)))) ((f (f (f e (f m m)) b) (f (f e m) (f (f e e) m)))).
surgery id_r ((f (f (f e (f m m)) b) (f (f e m) (f (f e e) m)))) ((f (f (f e m) b) (f (f e m) (f (f e e) m)))).
surgery id_r ((f (f (f e m) b) (f (f e m) (f (f e e) m)))) ((f (f e b) (f (f e m) (f (f e e) m)))).
surgery id_l ((f (f e b) (f (f e m) (f (f e e) m)))) ((f b (f (f e m) (f (f e e) m)))).
surgery id_r ((f b (f (f e m) (f (f e e) m)))) ((f b (f e (f (f e e) m)))).
surgery id_l ((f b (f e (f (f e e) m)))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_413: forall b: G, (((e <+> e) <+> ((e <+> b) <+> m)) <+> ((m <+> (m <+> m)) <+> (m <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f e b) m)) (f (f m (f m m)) (f m m)))) ((f (f e (f (f e b) m)) (f (f m (f m m)) (f m m)))).
surgery id_l ((f (f e (f (f e b) m)) (f (f m (f m m)) (f m m)))) ((f (f e (f b m)) (f (f m (f m m)) (f m m)))).
surgery id_r ((f (f e (f b m)) (f (f m (f m m)) (f m m)))) ((f (f e b) (f (f m (f m m)) (f m m)))).
surgery id_l ((f (f e b) (f (f m (f m m)) (f m m)))) ((f b (f (f m (f m m)) (f m m)))).
surgery id_r ((f b (f (f m (f m m)) (f m m)))) ((f b (f (f m m) (f m m)))).
surgery id_r ((f b (f (f m m) (f m m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_414: forall b: G, ((b <+> (m <+> (m <+> (m <+> ((e <+> m) <+> m))))) <+> ((e <+> e) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f b (f m (f m (f m (f (f e m) m))))) (f (f e e) m))) ((f (f b (f m (f m (f m (f e m))))) (f (f e e) m))).
surgery id_l ((f (f b (f m (f m (f m (f e m))))) (f (f e e) m))) ((f (f b (f m (f m (f m m)))) (f (f e e) m))).
surgery id_r ((f (f b (f m (f m (f m m)))) (f (f e e) m))) ((f (f b (f m (f m m))) (f (f e e) m))).
surgery id_r ((f (f b (f m (f m m))) (f (f e e) m))) ((f (f b (f m m)) (f (f e e) m))).
surgery id_r ((f (f b (f m m)) (f (f e e) m))) ((f (f b m) (f (f e e) m))).
surgery id_r ((f (f b m) (f (f e e) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_415: forall b: G, ((e <+> m) <+> (e <+> (((e <+> ((m <+> (e <+> m)) <+> m)) <+> e) <+> b))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f e (f (f (f e (f (f m (f e m)) m)) e) b)))) ((f e (f e (f (f (f e (f (f m (f e m)) m)) e) b)))).
surgery id_l ((f e (f e (f (f (f e (f (f m (f e m)) m)) e) b)))) ((f e (f (f (f e (f (f m (f e m)) m)) e) b))).
surgery id_l ((f e (f (f (f e (f (f m (f e m)) m)) e) b))) ((f e (f (f (f e (f (f m m) m)) e) b))).
surgery id_r ((f e (f (f (f e (f (f m m) m)) e) b))) ((f e (f (f (f e (f m m)) e) b))).
surgery id_r ((f e (f (f (f e (f m m)) e) b))) ((f e (f (f (f e m) e) b))).
surgery id_r ((f e (f (f (f e m) e) b))) ((f e (f (f e e) b))).
surgery id_l ((f e (f (f e e) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_416: forall b: G, ((e <+> ((e <+> e) <+> ((e <+> (e <+> (e <+> m))) <+> (e <+> m)))) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f e e) (f (f e (f e (f e m))) (f e m)))) b)) ((f (f e (f e (f (f e (f e (f e m))) (f e m)))) b)).
surgery id_l ((f (f e (f e (f (f e (f e (f e m))) (f e m)))) b)) ((f (f e (f (f e (f e (f e m))) (f e m))) b)).
surgery id_l ((f (f e (f (f e (f e (f e m))) (f e m))) b)) ((f (f e (f (f e (f e m)) (f e m))) b)).
surgery id_l ((f (f e (f (f e (f e m)) (f e m))) b)) ((f (f e (f (f e m) (f e m))) b)).
surgery id_r ((f (f e (f (f e m) (f e m))) b)) ((f (f e (f e (f e m))) b)).
surgery id_l ((f (f e (f e (f e m))) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_417: forall b: G, (((e <+> e) <+> (((e <+> b) <+> ((e <+> e) <+> m)) <+> m)) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f (f e b) (f (f e e) m)) m)) (f m m))) ((f (f e (f (f (f e b) (f (f e e) m)) m)) (f m m))).
surgery id_l ((f (f e (f (f (f e b) (f (f e e) m)) m)) (f m m))) ((f (f e (f (f b (f (f e e) m)) m)) (f m m))).
surgery id_l ((f (f e (f (f b (f (f e e) m)) m)) (f m m))) ((f (f e (f (f b (f e m)) m)) (f m m))).
surgery id_l ((f (f e (f (f b (f e m)) m)) (f m m))) ((f (f e (f (f b m) m)) (f m m))).
surgery id_r ((f (f e (f (f b m) m)) (f m m))) ((f (f e (f b m)) (f m m))).
surgery id_r ((f (f e (f b m)) (f m m))) ((f (f e b) (f m m))).
surgery id_l ((f (f e b) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_418: forall b: G, (((e <+> (e <+> m)) <+> (e <+> (e <+> e))) <+> (((e <+> m) <+> m) <+> b)) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f e (f e e))) (f (f (f e m) m) b))) ((f (f (f e m) (f e (f e e))) (f (f (f e m) m) b))).
surgery id_r ((f (f (f e m) (f e (f e e))) (f (f (f e m) m) b))) ((f (f e (f e (f e e))) (f (f (f e m) m) b))).
surgery id_l ((f (f e (f e (f e e))) (f (f (f e m) m) b))) ((f (f e (f e e)) (f (f (f e m) m) b))).
surgery id_l ((f (f e (f e e)) (f (f (f e m) m) b))) ((f (f e e) (f (f (f e m) m) b))).
surgery id_l ((f (f e e) (f (f (f e m) m) b))) ((f e (f (f (f e m) m) b))).
surgery id_r ((f e (f (f (f e m) m) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_419: forall b: G, ((e <+> (e <+> e)) <+> ((b <+> (m <+> m)) <+> (e <+> ((m <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e e)) (f (f b (f m m)) (f e (f (f m m) m))))) ((f (f e e) (f (f b (f m m)) (f e (f (f m m) m))))).
surgery id_l ((f (f e e) (f (f b (f m m)) (f e (f (f m m) m))))) ((f e (f (f b (f m m)) (f e (f (f m m) m))))).
surgery id_r ((f e (f (f b (f m m)) (f e (f (f m m) m))))) ((f e (f (f b m) (f e (f (f m m) m))))).
surgery id_r ((f e (f (f b m) (f e (f (f m m) m))))) ((f e (f b (f e (f (f m m) m))))).
surgery id_l ((f e (f b (f e (f (f m m) m))))) ((f e (f b (f (f m m) m)))).
surgery id_r ((f e (f b (f (f m m) m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_420: forall b: G, ((((b <+> (m <+> m)) <+> m) <+> ((m <+> m) <+> m)) <+> ((e <+> e) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f b (f m m)) m) (f (f m m) m)) (f (f e e) m))) ((f (f (f b (f m m)) (f (f m m) m)) (f (f e e) m))).
surgery id_r ((f (f (f b (f m m)) (f (f m m) m)) (f (f e e) m))) ((f (f (f b m) (f (f m m) m)) (f (f e e) m))).
surgery id_r ((f (f (f b m) (f (f m m) m)) (f (f e e) m))) ((f (f b (f (f m m) m)) (f (f e e) m))).
surgery id_r ((f (f b (f (f m m) m)) (f (f e e) m))) ((f (f b (f m m)) (f (f e e) m))).
surgery id_r ((f (f b (f m m)) (f (f e e) m))) ((f (f b m) (f (f e e) m))).
surgery id_r ((f (f b m) (f (f e e) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_421: forall b: G, (((e <+> (e <+> (e <+> e))) <+> (b <+> m)) <+> (((e <+> e) <+> e) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e (f e e))) (f b m)) (f (f (f e e) e) m))) ((f (f (f e (f e e)) (f b m)) (f (f (f e e) e) m))).
surgery id_l ((f (f (f e (f e e)) (f b m)) (f (f (f e e) e) m))) ((f (f (f e e) (f b m)) (f (f (f e e) e) m))).
surgery id_l ((f (f (f e e) (f b m)) (f (f (f e e) e) m))) ((f (f e (f b m)) (f (f (f e e) e) m))).
surgery id_r ((f (f e (f b m)) (f (f (f e e) e) m))) ((f (f e b) (f (f (f e e) e) m))).
surgery id_l ((f (f e b) (f (f (f e e) e) m))) ((f b (f (f (f e e) e) m))).
surgery id_l ((f b (f (f (f e e) e) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_422: forall b: G, ((e <+> ((e <+> (b <+> m)) <+> (m <+> m))) <+> ((e <+> m) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f e (f b m)) (f m m))) (f (f e m) (f e m)))) ((f (f e (f (f e b) (f m m))) (f (f e m) (f e m)))).
surgery id_l ((f (f e (f (f e b) (f m m))) (f (f e m) (f e m)))) ((f (f e (f b (f m m))) (f (f e m) (f e m)))).
surgery id_r ((f (f e (f b (f m m))) (f (f e m) (f e m)))) ((f (f e (f b m)) (f (f e m) (f e m)))).
surgery id_r ((f (f e (f b m)) (f (f e m) (f e m)))) ((f (f e b) (f (f e m) (f e m)))).
surgery id_l ((f (f e b) (f (f e m) (f e m)))) ((f b (f (f e m) (f e m)))).
surgery id_r ((f b (f (f e m) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_423: forall b: G, ((((((e <+> b) <+> m) <+> m) <+> m) <+> (m <+> m)) <+> (e <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f (f e b) m) m) m) (f m m)) (f e (f e m)))) ((f (f (f (f (f e b) m) m) (f m m)) (f e (f e m)))).
surgery id_r ((f (f (f (f (f e b) m) m) (f m m)) (f e (f e m)))) ((f (f (f (f e b) m) (f m m)) (f e (f e m)))).
surgery id_r ((f (f (f (f e b) m) (f m m)) (f e (f e m)))) ((f (f (f e b) (f m m)) (f e (f e m)))).
surgery id_l ((f (f (f e b) (f m m)) (f e (f e m)))) ((f (f b (f m m)) (f e (f e m)))).
surgery id_r ((f (f b (f m m)) (f e (f e m)))) ((f (f b m) (f e (f e m)))).
surgery id_r ((f (f b m) (f e (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_424: forall b: G, (b <+> ((e <+> m) <+> ((e <+> (((e <+> m) <+> m) <+> m)) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f b (f (f e m) (f (f e (f (f (f e m) m) m)) (f e m))))) ((f b (f e (f (f e (f (f (f e m) m) m)) (f e m))))).
surgery id_l ((f b (f e (f (f e (f (f (f e m) m) m)) (f e m))))) ((f b (f (f e (f (f (f e m) m) m)) (f e m)))).
surgery id_r ((f b (f (f e (f (f (f e m) m) m)) (f e m)))) ((f b (f (f e (f (f e m) m)) (f e m)))).
surgery id_r ((f b (f (f e (f (f e m) m)) (f e m)))) ((f b (f (f e (f e m)) (f e m)))).
surgery id_l ((f b (f (f e (f e m)) (f e m)))) ((f b (f (f e m) (f e m)))).
surgery id_r ((f b (f (f e m) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_425: forall b: G, (((e <+> e) <+> m) <+> (((e <+> e) <+> e) <+> ((e <+> (e <+> b)) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e e) m) (f (f (f e e) e) (f (f e (f e b)) m)))) ((f (f e e) (f (f (f e e) e) (f (f e (f e b)) m)))).
surgery id_l ((f (f e e) (f (f (f e e) e) (f (f e (f e b)) m)))) ((f e (f (f (f e e) e) (f (f e (f e b)) m)))).
surgery id_l ((f e (f (f (f e e) e) (f (f e (f e b)) m)))) ((f e (f (f e e) (f (f e (f e b)) m)))).
surgery id_l ((f e (f (f e e) (f (f e (f e b)) m)))) ((f e (f e (f (f e (f e b)) m)))).
surgery id_l ((f e (f e (f (f e (f e b)) m)))) ((f e (f (f e (f e b)) m))).
surgery id_l ((f e (f (f e (f e b)) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_426: forall b: G, ((((e <+> m) <+> e) <+> ((e <+> (e <+> (e <+> m))) <+> (m <+> m))) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) e) (f (f e (f e (f e m))) (f m m))) b)) ((f (f (f e e) (f (f e (f e (f e m))) (f m m))) b)).
surgery id_l ((f (f (f e e) (f (f e (f e (f e m))) (f m m))) b)) ((f (f e (f (f e (f e (f e m))) (f m m))) b)).
surgery id_l ((f (f e (f (f e (f e (f e m))) (f m m))) b)) ((f (f e (f (f e (f e m)) (f m m))) b)).
surgery id_l ((f (f e (f (f e (f e m)) (f m m))) b)) ((f (f e (f (f e m) (f m m))) b)).
surgery id_r ((f (f e (f (f e m) (f m m))) b)) ((f (f e (f e (f m m))) b)).
surgery id_l ((f (f e (f e (f m m))) b)) ((f (f e (f m m)) b)).
surgery id_r ((f (f e (f m m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_427: forall b: G, ((e <+> (e <+> m)) <+> ((e <+> m) <+> ((e <+> m) <+> ((b <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e m)) (f (f e m) (f (f e m) (f (f b m) m))))) ((f (f e m) (f (f e m) (f (f e m) (f (f b m) m))))).
surgery id_r ((f (f e m) (f (f e m) (f (f e m) (f (f b m) m))))) ((f e (f (f e m) (f (f e m) (f (f b m) m))))).
surgery id_r ((f e (f (f e m) (f (f e m) (f (f b m) m))))) ((f e (f e (f (f e m) (f (f b m) m))))).
surgery id_l ((f e (f e (f (f e m) (f (f b m) m))))) ((f e (f (f e m) (f (f b m) m)))).
surgery id_r ((f e (f (f e m) (f (f b m) m)))) ((f e (f e (f (f b m) m)))).
surgery id_l ((f e (f e (f (f b m) m)))) ((f e (f (f b m) m))).
surgery id_r ((f e (f (f b m) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_428: forall b: G, ((e <+> b) <+> ((e <+> (m <+> (e <+> m))) <+> (m <+> (m <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f (f e (f m (f e m))) (f m (f m (f m m)))))) ((f b (f (f e (f m (f e m))) (f m (f m (f m m)))))).
surgery id_l ((f b (f (f e (f m (f e m))) (f m (f m (f m m)))))) ((f b (f (f e (f m m)) (f m (f m (f m m)))))).
surgery id_r ((f b (f (f e (f m m)) (f m (f m (f m m)))))) ((f b (f (f e m) (f m (f m (f m m)))))).
surgery id_r ((f b (f (f e m) (f m (f m (f m m)))))) ((f b (f e (f m (f m (f m m)))))).
surgery id_l ((f b (f e (f m (f m (f m m)))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_429: forall b: G, (e <+> ((e <+> (((e <+> m) <+> e) <+> ((e <+> m) <+> m))) <+> (e <+> b))) = b.
Proof.
intros.
surgery id_r ((f e (f (f e (f (f (f e m) e) (f (f e m) m))) (f e b)))) ((f e (f (f e (f (f e e) (f (f e m) m))) (f e b)))).
surgery id_l ((f e (f (f e (f (f e e) (f (f e m) m))) (f e b)))) ((f e (f (f e (f e (f (f e m) m))) (f e b)))).
surgery id_l ((f e (f (f e (f e (f (f e m) m))) (f e b)))) ((f e (f (f e (f (f e m) m)) (f e b)))).
surgery id_r ((f e (f (f e (f (f e m) m)) (f e b)))) ((f e (f (f e (f e m)) (f e b)))).
surgery id_l ((f e (f (f e (f e m)) (f e b)))) ((f e (f (f e m) (f e b)))).
surgery id_r ((f e (f (f e m) (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_430: forall b: G, ((e <+> e) <+> ((e <+> ((e <+> e) <+> (b <+> (m <+> (m <+> m))))) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f e (f (f e e) (f b (f m (f m m))))) m))) ((f e (f (f e (f (f e e) (f b (f m (f m m))))) m))).
surgery id_l ((f e (f (f e (f (f e e) (f b (f m (f m m))))) m))) ((f e (f (f e (f e (f b (f m (f m m))))) m))).
surgery id_l ((f e (f (f e (f e (f b (f m (f m m))))) m))) ((f e (f (f e (f b (f m (f m m)))) m))).
surgery id_r ((f e (f (f e (f b (f m (f m m)))) m))) ((f e (f (f e (f b (f m m))) m))).
surgery id_r ((f e (f (f e (f b (f m m))) m))) ((f e (f (f e (f b m)) m))).
surgery id_r ((f e (f (f e (f b m)) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_431: forall b: G, (((((e <+> m) <+> e) <+> e) <+> (((e <+> m) <+> m) <+> m)) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f e m) e) e) (f (f (f e m) m) m)) (f e b))) ((f (f (f (f e e) e) (f (f (f e m) m) m)) (f e b))).
surgery id_l ((f (f (f (f e e) e) (f (f (f e m) m) m)) (f e b))) ((f (f (f e e) (f (f (f e m) m) m)) (f e b))).
surgery id_l ((f (f (f e e) (f (f (f e m) m) m)) (f e b))) ((f (f e (f (f (f e m) m) m)) (f e b))).
surgery id_r ((f (f e (f (f (f e m) m) m)) (f e b))) ((f (f e (f (f e m) m)) (f e b))).
surgery id_r ((f (f e (f (f e m) m)) (f e b))) ((f (f e (f e m)) (f e b))).
surgery id_l ((f (f e (f e m)) (f e b))) ((f (f e m) (f e b))).
surgery id_r ((f (f e m) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_432: forall b: G, (((e <+> m) <+> ((e <+> m) <+> m)) <+> (((e <+> m) <+> b) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f (f e m) m)) (f (f (f e m) b) (f e m)))) ((f (f e (f (f e m) m)) (f (f (f e m) b) (f e m)))).
surgery id_r ((f (f e (f (f e m) m)) (f (f (f e m) b) (f e m)))) ((f (f e (f e m)) (f (f (f e m) b) (f e m)))).
surgery id_l ((f (f e (f e m)) (f (f (f e m) b) (f e m)))) ((f (f e m) (f (f (f e m) b) (f e m)))).
surgery id_r ((f (f e m) (f (f (f e m) b) (f e m)))) ((f e (f (f (f e m) b) (f e m)))).
surgery id_r ((f e (f (f (f e m) b) (f e m)))) ((f e (f (f e b) (f e m)))).
surgery id_l ((f e (f (f e b) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_433: forall b: G, ((e <+> (e <+> e)) <+> (((e <+> (e <+> m)) <+> m) <+> (b <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e e)) (f (f (f e (f e m)) m) (f b (f e m))))) ((f (f e e) (f (f (f e (f e m)) m) (f b (f e m))))).
surgery id_l ((f (f e e) (f (f (f e (f e m)) m) (f b (f e m))))) ((f e (f (f (f e (f e m)) m) (f b (f e m))))).
surgery id_r ((f e (f (f (f e (f e m)) m) (f b (f e m))))) ((f e (f (f e (f e m)) (f b (f e m))))).
surgery id_l ((f e (f (f e (f e m)) (f b (f e m))))) ((f e (f (f e m) (f b (f e m))))).
surgery id_r ((f e (f (f e m) (f b (f e m))))) ((f e (f e (f b (f e m))))).
surgery id_l ((f e (f e (f b (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_434: forall b: G, ((((((e <+> m) <+> e) <+> m) <+> e) <+> (e <+> b)) <+> (m <+> (m <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f (f e m) e) m) e) (f e b)) (f m (f m m)))) ((f (f (f (f (f e m) e) e) (f e b)) (f m (f m m)))).
surgery id_r ((f (f (f (f (f e m) e) e) (f e b)) (f m (f m m)))) ((f (f (f (f e e) e) (f e b)) (f m (f m m)))).
surgery id_l ((f (f (f (f e e) e) (f e b)) (f m (f m m)))) ((f (f (f e e) (f e b)) (f m (f m m)))).
surgery id_l ((f (f (f e e) (f e b)) (f m (f m m)))) ((f (f e (f e b)) (f m (f m m)))).
surgery id_l ((f (f e (f e b)) (f m (f m m)))) ((f (f e b) (f m (f m m)))).
surgery id_l ((f (f e b) (f m (f m m)))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_435: forall b: G, ((e <+> m) <+> (((e <+> m) <+> (e <+> b)) <+> (m <+> ((m <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f (f e m) (f e b)) (f m (f (f m m) m))))) ((f e (f (f (f e m) (f e b)) (f m (f (f m m) m))))).
surgery id_r ((f e (f (f (f e m) (f e b)) (f m (f (f m m) m))))) ((f e (f (f e (f e b)) (f m (f (f m m) m))))).
surgery id_l ((f e (f (f e (f e b)) (f m (f (f m m) m))))) ((f e (f (f e b) (f m (f (f m m) m))))).
surgery id_l ((f e (f (f e b) (f m (f (f m m) m))))) ((f e (f b (f m (f (f m m) m))))).
surgery id_r ((f e (f b (f m (f (f m m) m))))) ((f e (f b (f m (f m m))))).
surgery id_r ((f e (f b (f m (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_436: forall b: G, (((e <+> b) <+> ((e <+> e) <+> (m <+> m))) <+> (m <+> (m <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f e b) (f (f e e) (f m m))) (f m (f m (f e m))))) ((f (f b (f (f e e) (f m m))) (f m (f m (f e m))))).
surgery id_l ((f (f b (f (f e e) (f m m))) (f m (f m (f e m))))) ((f (f b (f e (f m m))) (f m (f m (f e m))))).
surgery id_l ((f (f b (f e (f m m))) (f m (f m (f e m))))) ((f (f b (f m m)) (f m (f m (f e m))))).
surgery id_r ((f (f b (f m m)) (f m (f m (f e m))))) ((f (f b m) (f m (f m (f e m))))).
surgery id_r ((f (f b m) (f m (f m (f e m))))) ((f b (f m (f m (f e m))))).
surgery id_l ((f b (f m (f m (f e m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_437: forall b: G, (((e <+> m) <+> ((e <+> e) <+> m)) <+> ((e <+> e) <+> ((b <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f (f e e) m)) (f (f e e) (f (f b m) m)))) ((f (f e (f (f e e) m)) (f (f e e) (f (f b m) m)))).
surgery id_l ((f (f e (f (f e e) m)) (f (f e e) (f (f b m) m)))) ((f (f e (f e m)) (f (f e e) (f (f b m) m)))).
surgery id_l ((f (f e (f e m)) (f (f e e) (f (f b m) m)))) ((f (f e m) (f (f e e) (f (f b m) m)))).
surgery id_r ((f (f e m) (f (f e e) (f (f b m) m)))) ((f e (f (f e e) (f (f b m) m)))).
surgery id_l ((f e (f (f e e) (f (f b m) m)))) ((f e (f e (f (f b m) m)))).
surgery id_l ((f e (f e (f (f b m) m)))) ((f e (f (f b m) m))).
surgery id_r ((f e (f (f b m) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_438: forall b: G, (((e <+> ((e <+> m) <+> e)) <+> ((e <+> m) <+> ((e <+> e) <+> m))) <+> b) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f e m) e)) (f (f e m) (f (f e e) m))) b)) ((f (f (f e (f e e)) (f (f e m) (f (f e e) m))) b)).
surgery id_l ((f (f (f e (f e e)) (f (f e m) (f (f e e) m))) b)) ((f (f (f e e) (f (f e m) (f (f e e) m))) b)).
surgery id_l ((f (f (f e e) (f (f e m) (f (f e e) m))) b)) ((f (f e (f (f e m) (f (f e e) m))) b)).
surgery id_r ((f (f e (f (f e m) (f (f e e) m))) b)) ((f (f e (f e (f (f e e) m))) b)).
surgery id_l ((f (f e (f e (f (f e e) m))) b)) ((f (f e (f (f e e) m)) b)).
surgery id_l ((f (f e (f (f e e) m)) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_439: forall b: G, ((e <+> b) <+> ((m <+> m) <+> (((e <+> m) <+> (m <+> m)) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f (f m m) (f (f (f e m) (f m m)) (f m m))))) ((f b (f (f m m) (f (f (f e m) (f m m)) (f m m))))).
surgery id_r ((f b (f (f m m) (f (f (f e m) (f m m)) (f m m))))) ((f b (f m (f (f (f e m) (f m m)) (f m m))))).
surgery id_r ((f b (f m (f (f (f e m) (f m m)) (f m m))))) ((f b (f m (f (f e (f m m)) (f m m))))).
surgery id_r ((f b (f m (f (f e (f m m)) (f m m))))) ((f b (f m (f (f e m) (f m m))))).
surgery id_r ((f b (f m (f (f e m) (f m m))))) ((f b (f m (f e (f m m))))).
surgery id_l ((f b (f m (f e (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_440: forall b: G, ((((e <+> e) <+> (e <+> e)) <+> ((e <+> (e <+> m)) <+> (e <+> m))) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) (f e e)) (f (f e (f e m)) (f e m))) b)) ((f (f (f e (f e e)) (f (f e (f e m)) (f e m))) b)).
surgery id_l ((f (f (f e (f e e)) (f (f e (f e m)) (f e m))) b)) ((f (f (f e e) (f (f e (f e m)) (f e m))) b)).
surgery id_l ((f (f (f e e) (f (f e (f e m)) (f e m))) b)) ((f (f e (f (f e (f e m)) (f e m))) b)).
surgery id_l ((f (f e (f (f e (f e m)) (f e m))) b)) ((f (f e (f (f e m) (f e m))) b)).
surgery id_r ((f (f e (f (f e m) (f e m))) b)) ((f (f e (f e (f e m))) b)).
surgery id_l ((f (f e (f e (f e m))) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_441: forall b: G, (b <+> (((e <+> (((e <+> m) <+> m) <+> (e <+> (m <+> m)))) <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f b (f (f (f e (f (f (f e m) m) (f e (f m m)))) m) m))) ((f b (f (f e (f (f (f e m) m) (f e (f m m)))) m))).
surgery id_r ((f b (f (f e (f (f (f e m) m) (f e (f m m)))) m))) ((f b (f (f e (f (f e m) (f e (f m m)))) m))).
surgery id_r ((f b (f (f e (f (f e m) (f e (f m m)))) m))) ((f b (f (f e (f e (f e (f m m)))) m))).
surgery id_l ((f b (f (f e (f e (f e (f m m)))) m))) ((f b (f (f e (f e (f m m))) m))).
surgery id_l ((f b (f (f e (f e (f m m))) m))) ((f b (f (f e (f m m)) m))).
surgery id_r ((f b (f (f e (f m m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_442: forall b: G, (((e <+> (e <+> (e <+> e))) <+> (e <+> ((e <+> m) <+> m))) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e (f e e))) (f e (f (f e m) m))) (f b m))) ((f (f (f e (f e e)) (f e (f (f e m) m))) (f b m))).
surgery id_l ((f (f (f e (f e e)) (f e (f (f e m) m))) (f b m))) ((f (f (f e e) (f e (f (f e m) m))) (f b m))).
surgery id_l ((f (f (f e e) (f e (f (f e m) m))) (f b m))) ((f (f e (f e (f (f e m) m))) (f b m))).
surgery id_l ((f (f e (f e (f (f e m) m))) (f b m))) ((f (f e (f (f e m) m)) (f b m))).
surgery id_r ((f (f e (f (f e m) m)) (f b m))) ((f (f e (f e m)) (f b m))).
surgery id_l ((f (f e (f e m)) (f b m))) ((f (f e m) (f b m))).
surgery id_r ((f (f e m) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_443: forall b: G, (((e <+> (e <+> e)) <+> ((e <+> m) <+> m)) <+> (b <+> ((m <+> m) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e e)) (f (f e m) m)) (f b (f (f m m) m)))) ((f (f (f e e) (f (f e m) m)) (f b (f (f m m) m)))).
surgery id_l ((f (f (f e e) (f (f e m) m)) (f b (f (f m m) m)))) ((f (f e (f (f e m) m)) (f b (f (f m m) m)))).
surgery id_r ((f (f e (f (f e m) m)) (f b (f (f m m) m)))) ((f (f e (f e m)) (f b (f (f m m) m)))).
surgery id_l ((f (f e (f e m)) (f b (f (f m m) m)))) ((f (f e m) (f b (f (f m m) m)))).
surgery id_r ((f (f e m) (f b (f (f m m) m)))) ((f e (f b (f (f m m) m)))).
surgery id_r ((f e (f b (f (f m m) m)))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_444: forall b: G, ((e <+> ((e <+> (m <+> (e <+> (e <+> (m <+> m))))) <+> m)) <+> (b <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f e (f m (f e (f e (f m m))))) m)) (f b m))) ((f (f e (f (f e (f m (f e (f m m)))) m)) (f b m))).
surgery id_l ((f (f e (f (f e (f m (f e (f m m)))) m)) (f b m))) ((f (f e (f (f e (f m (f m m))) m)) (f b m))).
surgery id_r ((f (f e (f (f e (f m (f m m))) m)) (f b m))) ((f (f e (f (f e (f m m)) m)) (f b m))).
surgery id_r ((f (f e (f (f e (f m m)) m)) (f b m))) ((f (f e (f (f e m) m)) (f b m))).
surgery id_r ((f (f e (f (f e m) m)) (f b m))) ((f (f e (f e m)) (f b m))).
surgery id_l ((f (f e (f e m)) (f b m))) ((f (f e m) (f b m))).
surgery id_r ((f (f e m) (f b m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_445: forall b: G, (((e <+> e) <+> ((e <+> m) <+> m)) <+> ((e <+> (e <+> m)) <+> (b <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f e m) m)) (f (f e (f e m)) (f b m)))) ((f (f e (f (f e m) m)) (f (f e (f e m)) (f b m)))).
surgery id_r ((f (f e (f (f e m) m)) (f (f e (f e m)) (f b m)))) ((f (f e (f e m)) (f (f e (f e m)) (f b m)))).
surgery id_l ((f (f e (f e m)) (f (f e (f e m)) (f b m)))) ((f (f e m) (f (f e (f e m)) (f b m)))).
surgery id_r ((f (f e m) (f (f e (f e m)) (f b m)))) ((f e (f (f e (f e m)) (f b m)))).
surgery id_l ((f e (f (f e (f e m)) (f b m)))) ((f e (f (f e m) (f b m)))).
surgery id_r ((f e (f (f e m) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_446: forall b: G, (((e <+> (e <+> (m <+> (m <+> m)))) <+> (m <+> ((m <+> m) <+> m))) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e (f m (f m m)))) (f m (f (f m m) m))) b)) ((f (f (f e (f m (f m m))) (f m (f (f m m) m))) b)).
surgery id_r ((f (f (f e (f m (f m m))) (f m (f (f m m) m))) b)) ((f (f (f e (f m m)) (f m (f (f m m) m))) b)).
surgery id_r ((f (f (f e (f m m)) (f m (f (f m m) m))) b)) ((f (f (f e m) (f m (f (f m m) m))) b)).
surgery id_r ((f (f (f e m) (f m (f (f m m) m))) b)) ((f (f e (f m (f (f m m) m))) b)).
surgery id_r ((f (f e (f m (f (f m m) m))) b)) ((f (f e (f m (f m m))) b)).
surgery id_r ((f (f e (f m (f m m))) b)) ((f (f e (f m m)) b)).
surgery id_r ((f (f e (f m m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_447: forall b: G, ((((e <+> e) <+> e) <+> b) <+> (((e <+> m) <+> ((e <+> m) <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) e) b) (f (f (f e m) (f (f e m) m)) m))) ((f (f (f e e) b) (f (f (f e m) (f (f e m) m)) m))).
surgery id_l ((f (f (f e e) b) (f (f (f e m) (f (f e m) m)) m))) ((f (f e b) (f (f (f e m) (f (f e m) m)) m))).
surgery id_l ((f (f e b) (f (f (f e m) (f (f e m) m)) m))) ((f b (f (f (f e m) (f (f e m) m)) m))).
surgery id_r ((f b (f (f (f e m) (f (f e m) m)) m))) ((f b (f (f e (f (f e m) m)) m))).
surgery id_r ((f b (f (f e (f (f e m) m)) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_448: forall b: G, (((((e <+> e) <+> e) <+> (e <+> m)) <+> (e <+> m)) <+> ((e <+> m) <+> b)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f (f e e) e) (f e m)) (f e m)) (f (f e m) b))) ((f (f (f (f e e) (f e m)) (f e m)) (f (f e m) b))).
surgery id_l ((f (f (f (f e e) (f e m)) (f e m)) (f (f e m) b))) ((f (f (f e (f e m)) (f e m)) (f (f e m) b))).
surgery id_l ((f (f (f e (f e m)) (f e m)) (f (f e m) b))) ((f (f (f e m) (f e m)) (f (f e m) b))).
surgery id_r ((f (f (f e m) (f e m)) (f (f e m) b))) ((f (f e (f e m)) (f (f e m) b))).
surgery id_l ((f (f e (f e m)) (f (f e m) b))) ((f (f e m) (f (f e m) b))).
surgery id_r ((f (f e m) (f (f e m) b))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_449: forall b: G, ((e <+> (((b <+> m) <+> (e <+> m)) <+> (m <+> (e <+> m)))) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f (f b m) (f e m)) (f m (f e m)))) (f m m))) ((f (f e (f (f b (f e m)) (f m (f e m)))) (f m m))).
surgery id_l ((f (f e (f (f b (f e m)) (f m (f e m)))) (f m m))) ((f (f e (f (f b m) (f m (f e m)))) (f m m))).
surgery id_r ((f (f e (f (f b m) (f m (f e m)))) (f m m))) ((f (f e (f b (f m (f e m)))) (f m m))).
surgery id_l ((f (f e (f b (f m (f e m)))) (f m m))) ((f (f e (f b (f m m))) (f m m))).
surgery id_r ((f (f e (f b (f m m))) (f m m))) ((f (f e (f b m)) (f m m))).
surgery id_r ((f (f e (f b m)) (f m m))) ((f (f e b) (f m m))).
surgery id_l ((f (f e b) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_450: forall b: G, ((e <+> (m <+> m)) <+> (e <+> ((b <+> (e <+> (m <+> m))) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e (f m m)) (f e (f (f b (f e (f m m))) (f e m))))) ((f (f e m) (f e (f (f b (f e (f m m))) (f e m))))).
surgery id_r ((f (f e m) (f e (f (f b (f e (f m m))) (f e m))))) ((f e (f e (f (f b (f e (f m m))) (f e m))))).
surgery id_l ((f e (f e (f (f b (f e (f m m))) (f e m))))) ((f e (f (f b (f e (f m m))) (f e m)))).
surgery id_l ((f e (f (f b (f e (f m m))) (f e m)))) ((f e (f (f b (f m m)) (f e m)))).
surgery id_r ((f e (f (f b (f m m)) (f e m)))) ((f e (f (f b m) (f e m)))).
surgery id_r ((f e (f (f b m) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_451: forall b: G, (((e <+> m) <+> (e <+> (m <+> m))) <+> (e <+> (((e <+> m) <+> b) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f e m) (f e (f m m))) (f e (f (f (f e m) b) m)))) ((f (f e (f e (f m m))) (f e (f (f (f e m) b) m)))).
surgery id_l ((f (f e (f e (f m m))) (f e (f (f (f e m) b) m)))) ((f (f e (f m m)) (f e (f (f (f e m) b) m)))).
surgery id_r ((f (f e (f m m)) (f e (f (f (f e m) b) m)))) ((f (f e m) (f e (f (f (f e m) b) m)))).
surgery id_r ((f (f e m) (f e (f (f (f e m) b) m)))) ((f e (f e (f (f (f e m) b) m)))).
surgery id_l ((f e (f e (f (f (f e m) b) m)))) ((f e (f (f (f e m) b) m))).
surgery id_r ((f e (f (f (f e m) b) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_452: forall b: G, ((((e <+> (e <+> m)) <+> e) <+> ((e <+> (e <+> b)) <+> m)) <+> (e <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e (f e m)) e) (f (f e (f e b)) m)) (f e m))) ((f (f (f (f e m) e) (f (f e (f e b)) m)) (f e m))).
surgery id_r ((f (f (f (f e m) e) (f (f e (f e b)) m)) (f e m))) ((f (f (f e e) (f (f e (f e b)) m)) (f e m))).
surgery id_l ((f (f (f e e) (f (f e (f e b)) m)) (f e m))) ((f (f e (f (f e (f e b)) m)) (f e m))).
surgery id_l ((f (f e (f (f e (f e b)) m)) (f e m))) ((f (f e (f (f e b) m)) (f e m))).
surgery id_l ((f (f e (f (f e b) m)) (f e m))) ((f (f e (f b m)) (f e m))).
surgery id_r ((f (f e (f b m)) (f e m))) ((f (f e b) (f e m))).
surgery id_l ((f (f e b) (f e m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_453: forall b: G, ((((e <+> ((e <+> (e <+> m)) <+> m)) <+> e) <+> ((e <+> m) <+> m)) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e (f (f e (f e m)) m)) e) (f (f e m) m)) b)) ((f (f (f (f e (f (f e m) m)) e) (f (f e m) m)) b)).
surgery id_r ((f (f (f (f e (f (f e m) m)) e) (f (f e m) m)) b)) ((f (f (f (f e (f e m)) e) (f (f e m) m)) b)).
surgery id_l ((f (f (f (f e (f e m)) e) (f (f e m) m)) b)) ((f (f (f (f e m) e) (f (f e m) m)) b)).
surgery id_r ((f (f (f (f e m) e) (f (f e m) m)) b)) ((f (f (f e e) (f (f e m) m)) b)).
surgery id_l ((f (f (f e e) (f (f e m) m)) b)) ((f (f e (f (f e m) m)) b)).
surgery id_r ((f (f e (f (f e m) m)) b)) ((f (f e (f e m)) b)).
surgery id_l ((f (f e (f e m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_454: forall b: G, (e <+> ((b <+> m) <+> ((e <+> (e <+> (e <+> (e <+> m)))) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f e (f (f b m) (f (f e (f e (f e (f e m)))) (f m m))))) ((f e (f b (f (f e (f e (f e (f e m)))) (f m m))))).
surgery id_l ((f e (f b (f (f e (f e (f e (f e m)))) (f m m))))) ((f e (f b (f (f e (f e (f e m))) (f m m))))).
surgery id_l ((f e (f b (f (f e (f e (f e m))) (f m m))))) ((f e (f b (f (f e (f e m)) (f m m))))).
surgery id_l ((f e (f b (f (f e (f e m)) (f m m))))) ((f e (f b (f (f e m) (f m m))))).
surgery id_r ((f e (f b (f (f e m) (f m m))))) ((f e (f b (f e (f m m))))).
surgery id_l ((f e (f b (f e (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_455: forall b: G, (b <+> (m <+> ((e <+> m) <+> (e <+> (((e <+> e) <+> m) <+> (e <+> m)))))) = b.
Proof.
intros.
surgery id_r ((f b (f m (f (f e m) (f e (f (f (f e e) m) (f e m))))))) ((f b (f m (f e (f e (f (f (f e e) m) (f e m))))))).
surgery id_l ((f b (f m (f e (f e (f (f (f e e) m) (f e m))))))) ((f b (f m (f e (f (f (f e e) m) (f e m)))))).
surgery id_l ((f b (f m (f e (f (f (f e e) m) (f e m)))))) ((f b (f m (f (f (f e e) m) (f e m))))).
surgery id_r ((f b (f m (f (f (f e e) m) (f e m))))) ((f b (f m (f (f e e) (f e m))))).
surgery id_l ((f b (f m (f (f e e) (f e m))))) ((f b (f m (f e (f e m))))).
surgery id_l ((f b (f m (f e (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_456: forall b: G, (e <+> ((((e <+> b) <+> m) <+> m) <+> (m <+> ((e <+> m) <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_r ((f e (f (f (f (f e b) m) m) (f m (f (f e m) (f m m)))))) ((f e (f (f (f e b) m) (f m (f (f e m) (f m m)))))).
surgery id_r ((f e (f (f (f e b) m) (f m (f (f e m) (f m m)))))) ((f e (f (f e b) (f m (f (f e m) (f m m)))))).
surgery id_l ((f e (f (f e b) (f m (f (f e m) (f m m)))))) ((f e (f b (f m (f (f e m) (f m m)))))).
surgery id_r ((f e (f b (f m (f (f e m) (f m m)))))) ((f e (f b (f m (f e (f m m)))))).
surgery id_l ((f e (f b (f m (f e (f m m)))))) ((f e (f b (f m (f m m))))).
surgery id_r ((f e (f b (f m (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_457: forall b: G, (((b <+> m) <+> ((e <+> e) <+> (e <+> m))) <+> (((e <+> m) <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f (f e e) (f e m))) (f (f (f e m) m) m))) ((f (f b (f (f e e) (f e m))) (f (f (f e m) m) m))).
surgery id_l ((f (f b (f (f e e) (f e m))) (f (f (f e m) m) m))) ((f (f b (f e (f e m))) (f (f (f e m) m) m))).
surgery id_l ((f (f b (f e (f e m))) (f (f (f e m) m) m))) ((f (f b (f e m)) (f (f (f e m) m) m))).
surgery id_l ((f (f b (f e m)) (f (f (f e m) m) m))) ((f (f b m) (f (f (f e m) m) m))).
surgery id_r ((f (f b m) (f (f (f e m) m) m))) ((f b (f (f (f e m) m) m))).
surgery id_r ((f b (f (f (f e m) m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_458: forall b: G, (((e <+> (e <+> m)) <+> ((m <+> (e <+> m)) <+> ((e <+> e) <+> m))) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f (f m (f e m)) (f (f e e) m))) b)) ((f (f (f e m) (f (f m (f e m)) (f (f e e) m))) b)).
surgery id_r ((f (f (f e m) (f (f m (f e m)) (f (f e e) m))) b)) ((f (f e (f (f m (f e m)) (f (f e e) m))) b)).
surgery id_l ((f (f e (f (f m (f e m)) (f (f e e) m))) b)) ((f (f e (f (f m m) (f (f e e) m))) b)).
surgery id_r ((f (f e (f (f m m) (f (f e e) m))) b)) ((f (f e (f m (f (f e e) m))) b)).
surgery id_l ((f (f e (f m (f (f e e) m))) b)) ((f (f e (f m (f e m))) b)).
surgery id_l ((f (f e (f m (f e m))) b)) ((f (f e (f m m)) b)).
surgery id_r ((f (f e (f m m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_459: forall b: G, (((b <+> m) <+> (e <+> m)) <+> ((e <+> e) <+> (e <+> ((e <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f e m)) (f (f e e) (f e (f (f e m) m))))) ((f (f b (f e m)) (f (f e e) (f e (f (f e m) m))))).
surgery id_l ((f (f b (f e m)) (f (f e e) (f e (f (f e m) m))))) ((f (f b m) (f (f e e) (f e (f (f e m) m))))).
surgery id_r ((f (f b m) (f (f e e) (f e (f (f e m) m))))) ((f b (f (f e e) (f e (f (f e m) m))))).
surgery id_l ((f b (f (f e e) (f e (f (f e m) m))))) ((f b (f e (f e (f (f e m) m))))).
surgery id_l ((f b (f e (f e (f (f e m) m))))) ((f b (f e (f (f e m) m)))).
surgery id_l ((f b (f e (f (f e m) m)))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_460: forall b: G, ((((e <+> e) <+> ((e <+> e) <+> m)) <+> b) <+> (e <+> ((e <+> e) <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) (f (f e e) m)) b) (f e (f (f e e) m)))) ((f (f (f e (f (f e e) m)) b) (f e (f (f e e) m)))).
surgery id_l ((f (f (f e (f (f e e) m)) b) (f e (f (f e e) m)))) ((f (f (f e (f e m)) b) (f e (f (f e e) m)))).
surgery id_l ((f (f (f e (f e m)) b) (f e (f (f e e) m)))) ((f (f (f e m) b) (f e (f (f e e) m)))).
surgery id_r ((f (f (f e m) b) (f e (f (f e e) m)))) ((f (f e b) (f e (f (f e e) m)))).
surgery id_l ((f (f e b) (f e (f (f e e) m)))) ((f b (f e (f (f e e) m)))).
surgery id_l ((f b (f e (f (f e e) m)))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_461: forall b: G, ((e <+> ((b <+> ((e <+> m) <+> (m <+> m))) <+> m)) <+> (m <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f e (f (f b (f (f e m) (f m m))) m)) (f m (f e m)))) ((f (f e (f (f b (f e (f m m))) m)) (f m (f e m)))).
surgery id_l ((f (f e (f (f b (f e (f m m))) m)) (f m (f e m)))) ((f (f e (f (f b (f m m)) m)) (f m (f e m)))).
surgery id_r ((f (f e (f (f b (f m m)) m)) (f m (f e m)))) ((f (f e (f (f b m) m)) (f m (f e m)))).
surgery id_r ((f (f e (f (f b m) m)) (f m (f e m)))) ((f (f e (f b m)) (f m (f e m)))).
surgery id_r ((f (f e (f b m)) (f m (f e m)))) ((f (f e b) (f m (f e m)))).
surgery id_l ((f (f e b) (f m (f e m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_462: forall b: G, ((((e <+> m) <+> m) <+> ((e <+> e) <+> (e <+> e))) <+> (e <+> (e <+> b))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e m) m) (f (f e e) (f e e))) (f e (f e b)))) ((f (f (f e m) (f (f e e) (f e e))) (f e (f e b)))).
surgery id_r ((f (f (f e m) (f (f e e) (f e e))) (f e (f e b)))) ((f (f e (f (f e e) (f e e))) (f e (f e b)))).
surgery id_l ((f (f e (f (f e e) (f e e))) (f e (f e b)))) ((f (f e (f e (f e e))) (f e (f e b)))).
surgery id_l ((f (f e (f e (f e e))) (f e (f e b)))) ((f (f e (f e e)) (f e (f e b)))).
surgery id_l ((f (f e (f e e)) (f e (f e b)))) ((f (f e e) (f e (f e b)))).
surgery id_l ((f (f e e) (f e (f e b)))) ((f e (f e (f e b)))).
surgery id_l ((f e (f e (f e b)))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_463: forall b: G, ((((e <+> e) <+> m) <+> b) <+> (((m <+> m) <+> m) <+> ((e <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) b) (f (f (f m m) m) (f (f e m) m)))) ((f (f (f e e) b) (f (f (f m m) m) (f (f e m) m)))).
surgery id_l ((f (f (f e e) b) (f (f (f m m) m) (f (f e m) m)))) ((f (f e b) (f (f (f m m) m) (f (f e m) m)))).
surgery id_l ((f (f e b) (f (f (f m m) m) (f (f e m) m)))) ((f b (f (f (f m m) m) (f (f e m) m)))).
surgery id_r ((f b (f (f (f m m) m) (f (f e m) m)))) ((f b (f (f m m) (f (f e m) m)))).
surgery id_r ((f b (f (f m m) (f (f e m) m)))) ((f b (f m (f (f e m) m)))).
surgery id_r ((f b (f m (f (f e m) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_464: forall b: G, ((b <+> m) <+> (m <+> (((e <+> (e <+> m)) <+> ((m <+> m) <+> m)) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f m (f (f (f e (f e m)) (f (f m m) m)) m)))) ((f b (f m (f (f (f e (f e m)) (f (f m m) m)) m)))).
surgery id_l ((f b (f m (f (f (f e (f e m)) (f (f m m) m)) m)))) ((f b (f m (f (f (f e m) (f (f m m) m)) m)))).
surgery id_r ((f b (f m (f (f (f e m) (f (f m m) m)) m)))) ((f b (f m (f (f e (f (f m m) m)) m)))).
surgery id_r ((f b (f m (f (f e (f (f m m) m)) m)))) ((f b (f m (f (f e (f m m)) m)))).
surgery id_r ((f b (f m (f (f e (f m m)) m)))) ((f b (f m (f (f e m) m)))).
surgery id_r ((f b (f m (f (f e m) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_465: forall b: G, (((e <+> (e <+> (e <+> m))) <+> ((e <+> e) <+> (e <+> (m <+> m)))) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e (f e m))) (f (f e e) (f e (f m m)))) b)) ((f (f (f e (f e m)) (f (f e e) (f e (f m m)))) b)).
surgery id_l ((f (f (f e (f e m)) (f (f e e) (f e (f m m)))) b)) ((f (f (f e m) (f (f e e) (f e (f m m)))) b)).
surgery id_r ((f (f (f e m) (f (f e e) (f e (f m m)))) b)) ((f (f e (f (f e e) (f e (f m m)))) b)).
surgery id_l ((f (f e (f (f e e) (f e (f m m)))) b)) ((f (f e (f e (f e (f m m)))) b)).
surgery id_l ((f (f e (f e (f e (f m m)))) b)) ((f (f e (f e (f m m))) b)).
surgery id_l ((f (f e (f e (f m m))) b)) ((f (f e (f m m)) b)).
surgery id_r ((f (f e (f m m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_466: forall b: G, ((e <+> (b <+> m)) <+> ((m <+> ((e <+> m) <+> (m <+> (m <+> m)))) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f e (f b m)) (f (f m (f (f e m) (f m (f m m)))) m))) ((f (f e b) (f (f m (f (f e m) (f m (f m m)))) m))).
surgery id_l ((f (f e b) (f (f m (f (f e m) (f m (f m m)))) m))) ((f b (f (f m (f (f e m) (f m (f m m)))) m))).
surgery id_r ((f b (f (f m (f (f e m) (f m (f m m)))) m))) ((f b (f (f m (f e (f m (f m m)))) m))).
surgery id_l ((f b (f (f m (f e (f m (f m m)))) m))) ((f b (f (f m (f m (f m m))) m))).
surgery id_r ((f b (f (f m (f m (f m m))) m))) ((f b (f (f m (f m m)) m))).
surgery id_r ((f b (f (f m (f m m)) m))) ((f b (f (f m m) m))).
surgery id_r ((f b (f (f m m) m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_467: forall b: G, (e <+> ((e <+> (b <+> ((m <+> m) <+> m))) <+> ((e <+> m) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f e (f (f e (f b (f (f m m) m))) (f (f e m) (f e m))))) ((f e (f (f e (f b (f m m))) (f (f e m) (f e m))))).
surgery id_r ((f e (f (f e (f b (f m m))) (f (f e m) (f e m))))) ((f e (f (f e (f b m)) (f (f e m) (f e m))))).
surgery id_r ((f e (f (f e (f b m)) (f (f e m) (f e m))))) ((f e (f (f e b) (f (f e m) (f e m))))).
surgery id_l ((f e (f (f e b) (f (f e m) (f e m))))) ((f e (f b (f (f e m) (f e m))))).
surgery id_r ((f e (f b (f (f e m) (f e m))))) ((f e (f b (f e (f e m))))).
surgery id_l ((f e (f b (f e (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_468: forall b: G, ((e <+> m) <+> ((e <+> e) <+> ((e <+> (m <+> m)) <+> (e <+> (b <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f e e) (f (f e (f m m)) (f e (f b m)))))) ((f e (f (f e e) (f (f e (f m m)) (f e (f b m)))))).
surgery id_l ((f e (f (f e e) (f (f e (f m m)) (f e (f b m)))))) ((f e (f e (f (f e (f m m)) (f e (f b m)))))).
surgery id_l ((f e (f e (f (f e (f m m)) (f e (f b m)))))) ((f e (f (f e (f m m)) (f e (f b m))))).
surgery id_r ((f e (f (f e (f m m)) (f e (f b m))))) ((f e (f (f e m) (f e (f b m))))).
surgery id_r ((f e (f (f e m) (f e (f b m))))) ((f e (f e (f e (f b m))))).
surgery id_l ((f e (f e (f e (f b m))))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_469: forall b: G, (b <+> (((e <+> m) <+> ((m <+> m) <+> m)) <+> ((e <+> m) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_r ((f b (f (f (f e m) (f (f m m) m)) (f (f e m) (f e m))))) ((f b (f (f e (f (f m m) m)) (f (f e m) (f e m))))).
surgery id_r ((f b (f (f e (f (f m m) m)) (f (f e m) (f e m))))) ((f b (f (f e (f m m)) (f (f e m) (f e m))))).
surgery id_r ((f b (f (f e (f m m)) (f (f e m) (f e m))))) ((f b (f (f e m) (f (f e m) (f e m))))).
surgery id_r ((f b (f (f e m) (f (f e m) (f e m))))) ((f b (f e (f (f e m) (f e m))))).
surgery id_l ((f b (f e (f (f e m) (f e m))))) ((f b (f (f e m) (f e m)))).
surgery id_r ((f b (f (f e m) (f e m)))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_470: forall b: G, (((e <+> e) <+> (((e <+> e) <+> ((e <+> m) <+> m)) <+> m)) <+> (e <+> b)) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f (f e e) (f (f e m) m)) m)) (f e b))) ((f (f e (f (f (f e e) (f (f e m) m)) m)) (f e b))).
surgery id_l ((f (f e (f (f (f e e) (f (f e m) m)) m)) (f e b))) ((f (f e (f (f e (f (f e m) m)) m)) (f e b))).
surgery id_r ((f (f e (f (f e (f (f e m) m)) m)) (f e b))) ((f (f e (f (f e (f e m)) m)) (f e b))).
surgery id_l ((f (f e (f (f e (f e m)) m)) (f e b))) ((f (f e (f (f e m) m)) (f e b))).
surgery id_r ((f (f e (f (f e m) m)) (f e b))) ((f (f e (f e m)) (f e b))).
surgery id_l ((f (f e (f e m)) (f e b))) ((f (f e m) (f e b))).
surgery id_r ((f (f e m) (f e b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_471: forall b: G, (b <+> ((m <+> m) <+> ((e <+> (e <+> m)) <+> ((e <+> (e <+> m)) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f b (f (f m m) (f (f e (f e m)) (f (f e (f e m)) m))))) ((f b (f m (f (f e (f e m)) (f (f e (f e m)) m))))).
surgery id_l ((f b (f m (f (f e (f e m)) (f (f e (f e m)) m))))) ((f b (f m (f (f e m) (f (f e (f e m)) m))))).
surgery id_r ((f b (f m (f (f e m) (f (f e (f e m)) m))))) ((f b (f m (f e (f (f e (f e m)) m))))).
surgery id_l ((f b (f m (f e (f (f e (f e m)) m))))) ((f b (f m (f (f e (f e m)) m)))).
surgery id_l ((f b (f m (f (f e (f e m)) m)))) ((f b (f m (f (f e m) m)))).
surgery id_r ((f b (f m (f (f e m) m)))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_472: forall b: G, (((e <+> (e <+> m)) <+> ((e <+> m) <+> ((e <+> m) <+> (m <+> m)))) <+> b) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e m)) (f (f e m) (f (f e m) (f m m)))) b)) ((f (f (f e m) (f (f e m) (f (f e m) (f m m)))) b)).
surgery id_r ((f (f (f e m) (f (f e m) (f (f e m) (f m m)))) b)) ((f (f e (f (f e m) (f (f e m) (f m m)))) b)).
surgery id_r ((f (f e (f (f e m) (f (f e m) (f m m)))) b)) ((f (f e (f e (f (f e m) (f m m)))) b)).
surgery id_l ((f (f e (f e (f (f e m) (f m m)))) b)) ((f (f e (f (f e m) (f m m))) b)).
surgery id_r ((f (f e (f (f e m) (f m m))) b)) ((f (f e (f e (f m m))) b)).
surgery id_l ((f (f e (f e (f m m))) b)) ((f (f e (f m m)) b)).
surgery id_r ((f (f e (f m m)) b)) ((f (f e m) b)).
surgery id_r ((f (f e m) b)) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_473: forall b: G, (((e <+> e) <+> (((e <+> e) <+> (e <+> e)) <+> b)) <+> ((e <+> m) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f (f (f e e) (f e e)) b)) (f (f e m) m))) ((f (f e (f (f (f e e) (f e e)) b)) (f (f e m) m))).
surgery id_l ((f (f e (f (f (f e e) (f e e)) b)) (f (f e m) m))) ((f (f e (f (f e (f e e)) b)) (f (f e m) m))).
surgery id_l ((f (f e (f (f e (f e e)) b)) (f (f e m) m))) ((f (f e (f (f e e) b)) (f (f e m) m))).
surgery id_l ((f (f e (f (f e e) b)) (f (f e m) m))) ((f (f e (f e b)) (f (f e m) m))).
surgery id_l ((f (f e (f e b)) (f (f e m) m))) ((f (f e b) (f (f e m) m))).
surgery id_l ((f (f e b) (f (f e m) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_474: forall b: G, ((e <+> (e <+> m)) <+> ((e <+> ((e <+> e) <+> b)) <+> (m <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e m)) (f (f e (f (f e e) b)) (f m (f e m))))) ((f (f e m) (f (f e (f (f e e) b)) (f m (f e m))))).
surgery id_r ((f (f e m) (f (f e (f (f e e) b)) (f m (f e m))))) ((f e (f (f e (f (f e e) b)) (f m (f e m))))).
surgery id_l ((f e (f (f e (f (f e e) b)) (f m (f e m))))) ((f e (f (f e (f e b)) (f m (f e m))))).
surgery id_l ((f e (f (f e (f e b)) (f m (f e m))))) ((f e (f (f e b) (f m (f e m))))).
surgery id_l ((f e (f (f e b) (f m (f e m))))) ((f e (f b (f m (f e m))))).
surgery id_l ((f e (f b (f m (f e m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_475: forall b: G, (((e <+> ((e <+> e) <+> b)) <+> ((e <+> m) <+> (m <+> (e <+> m)))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f (f e e) b)) (f (f e m) (f m (f e m)))) m)) ((f (f e (f (f e e) b)) (f (f e m) (f m (f e m))))).
surgery id_l ((f (f e (f (f e e) b)) (f (f e m) (f m (f e m))))) ((f (f e (f e b)) (f (f e m) (f m (f e m))))).
surgery id_l ((f (f e (f e b)) (f (f e m) (f m (f e m))))) ((f (f e b) (f (f e m) (f m (f e m))))).
surgery id_l ((f (f e b) (f (f e m) (f m (f e m))))) ((f b (f (f e m) (f m (f e m))))).
surgery id_r ((f b (f (f e m) (f m (f e m))))) ((f b (f e (f m (f e m))))).
surgery id_l ((f b (f e (f m (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_476: forall b: G, ((b <+> m) <+> ((m <+> m) <+> ((e <+> m) <+> ((e <+> m) <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f b m) (f (f m m) (f (f e m) (f (f e m) (f m m)))))) ((f b (f (f m m) (f (f e m) (f (f e m) (f m m)))))).
surgery id_r ((f b (f (f m m) (f (f e m) (f (f e m) (f m m)))))) ((f b (f m (f (f e m) (f (f e m) (f m m)))))).
surgery id_r ((f b (f m (f (f e m) (f (f e m) (f m m)))))) ((f b (f m (f e (f (f e m) (f m m)))))).
surgery id_l ((f b (f m (f e (f (f e m) (f m m)))))) ((f b (f m (f (f e m) (f m m))))).
surgery id_r ((f b (f m (f (f e m) (f m m))))) ((f b (f m (f e (f m m))))).
surgery id_l ((f b (f m (f e (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_477: forall b: G, (((b <+> ((e <+> m) <+> (m <+> m))) <+> m) <+> (((e <+> e) <+> m) <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f b (f (f e m) (f m m))) m) (f (f (f e e) m) m))) ((f (f b (f (f e m) (f m m))) (f (f (f e e) m) m))).
surgery id_r ((f (f b (f (f e m) (f m m))) (f (f (f e e) m) m))) ((f (f b (f e (f m m))) (f (f (f e e) m) m))).
surgery id_l ((f (f b (f e (f m m))) (f (f (f e e) m) m))) ((f (f b (f m m)) (f (f (f e e) m) m))).
surgery id_r ((f (f b (f m m)) (f (f (f e e) m) m))) ((f (f b m) (f (f (f e e) m) m))).
surgery id_r ((f (f b m) (f (f (f e e) m) m))) ((f b (f (f (f e e) m) m))).
surgery id_r ((f b (f (f (f e e) m) m))) ((f b (f (f e e) m))).
surgery id_l ((f b (f (f e e) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_478: forall b: G, ((e <+> ((e <+> b) <+> m)) <+> ((m <+> m) <+> ((e <+> m) <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f e b) m)) (f (f m m) (f (f e m) (f e m))))) ((f (f e (f b m)) (f (f m m) (f (f e m) (f e m))))).
surgery id_r ((f (f e (f b m)) (f (f m m) (f (f e m) (f e m))))) ((f (f e b) (f (f m m) (f (f e m) (f e m))))).
surgery id_l ((f (f e b) (f (f m m) (f (f e m) (f e m))))) ((f b (f (f m m) (f (f e m) (f e m))))).
surgery id_r ((f b (f (f m m) (f (f e m) (f e m))))) ((f b (f m (f (f e m) (f e m))))).
surgery id_r ((f b (f m (f (f e m) (f e m))))) ((f b (f m (f e (f e m))))).
surgery id_l ((f b (f m (f e (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_479: forall b: G, (((e <+> e) <+> (m <+> m)) <+> (((b <+> m) <+> m) <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f e e) (f m m)) (f (f (f b m) m) (f e (f e m))))) ((f (f e (f m m)) (f (f (f b m) m) (f e (f e m))))).
surgery id_r ((f (f e (f m m)) (f (f (f b m) m) (f e (f e m))))) ((f (f e m) (f (f (f b m) m) (f e (f e m))))).
surgery id_r ((f (f e m) (f (f (f b m) m) (f e (f e m))))) ((f e (f (f (f b m) m) (f e (f e m))))).
surgery id_r ((f e (f (f (f b m) m) (f e (f e m))))) ((f e (f (f b m) (f e (f e m))))).
surgery id_r ((f e (f (f b m) (f e (f e m))))) ((f e (f b (f e (f e m))))).
surgery id_l ((f e (f b (f e (f e m))))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_480: forall b: G, ((e <+> e) <+> (((((e <+> (e <+> m)) <+> e) <+> (m <+> m)) <+> e) <+> b)) = b.
Proof.
intros.
surgery id_l ((f (f e e) (f (f (f (f (f e (f e m)) e) (f m m)) e) b))) ((f e (f (f (f (f (f e (f e m)) e) (f m m)) e) b))).
surgery id_l ((f e (f (f (f (f (f e (f e m)) e) (f m m)) e) b))) ((f e (f (f (f (f (f e m) e) (f m m)) e) b))).
surgery id_r ((f e (f (f (f (f (f e m) e) (f m m)) e) b))) ((f e (f (f (f (f e e) (f m m)) e) b))).
surgery id_l ((f e (f (f (f (f e e) (f m m)) e) b))) ((f e (f (f (f e (f m m)) e) b))).
surgery id_r ((f e (f (f (f e (f m m)) e) b))) ((f e (f (f (f e m) e) b))).
surgery id_r ((f e (f (f (f e m) e) b))) ((f e (f (f e e) b))).
surgery id_l ((f e (f (f e e) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_481: forall b: G, (((e <+> (e <+> (e <+> e))) <+> b) <+> ((e <+> ((e <+> e) <+> m)) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f e (f e (f e e))) b) (f (f e (f (f e e) m)) m))) ((f (f (f e (f e e)) b) (f (f e (f (f e e) m)) m))).
surgery id_l ((f (f (f e (f e e)) b) (f (f e (f (f e e) m)) m))) ((f (f (f e e) b) (f (f e (f (f e e) m)) m))).
surgery id_l ((f (f (f e e) b) (f (f e (f (f e e) m)) m))) ((f (f e b) (f (f e (f (f e e) m)) m))).
surgery id_l ((f (f e b) (f (f e (f (f e e) m)) m))) ((f b (f (f e (f (f e e) m)) m))).
surgery id_l ((f b (f (f e (f (f e e) m)) m))) ((f b (f (f e (f e m)) m))).
surgery id_l ((f b (f (f e (f e m)) m))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_482: forall b: G, ((((e <+> e) <+> (b <+> m)) <+> (e <+> m)) <+> (e <+> (m <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e e) (f b m)) (f e m)) (f e (f m (f m m))))) ((f (f (f e (f b m)) (f e m)) (f e (f m (f m m))))).
surgery id_r ((f (f (f e (f b m)) (f e m)) (f e (f m (f m m))))) ((f (f (f e b) (f e m)) (f e (f m (f m m))))).
surgery id_l ((f (f (f e b) (f e m)) (f e (f m (f m m))))) ((f (f b (f e m)) (f e (f m (f m m))))).
surgery id_l ((f (f b (f e m)) (f e (f m (f m m))))) ((f (f b m) (f e (f m (f m m))))).
surgery id_r ((f (f b m) (f e (f m (f m m))))) ((f b (f e (f m (f m m))))).
surgery id_l ((f b (f e (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_483: forall b: G, ((e <+> (e <+> e)) <+> ((e <+> ((e <+> e) <+> (e <+> m))) <+> (b <+> m))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e e)) (f (f e (f (f e e) (f e m))) (f b m)))) ((f (f e e) (f (f e (f (f e e) (f e m))) (f b m)))).
surgery id_l ((f (f e e) (f (f e (f (f e e) (f e m))) (f b m)))) ((f e (f (f e (f (f e e) (f e m))) (f b m)))).
surgery id_l ((f e (f (f e (f (f e e) (f e m))) (f b m)))) ((f e (f (f e (f e (f e m))) (f b m)))).
surgery id_l ((f e (f (f e (f e (f e m))) (f b m)))) ((f e (f (f e (f e m)) (f b m)))).
surgery id_l ((f e (f (f e (f e m)) (f b m)))) ((f e (f (f e m) (f b m)))).
surgery id_r ((f e (f (f e m) (f b m)))) ((f e (f e (f b m)))).
surgery id_l ((f e (f e (f b m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_484: forall b: G, ((e <+> (e <+> m)) <+> (e <+> (e <+> (((e <+> (b <+> m)) <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e m)) (f e (f e (f (f (f e (f b m)) m) m))))) ((f (f e m) (f e (f e (f (f (f e (f b m)) m) m))))).
surgery id_r ((f (f e m) (f e (f e (f (f (f e (f b m)) m) m))))) ((f e (f e (f e (f (f (f e (f b m)) m) m))))).
surgery id_l ((f e (f e (f e (f (f (f e (f b m)) m) m))))) ((f e (f e (f (f (f e (f b m)) m) m)))).
surgery id_l ((f e (f e (f (f (f e (f b m)) m) m)))) ((f e (f (f (f e (f b m)) m) m))).
surgery id_r ((f e (f (f (f e (f b m)) m) m))) ((f e (f (f e (f b m)) m))).
surgery id_r ((f e (f (f e (f b m)) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_485: forall b: G, ((e <+> (e <+> e)) <+> (((e <+> e) <+> (e <+> m)) <+> ((e <+> m) <+> b))) = b.
Proof.
intros.
surgery id_l ((f (f e (f e e)) (f (f (f e e) (f e m)) (f (f e m) b)))) ((f (f e e) (f (f (f e e) (f e m)) (f (f e m) b)))).
surgery id_l ((f (f e e) (f (f (f e e) (f e m)) (f (f e m) b)))) ((f e (f (f (f e e) (f e m)) (f (f e m) b)))).
surgery id_l ((f e (f (f (f e e) (f e m)) (f (f e m) b)))) ((f e (f (f e (f e m)) (f (f e m) b)))).
surgery id_l ((f e (f (f e (f e m)) (f (f e m) b)))) ((f e (f (f e m) (f (f e m) b)))).
surgery id_r ((f e (f (f e m) (f (f e m) b)))) ((f e (f e (f (f e m) b)))).
surgery id_l ((f e (f e (f (f e m) b)))) ((f e (f (f e m) b))).
surgery id_r ((f e (f (f e m) b))) ((f e (f e b))).
surgery id_l ((f e (f e b))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_486: forall b: G, ((e <+> m) <+> (((e <+> e) <+> b) <+> ((e <+> (e <+> m)) <+> (m <+> m)))) = b.
Proof.
intros.
surgery id_r ((f (f e m) (f (f (f e e) b) (f (f e (f e m)) (f m m))))) ((f e (f (f (f e e) b) (f (f e (f e m)) (f m m))))).
surgery id_l ((f e (f (f (f e e) b) (f (f e (f e m)) (f m m))))) ((f e (f (f e b) (f (f e (f e m)) (f m m))))).
surgery id_l ((f e (f (f e b) (f (f e (f e m)) (f m m))))) ((f e (f b (f (f e (f e m)) (f m m))))).
surgery id_l ((f e (f b (f (f e (f e m)) (f m m))))) ((f e (f b (f (f e m) (f m m))))).
surgery id_r ((f e (f b (f (f e m) (f m m))))) ((f e (f b (f e (f m m))))).
surgery id_l ((f e (f b (f e (f m m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_487: forall b: G, ((e <+> b) <+> (m <+> (m <+> ((e <+> e) <+> (m <+> (m <+> (e <+> m))))))) = b.
Proof.
intros.
surgery id_l ((f (f e b) (f m (f m (f (f e e) (f m (f m (f e m)))))))) ((f b (f m (f m (f (f e e) (f m (f m (f e m)))))))).
surgery id_l ((f b (f m (f m (f (f e e) (f m (f m (f e m)))))))) ((f b (f m (f m (f e (f m (f m (f e m)))))))).
surgery id_l ((f b (f m (f m (f e (f m (f m (f e m)))))))) ((f b (f m (f m (f m (f m (f e m))))))).
surgery id_l ((f b (f m (f m (f m (f m (f e m))))))) ((f b (f m (f m (f m (f m m)))))).
surgery id_r ((f b (f m (f m (f m (f m m)))))) ((f b (f m (f m (f m m))))).
surgery id_r ((f b (f m (f m (f m m))))) ((f b (f m (f m m)))).
surgery id_r ((f b (f m (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_488: forall b: G, ((((((e <+> e) <+> m) <+> b) <+> m) <+> (m <+> (e <+> (e <+> m)))) <+> m) = b.
Proof.
intros.
surgery id_r ((f (f (f (f (f (f e e) m) b) m) (f m (f e (f e m)))) m)) ((f (f (f (f (f e e) m) b) m) (f m (f e (f e m))))).
surgery id_r ((f (f (f (f (f e e) m) b) m) (f m (f e (f e m))))) ((f (f (f (f e e) m) b) (f m (f e (f e m))))).
surgery id_r ((f (f (f (f e e) m) b) (f m (f e (f e m))))) ((f (f (f e e) b) (f m (f e (f e m))))).
surgery id_l ((f (f (f e e) b) (f m (f e (f e m))))) ((f (f e b) (f m (f e (f e m))))).
surgery id_l ((f (f e b) (f m (f e (f e m))))) ((f b (f m (f e (f e m))))).
surgery id_l ((f b (f m (f e (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_489: forall b: G, ((((e <+> e) <+> m) <+> (m <+> (e <+> m))) <+> ((e <+> b) <+> (e <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f (f e e) m) (f m (f e m))) (f (f e b) (f e m)))) ((f (f (f e e) (f m (f e m))) (f (f e b) (f e m)))).
surgery id_l ((f (f (f e e) (f m (f e m))) (f (f e b) (f e m)))) ((f (f e (f m (f e m))) (f (f e b) (f e m)))).
surgery id_l ((f (f e (f m (f e m))) (f (f e b) (f e m)))) ((f (f e (f m m)) (f (f e b) (f e m)))).
surgery id_r ((f (f e (f m m)) (f (f e b) (f e m)))) ((f (f e m) (f (f e b) (f e m)))).
surgery id_r ((f (f e m) (f (f e b) (f e m)))) ((f e (f (f e b) (f e m)))).
surgery id_l ((f e (f (f e b) (f e m)))) ((f e (f b (f e m)))).
surgery id_l ((f e (f b (f e m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_490: forall b: G, ((e <+> ((e <+> e) <+> m)) <+> (b <+> (e <+> (m <+> ((e <+> e) <+> m))))) = b.
Proof.
intros.
surgery id_l ((f (f e (f (f e e) m)) (f b (f e (f m (f (f e e) m)))))) ((f (f e (f e m)) (f b (f e (f m (f (f e e) m)))))).
surgery id_l ((f (f e (f e m)) (f b (f e (f m (f (f e e) m)))))) ((f (f e m) (f b (f e (f m (f (f e e) m)))))).
surgery id_r ((f (f e m) (f b (f e (f m (f (f e e) m)))))) ((f e (f b (f e (f m (f (f e e) m)))))).
surgery id_l ((f e (f b (f e (f m (f (f e e) m)))))) ((f e (f b (f m (f (f e e) m))))).
surgery id_l ((f e (f b (f m (f (f e e) m))))) ((f e (f b (f m (f e m))))).
surgery id_l ((f e (f b (f m (f e m))))) ((f e (f b (f m m)))).
surgery id_r ((f e (f b (f m m)))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_491: forall b: G, (e <+> ((e <+> m) <+> ((((e <+> e) <+> e) <+> ((e <+> b) <+> m)) <+> m))) = b.
Proof.
intros.
surgery id_r ((f e (f (f e m) (f (f (f (f e e) e) (f (f e b) m)) m)))) ((f e (f e (f (f (f (f e e) e) (f (f e b) m)) m)))).
surgery id_l ((f e (f e (f (f (f (f e e) e) (f (f e b) m)) m)))) ((f e (f (f (f (f e e) e) (f (f e b) m)) m))).
surgery id_l ((f e (f (f (f (f e e) e) (f (f e b) m)) m))) ((f e (f (f (f e e) (f (f e b) m)) m))).
surgery id_l ((f e (f (f (f e e) (f (f e b) m)) m))) ((f e (f (f e (f (f e b) m)) m))).
surgery id_l ((f e (f (f e (f (f e b) m)) m))) ((f e (f (f e (f b m)) m))).
surgery id_r ((f e (f (f e (f b m)) m))) ((f e (f (f e b) m))).
surgery id_l ((f e (f (f e b) m))) ((f e (f b m))).
surgery id_r ((f e (f b m))) ((f e b)).
surgery id_l ((f e b)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_492: forall b: G, (((b <+> m) <+> (e <+> (e <+> m))) <+> ((e <+> m) <+> ((e <+> m) <+> m))) = b.
Proof.
intros.
surgery id_r ((f (f (f b m) (f e (f e m))) (f (f e m) (f (f e m) m)))) ((f (f b (f e (f e m))) (f (f e m) (f (f e m) m)))).
surgery id_l ((f (f b (f e (f e m))) (f (f e m) (f (f e m) m)))) ((f (f b (f e m)) (f (f e m) (f (f e m) m)))).
surgery id_l ((f (f b (f e m)) (f (f e m) (f (f e m) m)))) ((f (f b m) (f (f e m) (f (f e m) m)))).
surgery id_r ((f (f b m) (f (f e m) (f (f e m) m)))) ((f b (f (f e m) (f (f e m) m)))).
surgery id_r ((f b (f (f e m) (f (f e m) m)))) ((f b (f e (f (f e m) m)))).
surgery id_l ((f b (f e (f (f e m) m)))) ((f b (f (f e m) m))).
surgery id_r ((f b (f (f e m) m))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_493: forall b: G, (((e <+> (b <+> m)) <+> (((e <+> e) <+> m) <+> (m <+> m))) <+> (m <+> m)) = b.
Proof.
intros.
surgery id_r ((f (f (f e (f b m)) (f (f (f e e) m) (f m m))) (f m m))) ((f (f (f e b) (f (f (f e e) m) (f m m))) (f m m))).
surgery id_l ((f (f (f e b) (f (f (f e e) m) (f m m))) (f m m))) ((f (f b (f (f (f e e) m) (f m m))) (f m m))).
surgery id_r ((f (f b (f (f (f e e) m) (f m m))) (f m m))) ((f (f b (f (f e e) (f m m))) (f m m))).
surgery id_l ((f (f b (f (f e e) (f m m))) (f m m))) ((f (f b (f e (f m m))) (f m m))).
surgery id_l ((f (f b (f e (f m m))) (f m m))) ((f (f b (f m m)) (f m m))).
surgery id_r ((f (f b (f m m)) (f m m))) ((f (f b m) (f m m))).
surgery id_r ((f (f b m) (f m m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_494: forall b: G, (b <+> ((e <+> (m <+> m)) <+> ((e <+> (e <+> m)) <+> (m <+> (e <+> m))))) = b.
Proof.
intros.
surgery id_r ((f b (f (f e (f m m)) (f (f e (f e m)) (f m (f e m)))))) ((f b (f (f e m) (f (f e (f e m)) (f m (f e m)))))).
surgery id_r ((f b (f (f e m) (f (f e (f e m)) (f m (f e m)))))) ((f b (f e (f (f e (f e m)) (f m (f e m)))))).
surgery id_l ((f b (f e (f (f e (f e m)) (f m (f e m)))))) ((f b (f (f e (f e m)) (f m (f e m))))).
surgery id_l ((f b (f (f e (f e m)) (f m (f e m))))) ((f b (f (f e m) (f m (f e m))))).
surgery id_r ((f b (f (f e m) (f m (f e m))))) ((f b (f e (f m (f e m))))).
surgery id_l ((f b (f e (f m (f e m))))) ((f b (f m (f e m)))).
surgery id_l ((f b (f m (f e m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_495: forall b: G, ((((e <+> (e <+> e)) <+> e) <+> (e <+> b)) <+> (((m <+> m) <+> m) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f (f (f e (f e e)) e) (f e b)) (f (f (f m m) m) m))) ((f (f (f (f e e) e) (f e b)) (f (f (f m m) m) m))).
surgery id_l ((f (f (f (f e e) e) (f e b)) (f (f (f m m) m) m))) ((f (f (f e e) (f e b)) (f (f (f m m) m) m))).
surgery id_l ((f (f (f e e) (f e b)) (f (f (f m m) m) m))) ((f (f e (f e b)) (f (f (f m m) m) m))).
surgery id_l ((f (f e (f e b)) (f (f (f m m) m) m))) ((f (f e b) (f (f (f m m) m) m))).
surgery id_l ((f (f e b) (f (f (f m m) m) m))) ((f b (f (f (f m m) m) m))).
surgery id_r ((f b (f (f (f m m) m) m))) ((f b (f (f m m) m))).
surgery id_r ((f b (f (f m m) m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_496: forall b: G, ((b <+> (e <+> (e <+> m))) <+> ((e <+> (m <+> m)) <+> (e <+> (e <+> m)))) = b.
Proof.
intros.
surgery id_l ((f (f b (f e (f e m))) (f (f e (f m m)) (f e (f e m))))) ((f (f b (f e m)) (f (f e (f m m)) (f e (f e m))))).
surgery id_l ((f (f b (f e m)) (f (f e (f m m)) (f e (f e m))))) ((f (f b m) (f (f e (f m m)) (f e (f e m))))).
surgery id_r ((f (f b m) (f (f e (f m m)) (f e (f e m))))) ((f b (f (f e (f m m)) (f e (f e m))))).
surgery id_r ((f b (f (f e (f m m)) (f e (f e m))))) ((f b (f (f e m) (f e (f e m))))).
surgery id_r ((f b (f (f e m) (f e (f e m))))) ((f b (f e (f e (f e m))))).
surgery id_l ((f b (f e (f e (f e m))))) ((f b (f e (f e m)))).
surgery id_l ((f b (f e (f e m)))) ((f b (f e m))).
surgery id_l ((f b (f e m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_497: forall b: G, (b <+> ((((e <+> (e <+> m)) <+> m) <+> m) <+> (e <+> ((m <+> m) <+> m)))) = b.
Proof.
intros.
surgery id_r ((f b (f (f (f (f e (f e m)) m) m) (f e (f (f m m) m))))) ((f b (f (f (f e (f e m)) m) (f e (f (f m m) m))))).
surgery id_r ((f b (f (f (f e (f e m)) m) (f e (f (f m m) m))))) ((f b (f (f e (f e m)) (f e (f (f m m) m))))).
surgery id_l ((f b (f (f e (f e m)) (f e (f (f m m) m))))) ((f b (f (f e m) (f e (f (f m m) m))))).
surgery id_r ((f b (f (f e m) (f e (f (f m m) m))))) ((f b (f e (f e (f (f m m) m))))).
surgery id_l ((f b (f e (f e (f (f m m) m))))) ((f b (f e (f (f m m) m)))).
surgery id_l ((f b (f e (f (f m m) m)))) ((f b (f (f m m) m))).
surgery id_r ((f b (f (f m m) m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_498: forall b: G, ((b <+> (e <+> ((e <+> (e <+> (e <+> m))) <+> m))) <+> ((m <+> m) <+> m)) = b.
Proof.
intros.
surgery id_l ((f (f b (f e (f (f e (f e (f e m))) m))) (f (f m m) m))) ((f (f b (f (f e (f e (f e m))) m)) (f (f m m) m))).
surgery id_l ((f (f b (f (f e (f e (f e m))) m)) (f (f m m) m))) ((f (f b (f (f e (f e m)) m)) (f (f m m) m))).
surgery id_l ((f (f b (f (f e (f e m)) m)) (f (f m m) m))) ((f (f b (f (f e m) m)) (f (f m m) m))).
surgery id_r ((f (f b (f (f e m) m)) (f (f m m) m))) ((f (f b (f e m)) (f (f m m) m))).
surgery id_l ((f (f b (f e m)) (f (f m m) m))) ((f (f b m) (f (f m m) m))).
surgery id_r ((f (f b m) (f (f m m) m))) ((f b (f (f m m) m))).
surgery id_r ((f b (f (f m m) m))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

Lemma rewrite_eq_499: forall b: G, ((b <+> ((e <+> m) <+> m)) <+> (e <+> ((e <+> m) <+> (e <+> (m <+> m))))) = b.
Proof.
intros.
surgery id_r ((f (f b (f (f e m) m)) (f e (f (f e m) (f e (f m m)))))) ((f (f b (f e m)) (f e (f (f e m) (f e (f m m)))))).
surgery id_l ((f (f b (f e m)) (f e (f (f e m) (f e (f m m)))))) ((f (f b m) (f e (f (f e m) (f e (f m m)))))).
surgery id_r ((f (f b m) (f e (f (f e m) (f e (f m m)))))) ((f b (f e (f (f e m) (f e (f m m)))))).
surgery id_l ((f b (f e (f (f e m) (f e (f m m)))))) ((f b (f (f e m) (f e (f m m))))).
surgery id_r ((f b (f (f e m) (f e (f m m))))) ((f b (f e (f e (f m m))))).
surgery id_l ((f b (f e (f e (f m m))))) ((f b (f e (f m m)))).
surgery id_l ((f b (f e (f m m)))) ((f b (f m m))).
surgery id_r ((f b (f m m))) ((f b m)).
surgery id_r ((f b m)) (b).
reflexivity.
Qed.

