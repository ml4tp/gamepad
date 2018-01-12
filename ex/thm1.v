(*Set Printing All.*)
Require Import Omega.

Section Group.
(* The set of the group. *)
Variable G : Set.

(* The left identity for +. *)
Variable e : G.

(* The right identity for +. *)
Variable m : G.

(* The right identity for o. *)
Variable z : G.

(* + binary operator. *)
Variable f : G -> G -> G.

(* o binary operator. *)
Variable q : G -> G -> G.

(* For readability, we use infix <+> to stand for the binary operator. *)
Infix "<+>" := f (at level 50).
Infix "<o>" := q (at level 50).

(* [m] is the right-identity for all elements [a] *)
Variable id_r : forall a, a <+> m = a.

(* [e] is the right-identity for all elements [a] *)
Variable id_l : forall a, e <+> a = a.

(* [z] is the right-identity for all elements [a] for <o> *)
Variable id_r_o: forall a, z <o> a = a.

Lemma foobar:
  (forall b, b <+> m = b) ->
  (forall b, e <+> b = b) ->
  (e <+> m) <+> (e <+> m) = m <+> m.
Proof.
  intros.
  
  assert ((e <+> m) <+> (e <+> m) = m <+> (e <+> m)) as H1. {
    rewrite H0.
    reflexivity.
  }
  rewrite H1.
  clear H1.
  
Theorem iden_eq_short:
  (forall b, b <+> m = b) ->
  (forall b, e <+> b = b) ->
  forall b, b <+> (e <+> m) = b.
  intros.

  assert ((e <+> m) <+> (e <+> m) = m <+> m) as H3.
  rewrite H0.
  reflexivity.
  rewrite H3.
  clear H3.
  
  
rewrite -> H0.
rewrite -> H.
reflexivity.
Qed.
Print iden_eq_short.

Hint Rewrite id_r id_l : ids.
Theorem iden_eq_short_auto:
  (forall b, b <+> m = b) ->
  (forall b, e <+> b = b) ->
  forall b, b <+> (e <+> m) = b.
intros.
autorewrite with ids in *.
reflexivity.
Qed.

Print iden_eq_short_auto.

(* really long proof, theoretically right,
but we want to prevent this from happening *)
Theorem iden_eq_long_plus:
  (forall a, a <+> m = a) ->
  (forall a, e <+> a = a) ->
  forall a, a <+> (e <+> m) = a.
intros.
rewrite <- H0.
rewrite <- H0.
rewrite <- H0.
rewrite <- H0.
rewrite <- H0.
rewrite -> H0.
rewrite -> H.
rewrite -> H0.
rewrite -> H0.
rewrite -> H0.
rewrite -> H0.
rewrite -> H0.
reflexivity.
Qed.

Hint Rewrite id_r id_l id_r_o : ids_new.
Theorem iden_plus_o:
  (forall a, a <+> m = a) ->
  (forall a, z <o> a = a) ->
  forall b, (z <o> ((z <o> b) <+> m)) = b.
  (* make this really complicated, add new identities as in previous two lines? *)
Proof.
  intros.
  autorewrite with ids_new in *.
  reflexivity. 
Qed.

(*
Print iden_plus_o.

Hint Rewrite id_r id_l id_r_o : ids_new.
Theorem iden_plus_o_alt:
  (forall a, a <+> m = a) ->
  (forall a, z <o> a = a) ->
  forall b, (z <o> ((z <o> b) <+> m)) = b. 
Proof.
(* Follow the computer! *)
Admitted.

Print iden_plus_o_alt.

(* fancy omega---could we learn it? *)
Lemma odds_arent_even:
forall a b: nat, 2*a + 1 <> 2*b.
Proof.
  intros.
  omega.
Qed.
*)
End Group.