(* Definition my_true := true. *)
(* Definition my_false := false. *)
(* Definition my_if {A} (e1: bool) (e2 e3: A) := if e1 then e2 else e3. *)

(*
Definition id := (fun x: bool => x).
Definition neg := (fun x: bool => if x then false else true).
Definition and := (fun x y: bool => if x then (if y then true else false) else false).
Definition or := (fun x y: bool => if x then true else y).
 *)

Axiom id : bool -> bool.
Axiom neg : bool -> bool.
Axiom and : bool -> bool -> bool.
Axiom or : bool -> bool -> bool.

Axiom id_spec: forall b: bool, id b = b.

Axiom neg_spec1 : neg true = false.
Axiom neg_spec2 : neg false = true.

Axiom and_spec: and true true = true /\
                and true false = false /\
                and false true = true /\
                and false false = true.

Axiom or_spec: or true true = true /\
               or true false = true /\
               or false true = true /\
               or false false = false.

Lemma foo1 : id true = true.
Proof.
  apply id_spec.
Qed.

Lemma foo2 : forall b: bool, id b = if b then true else false.
Proof.
  intro.
  rewrite id_spec.
  case b.
  reflexivity.
  reflexivity.
Qed.

Lemma foo3 : forall b: bool, id b = neg (neg b).
Proof.
  intro.
  rewrite id_spec.
  case b.
  rewrite neg_spec1.
  rewrite neg_spec2.
  reflexivity.
  rewrite neg_spec2.
  rewrite neg_spec1.
  reflexivity.
Qed.

(*
Lemma foo4 : forall b: bool, forall f: bool -> bool, or (f b) true = true.
Proof.
  intros.
  unfold or.
  case (f b).
  reflexivity.
  reflexivity.
Qed.
*)
