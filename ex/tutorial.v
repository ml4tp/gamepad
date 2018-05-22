Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrnat.

Section HilbertSaxiom.
  Variables A B C : Prop.
  Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C.
  Proof.
    (* move => is equivalent to move=>, 
     * equivalent to intros hAiBiC hAiB hA
     * moves hypotheses into context
     * move is a tactic, => is a tactical 
     * move does nothing, *)
    move => hAiBiC hAiB hA.
    (* move : is equivalent to move:,
     * equivalent to revert hAiBiC
     * almost equivalent to generalize hAiBiC (which leaves in context) *)
    move : hAiBiC.
    apply.
      by [].
    (* apply : hAiB. is equivalent to move : hAiB. apply. *)
    (* move: hAiB; apply. *)
      (* move : hAiB. apply. by []. is equivalent to the below. *)
    by apply: hAiB.
  Qed.

  Hypotheses (hAiBiC : A -> B -> C) (hAiB : A -> B) (hA : A).
  Lemma HilbertS2 : C.
  Proof.
    (* only apply: hA to first subgoal generated. *)
    apply: hAiBiC; first by apply: hA.
    (* exact is kind of equivalent to apply. by []. *)
    (* below is equivalent to move: hAiB; exact. *)
    exact : hAiB.
  Qed.

  Lemma HilbertS3 : C.
  Proof.
    (* apply: hAiBiC; last exact: hAiB; exact. *)
    by [apply: hAiBiC; last exact: hAiB].
  Qed.

  Lemma HilbertS4 : C.
  Proof.
    exact: (hAiBiC _ (hAiB _)).
  Qed.

  Lemma HilbertS5 : C.
  Proof.
    exact: hAiBiC (hAiB _).
  Qed.

  Lemma HilbertS6 : C.
  Proof.
    exact: HilbertS5.
  Qed.

End HilbertSaxiom.

Section Symmetric_Conjunction_Disjunction.
  Lemma andb_sym : forall A B : bool, A && B -> B && A.
  Proof.
    case.
    (* case; by []. is equivalent to below. *)
    by case.  
      by [].
  Qed.

  Lemma andb_sym2 : forall A B : bool, A && B -> B && A.
  Proof.
    by [case; case].
  Qed.

  Lemma andb_sym3 : forall A B : bool, A && B -> B && A.
  Proof.
    by do 2! case.
  Qed.

  Lemma and_sym : forall A B : Prop, A /\ B -> B /\ A.
  Proof.
    (* move => A1 B; case. is equvialent to move => A1 B []. wtf??? *)
    by [move => A1 B []].
  Qed.

  Lemma or_sym : forall A B : Prop, A \/ B -> B \/ A.
  Proof.
    (* move => A B; case => [hA | hB]. is equivalent to 
     * move=> A B [hA | hB]. *)    
    (* move : or_intror. apply. is equivalent to apply : or_intror. *)
    by move=> A B [hA | hB]; [apply: or_intror | apply: or_introl].
  Qed.

  Lemma or_sym2 : forall A B : bool, A \/ B -> B \/ A.
  Proof.
    (* apply / orP.  the / means apply it to the goal. *)
    (* move: AorB; move/orP. is equivalent to  move/orP : AorB. *)
      by move=> [] [] AorB; apply/orP; move/orP : AorB.
  Qed.

End Symmetric_Conjunction_Disjunction.


Section R_sym_trans.
  Variables (D : Type) (R : D -> D -> Prop).
  Hypothesis R_sym : forall x y, R x y -> R y x.
  Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.
  
  Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
  Proof.
    (* move=> x; case=> y Rxy. equivalent to below *)
    move=> x [y Rxy].
      by apply: R_trans _ _ _ _ (R_sym _ y _).
  Qed.
End R_sym_trans.


Section Smullyan_drinker.
  Variables (D : Type)(P : D -> Prop).
  Hypothesis (d : D) (EM : forall A, A \/ ~A).

  Lemma drinker : exists x, P x -> forall y, P y.
  Proof.
    (* case: (EM (exists y, ~P y)) is equivalent to move: (EM (exists y, ~P y)); case. *)
    case: (EM (exists y, ~P y)) => [[y notPy]| nonotPy]; first by exists y.
    (*
      exists d => _ y.
      case : (EM (P y)).
        done.
        move => notPy.
    *)
    exists d => _ y; case: (EM (P y)) => // notPy.
    by case: nonotPy; exists y.
  Qed.

  Lemma drinker2 : exists x, P x -> forall y, P y.
  Proof.
    case: (EM (exists y, ~P y)) => [[y notPy]| nonotPy]; first by exists y.
    exists d => _ y.
    case : (EM (P y)).
    + done.
    + move => notPy.                                                                    
      by case: nonotPy; exists y.
  Qed.
      
  Lemma drinker_unfold : exists x, P x -> forall y, P y.
  Proof.
    (* case: (EM (exists y, ~P y)) is equivalent to move: (EM (exists y, ~P y)); case. *)
    (* case: (EM (exists y, ~P y)) => [[y notPy]| nonotPy]; first by exists y. *)
    move : (EM (exists y, ~P y)).
    case.
    + move => [y notPy].
      exists y.
        by [].
    + move => nonotPy.

      (* exists d => _ y; case: (EM (P y)) => // notPy. *)
      exists d.
      move => foo y.
      move : (EM (P y)).
      case => // notPy.
    
      (* by case: nonotPy; exists y. *)
      move : nonotPy.
      case.
      exists y.
        by [].
  Qed.
End Smullyan_drinker.


Section Equality.
  Variable f : nat -> nat.

  Hypothesis f00 : f 0 = 0.
  Lemma fkk : forall k, k = 0 -> f k = k.
  Proof.
    move => k k0.
    by rewrite k0.
  Qed.

  Lemma fkk2 : forall k, k = 0 -> f k = k.
  Proof.
    (* move=> k hyp; rewrite {} hyp. by []. *)
    by move=> k ->.
  Qed.

  Variables (D : eqType) (x y : D).
  Lemma eq_prop_bool : x = y -> x == y.
  Proof.
      by move/eqP.
  Qed.
  
  Lemma eq_bool_prop : x == y -> x = y.
  Proof. by move/eqP. Qed.
End Equality.


Section Using_Definition.
  Variable U : Type.
  Definition set := U -> Prop.
  Definition subset (A B : set) := forall x, A x -> B x.
  Definition transitive (T : Type) (R : T -> T -> Prop) :=
    forall x y z, R x y -> R y z -> R x z.

  Lemma subset_trans : transitive set subset.
  Proof.
    (* rewrite /transitive /subset. equivalent to unfold transitive, subset *)
    (* rewrite /transitive /subset; move=> x y z subxy subyz t xt. *)
    (*
    rewrite / transitive.
    rewrite / subset.
    move => x y z subxy subyz t xt.
    *)
    rewrite /transitive /subset => x y z subxy subyz t xt.
      by apply: subyz; apply: subxy.
  Qed.

  Lemma subset_trans2 : transitive set subset.
  Proof.
    (* move forces unfolding *)
    move=> x y z subxy subyz t.
      by move/subxy; move/subyz.
  Qed.
End Using_Definition.