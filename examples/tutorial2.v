Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrnat.

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
End Smullyan_drinker.