import random

from pycoqtop.coqtop import CoqTop


# 1. Replace random policy (left, right) with learned policy
#    a. fix tcoq to print AST table after each sendone
#    b. use existing stuff to parse context + AST to feed into
#       tac pred + pos eval model
# 2. [DONE] interface with coqtop
# 3. [DONE] sample from policy, send to coqtop, parse result
# 4. Extension is to write which part of goal the model is attending


PREFIX = """(* The set of the group. *)
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
"""


def policy():
    return random.choice(["LEFT", "RIGHT"])


class MyAlgRewriter(object):
    def __init__(self, lemma):
        self.top = CoqTop()
        self.top.__enter__()

        self.top.sendone(PREFIX)
        self.top.sendone(lemma)
        self.top.sendone("Proof.")
        self.top.sendone("intros.")

        self.good_choices = 0
        self.num_steps = 0

    def finalize(self):
        self.top.__exit__()        

    def proof_complete(self):
        # NOTE(deh): only works for straight-line proofs
        res = self.top.sendone("reflexivity.")
        if "Error" not in res:
            self.top.sendone("Qed.")
            return True
        else:
            return False
        # return "Attempt to save an incomplete proof" not in res

    def attempt_proof_step(self):
        self.num_steps += 1
        choice = policy()
        if choice == "RIGHT":
            print("Trying Right")
            res = self.top.sendone("rewrite id_r.")
        else:
            print("Trying Left")
            res = self.top.sendone("rewrite id_l.")
        print(res)
        return "Error" not in res

    def attempt_proof(self):
        while not self.proof_complete():
            if self.attempt_proof_step():
                self.good_choices += 1


LEMMA = "Lemma rewrite_eq_0: forall b, ( e <+> ( ( ( ( b ) <+> m ) <+> m ) <+> m ) ) <+> m = b."


if __name__ == "__main__":
    rw = MyAlgRewriter(LEMMA)
    rw.attempt_proof()
    # rw.finalize()
