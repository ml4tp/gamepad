import random

from pycoqtop.coqtop import CoqTop
from lib.myfile import MyFile
from recon.parse_raw import TacStParser


"""
[Note]

Don't forget to set environment variable of where to load the
intermediate results.

    export TCOQ_DUMP=/tmp/tcoq.log
"""

# 1. Replace random policy (left, right) with learned policy
#    a. [DONE] fix tcoq to print AST table after each sendone
#    b. [DONE] use existing stuff to parse context + AST to feed into
#       tac pred + pos eval model
#    c. Load pretrained model. Use it to do inference. Feed in next state.
# 2. [DONE] interface with coqtop
# 3. [DONE] sample from policy, send to coqtop, parse result
# 4. Extension is to write which part of goal the model is attending
# 5. Generate dataset without myrewrite from dataset with myrewrite
# 6. Train model


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
        self.ts_parser = TacStParser("/tmp/tcoq.log")
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

    def _log(self, msg):
        print(msg)

    def is_success(self, msg):
        return "Error" not in msg

    def load_tcoq_result(self):
        # TODO(deh): can optimize to not read whole file
        # NOTE(deh): export TCOQ_DUMP=/tmp/tcoq.log
        ts_parser = TacStParser("/tmp/tcoq.log")
        lemma = ts_parser.parse_partial_lemma()
        
        # Return decoder, contex, and conclusion
        decl = lemma.decls[-1]
        return lemma.decoder, decl.ctx, decl.concl_idx

    def proof_complete(self):
        # NOTE(deh): only works for straight-line proofs
        res = self.top.sendone("reflexivity.")
        if self.is_success(res):
            self.top.sendone("Qed.")
            return True
        else:
            return False

    def _dump_ctx(self, decoder, ctx, concl_idx):
        self._log("CTX")
        for ident, typ_idx in ctx.traverse():
            self._log(ident, typ_idx, decoder.decode_exp_by_key(typ_idx))
        self._log("CONCL", concl_idx, decoder.decode_exp_by_key(concl_idx))

    def attempt_proof_step(self):
        self.num_steps += 1
        choice = policy()
        if choice == "RIGHT":
            self._log("Trying RIGHT")
            res = self.top.sendone("rewrite id_r.")
        else:
            self._log("Trying RIGHT")
            res = self.top.sendone("rewrite id_l.")
        self._log(res)

        decoder, ctx, concl_idx = self.load_tcoq_result()
        self._dump_ctx(decoder, ctx, concl_idx)
        
        return self.is_success(res), decoder, ctx, concl_idx

    def attempt_proof(self):
        while not self.proof_complete():
            if self.attempt_proof_step():
                self.good_choices += 1


LEMMA = "Lemma rewrite_eq_0: forall b, ( e <+> ( ( ( ( b ) <+> m ) <+> m ) <+> m ) ) <+> m = b."


if __name__ == "__main__":
    rw = MyAlgRewriter(LEMMA)
    rw.attempt_proof()
    # rw.finalize()
