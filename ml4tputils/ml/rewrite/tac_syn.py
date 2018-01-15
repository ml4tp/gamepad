import random

from pycoqtop.coqtop import CoqTop
from lib.myfile import MyFile
from recon.parse_raw import TacStParser
from tacst_prep import PosEvalPt

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
    def __init__(self, lemma, modelName):
        self.ts_parser = TacStParser("/tmp/tcoq.log")

        self.top = CoqTop()
        self.top.__enter__()
        self.top.sendone(PREFIX)
        self.top.sendone(lemma)
        self.top.sendone("Proof.")
        self.top.sendone("intros.")
        self.load_tcoq_result()

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
        
        # Set decoder, contex, and conclusion
        decl = lemma.decls[-1]
        self.decoder = lemma.decoder
        self.ctx = decl.ctx
        self.concl_idx = decl.concl_idx

    def proof_complete(self):
        # NOTE(deh): only works for straight-line proofs
        res = self.top.sendone("reflexivity.")
        if self.is_success(res):
            self.top.sendone("Qed.")
            return True
        else:
            return False

    def _dump_ctx(self):
        print("CTX")
        for ident, typ_idx in self.ctx.traverse():
            print(ident, typ_idx, self.decoder.decode_exp_by_key(typ_idx))
        print("CONCL", self.concl_idx, self.decoder.decode_exp_by_key(self.concl_idx))

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

        self.load_tcoq_result()
        self._dump_ctx()

        PosEvalPt
        
        return self.is_success(res)

    def attempt_proof(self):
        while not self.proof_complete():
            if self.attempt_proof_step():
                self.good_choices += 1


LEMMA = "Lemma rewrite_eq_0: forall b, ( e <+> ( ( ( ( b ) <+> m ) <+> m ) <+> m ) ) <+> m = b."


if __name__ == "__main__":
    rw = MyAlgRewriter(LEMMA)
    rw.attempt_proof()

    # Inference
    import pickle
    from tacst_prep import PosEvalPt

    import torch

    from ml.poseval.fold_model import PosEvalModel
    from ml.poseval.fold_train import PosEvalTrainer, PosEvalInfer

    print("Loading tactrs ...")
    with open("tactr.pickle", 'rb') as f:
	tactrs = pickle.load(f)

    print("Loading poseval dataset ...")
    with open("poseval.pickle", 'rb') as f:
	poseval_dataset, tokens_to_idx = pickle.load(f)

# Inference
    modelName = "mllogs/model-2018-01-14T185643.886047.params"
    model_infer = PosEvalModel(*tokens_to_idx)
    model_infer.load_state_dict(torch.load(modelName))
    infer = PosEvalInfer(tactrs, model_infer)
    infer.infer(poseval_dataset)
    # rw.finalize()
