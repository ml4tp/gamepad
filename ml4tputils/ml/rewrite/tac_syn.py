import pickle
import random

import torch

from coq.constr import *
from lib.myfile import MyFile
from ml.poseval.fold_model import PosEvalModel
from ml.poseval.fold_train import PosEvalTrainer
from ml.tacst_prep import PosEvalPt, Dataset
from pycoqtop.coqtop import CoqTop
from recon.parse_raw import TacStParser, FullTac

"""
[Note]

Don't forget to set environment variable of where to load the
intermediate results.

    export TCOQ_DUMP=/tmp/tcoq.log

How to run:
python ml4tputils/ml/main.py --end2end --mload mllogs/state_128_lr_0.001_conclu_pos_0_ln_False_drop_0.0_wd_0.0_v_False_attn_False_heads_1_m__r_/2018-01-31T155013.695099.pth --validate
"""


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


class FakeTacEdge(object):
    def __init__(self, name):
        self.name = name


class InOrder(object):
    def __init__(self):
        self.acc = []

    def traverse(self, c):
        self.acc = []
        self._traverse(c)
        return self.acc

    def _traverse(self, c):
        typ = type(c)
        if typ is VarExp:
            self.acc += [c]
        elif typ is ConstExp:
            self.acc += [c]
        elif typ is AppExp:
            self.acc += [c]
            self._traverse(c.c)
            self._traverses(c.cs)
        else:
            raise NameError("TODO")

    def _traverses(self, cs):
        for c in cs:
            self._traverse(c)


class RewritePos(object):
    """Rewrite at a specific position
    """
    def __init__(self):
        self.cnt = 0
        self.pos = 0

    def rewrite(self, pos, c):
        self.cnt = 0
        self.pos = pos
        return self._rewrite(c)

    def _rewrite(self, c):
        if cnt == self.pos:
            if typ is VarExp:
                return None
            elif typ is ConstExp:
                return None
            elif typ is AppExp:
                return c.cs[0], c.cs[1]

        self.cnt += 1
        typ = type(c)
        if typ is VarExp:
            self.acc += [c]
        elif typ is ConstExp:
            self.acc += [c]
        elif typ is AppExp:
            self.acc += [c]
            self._rewrite(c.c)
            self._rewrite(c.cs)
        else:
            raise NameError("TODO")


def separate_goal(c):
    # 0 is I(Coq.Init.Logic.eq.0, )
    left_c = c.cs[1]
    right_c = c.cs[2]
    return left_c, right_c


class MyAlgRewriter(object):
    def __init__(self, trainer, lemma):
        self.ts_parser = TacStParser("/tmp/tcoq.log")

        self.top = CoqTop()
        self.top.__enter__()
        self.top.sendone(PREFIX)
        self.top.sendone(lemma)
        self.top.sendone("Proof.")
        self.top.sendone("intros.")
        self.load_tcoq_result()

        self.trainer = trainer
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
        self.ctx = decl.ctx.traverse()
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
        for ident, typ_idx in self.ctx:
            print(ident, typ_idx, self.decoder.decode_exp_by_key(typ_idx))
        if self.concl_idx != -1:
            c = self.decoder.decode_exp_by_key(self.concl_idx)
            print("CONCL", self.concl_idx, c)
            left_c, right_c = separate_goal(c)
            print("LEFT", left_c)
            print(InOrder().traverse(left_c))
            print("RIGHT", right_c)
            InOrder().traverse(right_c)

    def attempt_proof_step(self):
        # TODO(deh): run infer
        # gid, ctx, concl_idx, tac, tacst_size, subtr_size
        # def __init__(self, gid, ctx, concl_idx, tac, tacst_size, subtr_size):
        edge = FakeTacEdge("rewrite")
        poseval_pt = PosEvalPt(0, self.ctx, self.concl_idx, [edge], 0, 0)
        poseval_pt.tac_bin = 0
        logits, _, _, _ = self.trainer.forward([(0, poseval_pt)])
        print("Prediction", logits[0])
        values, indices = logits[0].max(0)
        print("Values", values, "indicies", indices)

        self.num_steps += 1
        if indices.data[0] == 0:
            self._log("Trying RIGHT")
            res = self.top.sendone("rewrite id_r.")
        elif indices.data[0] == 1:
            self._log("Trying LEFT")
            res = self.top.sendone("rewrite id_l.")

        choice = policy()
        if choice == "RIGHT":
            self._log("Trying RIGHT")
            res = self.top.sendone("rewrite id_r.")
        else:
            self._log("Trying LEFT")
            res = self.top.sendone("rewrite id_l.")
        self._log(res)

        self.load_tcoq_result()
        self._dump_ctx()
        
        return self.is_success(res)

    def attempt_proof(self):
        while not self.proof_complete():
            if self.attempt_proof_step():
                self.good_choices += 1


LEMMA = "Lemma rewrite_eq_0: forall b, ( e <+> ( ( ( ( b ) <+> m ) <+> m ) <+> m ) ) <+> m = b."


def to_tacpred_dataset(poseval_dataset):
    def clean(orig):
        dataset = []
        for tactr_id, pt in orig:
            # Item 3 contains [TacEdge]
            tac = pt.tacst[3][-1]
            if "theorems.id_r" in tac.ftac.gids:
                pt.tac_bin = 0
                dataset += [(tactr_id, pt)]
            elif "theorems.id_l" in tac.ftac.gids:
                pt.tac_bin = 1
                dataset += [(tactr_id, pt)]
        return dataset
    train = clean(poseval_dataset.train)
    test = clean(poseval_dataset.test)
    val = clean(poseval_dataset.val)
    return Dataset(train, test, val)


def end2end(trainer):
   rewriter = MyAlgRewriter(trainer, LEMMA)
   rewriter.attempt_proof()


# if __name__ == "__main__":
#     # Load stuff
#     print("Loading tactrs ...")
#     with open("tactr.pickle", 'rb') as f:
#         tactrs = pickle.load(f)
#     print("Loading poseval dataset ...")
#     with open("poseval.pickle", 'rb') as f:
#         poseval_dataset, tokens_to_idx = pickle.load(f)

#     # TODO(deh): save the model to test_model and load from there
#     # Load model
#     model_name = "mllogs/model-2018-01-14T193916.553740.params"
#     model_infer = PosEvalModel(*tokens_to_idx)
#     model_infer.load_state_dict(torch.load(model_name))
#     infer = PosEvalInfer(tactrs, model_infer)

#     # Run rewriter
#     rw = MyAlgRewriter(infer, LEMMA)
#     rw.attempt_proof()
#     # rw.finalize()
