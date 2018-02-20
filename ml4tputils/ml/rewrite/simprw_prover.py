from coq.constr import *
from ml.rewrite.pycoq_prover import PyCoqProver
from ml.tacst_prep import PosEvalPt, Dataset
from ml.rewrite.utils import IdLaw, SimpRWPP, SimpRWRewriter


SIMPRW_PRELUDE = """Require Import mathcomp.ssreflect.ssreflect.

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
"""


class FakeTacEdge(object):
    def __init__(self, name):
        self.name = name


class PyCoqTrainedProver(PyCoqProver):
    """A PyCoq Prover for the simple-rewrite problem that uses a pre-trained model to perform inference.
    """
    def __init__(self, policy, lemma, trainer, train_module="theorems", tcoq_dump_path="/tmp/tcoq.log", f_log=False):
        super().__init__(policy, lemma, prelude=SIMPRW_PRELUDE, tcoq_dump_path=tcoq_dump_path, f_log=f_log)

        # Internal state
        self.trainer = trainer     # PosEvalTrainer
        self.simprw_printer = SimpRWPP()

        # Inferred proof step statistics
        self.num_bad_ast = 0       # The inferred proof step produced an ill-formed AST
        self.num_bad_steps = 0     # The inferred proof step cannot be taken

        # Module shenanigans
        acc = {}
        for k, v in self.trainer.model.const_to_idx.items():
            acc[Name(k.base.replace(train_module, "Top"))] = v
        self.trainer.model.const_to_idx = acc
        self.trainer.tacst_folder[0].tactr.decoder = self.decoder

    def infer_proof_step(self, goal_c):
        # 1. Create data set point
        edge = FakeTacEdge("rewrite")
        poseval_pt = PosEvalPt(0, self.ctx, self.concl_idx, [edge], 0, 0, 0)
        poseval_pt.tac_bin = 0

        # 2. Perform inference and sort by likelihood
        posdir_logits, _, _, _ = self.trainer.forward([(0, poseval_pt)])
        np_posdir_logits = posdir_logits[0].data.numpy()
        posdir_pred = np_posdir_logits.argsort()[::-1]

        # 3. Return the most-likely position and identity law pair
        for idx, posdir in enumerate(posdir_pred):
            if posdir % 2 == 0:
                # Evens encode right-identity
                pos = int(posdir / 2)
                rw_dir = "id_r"
                rw_c = SimpRWRewriter().rewrite(pos, IdLaw.ID_R, goal_c)
            else:
                # Odds encode left-identity
                pos = int((posdir - 1) / 2)
                rw_dir = "id_l"
                rw_c = SimpRWRewriter().rewrite(pos, IdLaw.ID_L, goal_c)

            if rw_c is None:
                return None
            else:
                return "surgery {} ({}) ({}).".format(rw_dir, self.simprw_printer.pp(goal_c),
                                                      self.simprw_printer.pp(rw_c))

    def attempt_proof_step(self):
        self.num_steps += 1

        # 1. Obtain goal
        goal_c = self.decoder.decode_exp_by_key(self.concl_idx)
        left_c, right_c = self.sep_eq_goal(goal_c)

        # 2. Get step from deterministic solver and inferred step.
        step_det = self.policy.next_proof_step(left_c.copy())
        self._log("Deterministic step  : {}".format(step_det))
        step_infer = self.infer_proof_step(left_c.copy())
        self._log("Inferred step       : {}".format(step_infer))

        if step_infer is None:
            # Case A: The inferred step produced a bad AST.
            self.num_bad_ast += 1
            self.bad_points.add(self.num_steps)

            # Take the deterministic solver step.
            self.proof += [step_det]
            res = self.top.sendone(step_det)
        else:
            # Case B: The inferred step produced a well-formed AST.

            # Try to take the inferred step
            res = self.top.sendone(step_infer)
            self._log(res)
            if self._is_success(res):
                # Case B1: The inferred step was successful.
                self.proof += [step_infer]
            else:
                # Case B2: The inferred step was successful.
                self.num_bad_steps += 1
                self.bad_points.add(self.num_steps)

                # Take the deterministic solver step.
                self.proof += [step_det]
                res = self.top.sendone(step_det)

        # 3. Prepare for next the iteration (load result and update AST decoder)
        self._load_tcoq_result(res)
        self.trainer.tacst_folder[0].tactr.decoder = self.decoder

        return self._is_success(res)
