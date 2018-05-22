from pycoqtop.coqtop import CoqTop
from recon.tacst_parser import TacStParser


class PyCoqProver(object):
    """A Python prover that constructs simple Coq proofs.
    """
    def __init__(self, policy, lemma, prelude, tcoq_dump_path="/tmp/tcoq.log", f_log=True):
        # Internal state
        self.policy = policy
        self.lemma = lemma
        self.prelude = prelude
        self.tcoq_dump_path = tcoq_dump_path
        self.f_log = f_log

        # Proof state
        self.decoder = None
        self.last_res = None
        self.ctx = None
        self.concl_idx = None

        self.proof = ["intros."]
        self.good_choices = 0
        self.num_steps = 0
        self.bad_steps = set()

        # Intializing CoqTop and send the prelude (if any)
        self.top = CoqTop()
        self.top.__enter__()
        self.top.sendone(prelude)

        # Initializing proof
        self.top.sendone(lemma)
        self.top.sendone("Proof.")
        res = self.top.sendone("intros.")
        self._load_tcoq_result(res)

    # -------------------------------------------------
    # Helper

    def _log(self, msg):
        if self.f_log:
            print(msg)

    def _is_success(self, msg):
        return "Error" not in msg

    def _dump_ctx(self):
        for ident, typ_idx, _ in self.ctx:
            self._log("id({}): {}".format(ident, typ_idx, self.decoder.decode_exp_by_key(typ_idx)))
        if self.concl_idx != -1:
            c = self.decoder.decode_exp_by_key(self.concl_idx)
            self._log("concl({}): {}".format(self.concl_idx, c))

    def _load_tcoq_result(self, res):
        # Update result
        self.last_res = res

        # TODO(deh): can optimize to not read whole file
        # Parse and update AST decoder
        ts_parser = TacStParser(self.tcoq_dump_path)
        lemma = ts_parser.parse_partial_lemma()
        self.decoder = lemma.decoder

        if self._is_success(res):
            # Update contex and conclusion if we made progress
            decl = lemma.decls[-1]
            self.ctx = decl.ctx.traverse()
            self.concl_idx = decl.concl_kdx
            self._dump_ctx()

    # -------------------------------------------------
    # API

    def sep_eq_goal(self, c):
        # 0 is I(Coq.Init.Logic.eq.0, )
        left_c = c.cs[1]
        right_c = c.cs[2]
        return left_c, right_c

    def is_proof_complete(self):
        # TODO(deh): Only works for straight-line proofs right now
        res = self.top.sendone("reflexivity.")
        if self._is_success(res):
            self.top.sendone("Qed.")
            return True
        else:
            return False

    def attempt_proof_step(self):
        self.num_steps += 1

        # 1. Obtain goal
        goal_c = self.decoder.decode_exp_by_key(self.concl_idx)
        left_c, right_c = self.sep_eq_goal(goal_c)

        # 2. Compute and take next step.
        #    We assume the expression to simplify is on the left.
        step = self.policy.next_proof_step(left_c)
        res = self.top.sendone(step)
        self._log(res)
        if self._is_success(res):
            self.proof += [step]
        else:
            return None

        # 3. Prepare for next iteration.
        self._load_tcoq_result(res)

        return self._is_success(res)

    def attempt_proof(self):
        while not self.is_proof_complete():
            if self.attempt_proof_step():
                self.good_choices += 1
        self.proof += ["reflexivity."]

    def extract_proof(self):
        return "\n".join([self.lemma, "Proof."] + self.proof + ["Qed."])
