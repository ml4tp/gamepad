import pickle
import random
import json
import torch

from coq.ast import *
from coq.glob_ast import *
from lib.myfile import MyFile
from pycoqtop.coqtop import CoqTop
from recon.parse_raw import TacStParser, FullTac
from ml.tacst_prep import PosEvalPt, Dataset
from coq.parse_sexpr import ParseSexpr


"""
[Note]

Don't forget to set environment variable of where to load the
intermediate results.

    export TCOQ_DUMP=/tmp/tcoq.log

1. Check train/test for duplicates
2. Accuracy code for logits2
3. Use policy greedily
4. Implement beam search
"""


PREFIX = """Require Import mathcomp.ssreflect.ssreflect.

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

(*
Ltac surgery dir e1 e2 :=
  let H := fresh in
  (have H : e1 = e2 by repeat (rewrite dir); reflexivity); rewrite H; clear H.
*)
"""

FILE = "theorems"


# -------------------------------------------------
# Random expressions

class GenAlgExpr(object):
    def __init__(self):
        self.lemma_cnt = 0

    def _select(self, length, gen_red, gen_left, gen_right):
        length1 = random.choice(range(1, length))
        length2 = length - length1
        x = gen_red(length1)
        if random.choice([True, False]):
            y = gen_left(length2)
            return "({} <+> {})".format(y, x)
        else:
            y = gen_right(length2)
            return "({} <+> {})".format(x, y)

    def gen_expr_b(self, length):
        if length == 1:
            return "b"
        elif length > 1:
            return self._select(length, self.gen_expr_b, self.gen_expr_e, self.gen_expr_m)
        else:
            raise NameError("Cannot generate expr that reduces to b")

    def gen_expr_e(self, length):
        if length == 1:
            return "e"
        elif length > 1:
            return self._select(length, self.gen_expr_e, self.gen_expr_e, self.gen_expr_m)
        else:
            raise NameError("Cannot generate expr that reduces to e")

    def gen_expr_m(self, length):
        if length == 1:
            return "m"
        elif length > 1:
            return self._select(length, self.gen_expr_m, self.gen_expr_e, self.gen_expr_m)
        else:
            raise NameError("Cannot generate expr that reduces to m")        

    def gen_lemma(self, length):
        lemma_cnt = self.lemma_cnt
        self.lemma_cnt += 1

        ty = self.gen_expr_b(length)
        return "Lemma rewrite_eq_{}: forall b: G, {} = b.".format(lemma_cnt, ty)


# -------------------------------------------------
# Helper (these are generic Coq ast functions that we should move)
# ughh ... visitor pattern?

def is_leaf(c):
    typ = type(c)
    if typ is VarExp or typ is ConstExp:
        return True
    elif typ is AppExp:
        return False
    else:
        raise NameError("Shouldn't happen {}".format(c))

class PreOrder(object):
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
            raise NameError("Shouldn't happen {}".format(c))

    def _traverses(self, cs):
        for c in cs:
            self._traverse(c)


class AstOp(object):
    def __init__(self):
        pass
    
    def _tag(self, c_orig, c_new):
        c_new.tag = c_orig.tag
        return c_new

    def copy(self, c):
        # TODO(deh): probably make this a member function
        typ = type(c)
        if typ is VarExp:
            return self._tag(c, VarExp(c.x))
        elif typ is ConstExp:
            return self._tag(c, ConstExp(c.const, c.ui))
        elif typ is AppExp:
            c_p = self.copy(c.c)
            cs_p = self.copys(c.cs)
            return self._tag(c, AppExp(c_p, cs_p))
        else:
            raise NameError("Shouldn't happen {}".format(c))

    def copys(self, cs):
        return [self.copy(c) for c in cs]

    def eq(self, c1, c2):
        # TODO(deh): probably make this a member function
        typ1, typ2 = type(c1), type(c2)
        if typ1 is VarExp and typ2 is VarExp:
            return c1.x == c2.x
        elif typ1 is ConstExp and typ2 is ConstExp:
            return c1.const == c2.const
        elif typ1 is AppExp and typ2 is AppExp:
            b1 = self.eq(c1.c, c2.c)
            b2 = self.eqs(c1.cs, c2.cs)
            return all(lambda x: x, )
        else:
            # TODO(deh): more cases ...
            return False

    def eqs(self, cs1, cs2):
        if len(cs1) == len(cs2):
            return all(lambda x: x, [self.eq(c1, c2) for c1, c2 in zip(cs1, cs2)])
        else:
            return False

    def staple(self, c_skel, pos, c_subst):
        self.pos = 0
        return self._staple(c_skel, pos, c_subst)

    def _staple(self, c_skel, pos, c_subst):
        if self.pos == pos:
            self.pos += 1
            return c_subst
        else:
            self.pos += 1

        typ = type(c_skel)
        if typ is VarExp:
            return c_skel
        elif typ is ConstExp:
            return c_skel
        elif typ is AppExp:
            c_p = self._staple(c_skel.c, pos, c_subst)
            cs_p = self._staples(c_skel.cs, pos, c_subst)
            return self._tag(c_skel, AppExp(c_p, cs_p))
        else:
            raise NameError("Shouldn't happen {}".format(c))

    def _staples(self, cs, pos, c_subst):
        return [self._staple(c, pos, c_subst) for c in cs]

    def rewrite(self, pos, rw_dir, c):
        print("REWRITING POS", pos, "DIR", rw_dir, "EXP", c)
        self.pos = 0
        self.found = False
        rw_c = self._rewrite(pos, rw_dir, c)
        if self.found:
            return rw_c
        else:
            return None

    def _rewrite(self, pos, rw_dir, c):
        typ = type(c)
        if typ is VarExp:
            self.pos += 1
            return c
        elif typ is ConstExp:
            self.pos += 1
            return c
        elif typ is AppExp:
            if self.pos == pos:
                if rw_dir == 0:
                    # use id_r
                    self.pos += 1
                    self.found = True
                    return c.cs[0]
                else:
                    # use id_l
                    self.pos += 1
                    self.found = True
                    return c.cs[1]
            self.pos += 1
            c_p = self._rewrite(pos, rw_dir, c.c)
            c1 = self._rewrite(pos, rw_dir, c.cs[0])
            c2 = self._rewrite(pos, rw_dir, c.cs[1])
            return AppExp(c_p, [c1, c2])
        else:
            raise NameError("Shouldn't happen {}".format(c))


# -------------------------------------------------
# Simple algebraic problem

class RandAlgPolicy(object):
    """A random policy that
    1. Picks a random place in the AST
    2. Attempts a left or right rewrite
    """
    def __init__(self):
        pass

    def next_proof_step(self, goal_c):
        rw_dir, rw_c = self._select(goal_c)
        return "surgery {} ({}) ({}).".format(rw_dir, self._pp(goal_c), self._pp(rw_c))

    def _locate_b(self, orig_c, inorder):
        # Compute the position of b
        for idx, c_p in inorder:
            if isinstance(c_p, VarExp) and c_p.x == "b":
                return idx
        raise NameError("Variable b not found in {}".format(self._pp(orig_c)))

    def _count(self, preorder):
        cnt_e = 0
        cnt_m = 0
        for pos, c in preorder:
            if isinstance(c, ConstExp):
                if c.const == Name("Top.m"):
                    cnt_m += 1
                elif c.const == Name("Top.e"):
                    cnt_e += 1
        return cnt_e, cnt_m

    def _reduce2(self, red, c):
        self.elim_m = False
        self.elim_e = False
        return self._reduce(red, c)

    def _reduce(self, red, c):
        if self.elim_m or self.elim_e:
            return c

        typ = type(c)
        if typ is VarExp:
            return c
        elif typ is ConstExp:
            return c
        elif typ is AppExp:
            left_c = c.cs[0]
            right_c = c.cs[1]
            if red == "e":
                print("REDUCING e", self._pp(c))
                if isinstance(right_c, ConstExp) and right_c.const == Name("Top.m"):
                    self.elim_m = True
                    return left_c
                elif isinstance(left_c, ConstExp) and left_c.const == Name("Top.e") and is_leaf(right_c):
                    self.elim_e = True
                    return right_c
                else:
                    c1 = self._reduce("e", left_c)
                    c2 = self._reduce("m", right_c)
                    return AppExp(c.c, [c1, c2])
            elif red == "m":
                print("REDUCING m", self._pp(c))
                if isinstance(left_c, ConstExp) and left_c.const == Name("Top.e"):
                    self.elim_e = True
                    return right_c
                elif isinstance(right_c, ConstExp) and right_c.const == Name("Top.m") and is_leaf(left_c):
                    self.elim_m = True
                    return left_c
                else:
                    c1 = self._reduce("e", left_c)
                    c2 = self._reduce("m", right_c)
                    return AppExp(c.c, [c1, c2])
            elif red == "em":
                print("REDUCING em", self._pp(c))
                preorder_p = [(pos, c_p) for pos, c_p in enumerate(PreOrder().traverse(right_c))]
                cnt_e, cnt_m = self._count(preorder_p)
                if isinstance(right_c, ConstExp) and right_c.const == Name("Top.m"):
                    self.elim_m = True
                    return left_c
                elif isinstance(left_c, ConstExp) and left_c.const == Name("Top.e") and cnt_e >= 1:
                    self.elim_e = True
                    return right_c
                else:
                    c1 = self._reduce("e", left_c)
                    c2 = self._reduce("m", right_c)
                    return AppExp(c.c, [c1, c2])
            elif red == "me":
                print("REDUCING me", self._pp(c))
                preorder_p = [(pos, c_p) for pos, c_p in enumerate(PreOrder().traverse(left_c))]
                cnt_e, cnt_m = self._count(preorder_p)
                if isinstance(left_c, ConstExp) and left_c.const == Name("Top.e"):
                    self.elim_e = True
                    return right_c
                elif isinstance(right_c, ConstExp) and right_c.const == Name("Top.m") and cnt_m >= 1:
                    self.elim_m = True
                    return left_c
                else:
                    c1 = self._reduce("e", left_c)
                    c2 = self._reduce("m", right_c)
                    return AppExp(c.c, [c1, c2])
            else:
                raise NameError("Shouldn't happen")
        else:
            raise NameError("I'm tired of these motherf*cking snakes on this motherf*cking plane {}.".format(c))

    def _select(self, c):
        # side = random.choice(["LEFT", "RIGHT"])
        cnt = 0
        while cnt < 10:
            cnt += 1
            c_p = self._reduce2("e", c)
            if self.elim_e:
                return "id_l", c_p
            elif self.elim_m:
                return "id_r", c_p
        assert False

    def _strip(self, name):
        # Convert Top.name into name
        loc = name.rfind('.')
        return name[loc+1:]

    def _pp(self, c):
        typ = type(c)
        if typ is VarExp:
            return self._strip(str(c.x))
        elif typ is ConstExp:
            return self._strip(str(c.const))
        elif typ is AppExp:
            s_op = self._pp(c.c)
            s_left = self._pp(c.cs[0])
            s_right = self._pp(c.cs[1])
            return "({} {} {})".format(s_op, s_left, s_right)


# -------------------------------------------------
# Prover

class PyCoqAlgProver(object):
    def __init__(self, policy, lemma):
        # Internal state
        self.ts_parser = TacStParser("/tmp/tcoq.log")
        self.policy = policy
        self.lemma = lemma

        # Intializing CoqTop
        self.top = CoqTop()
        self.top.__enter__()
        self.top.sendone(PREFIX)
        
        # Initializing proof
        self.top.sendone(lemma)
        self.top.sendone("Proof.")
        res = self.top.sendone("intros.")
        self.load_tcoq_result(res)
        print("AFTER INTROS")

        # Proof state
        self.proof = ["intros."]
        self.good_choices = 0
        self.num_steps = 0
        self.bad_points = set()

    def finalize(self):
        self.top.__exit__()        

    def _log(self, msg):
        print(msg)

    def is_success(self, msg):
        return "Error" not in msg

    def load_tcoq_result(self, res):
        # TODO(deh): can optimize to not read whole file
        # NOTE(deh): export TCOQ_DUMP=/tmp/tcoq.log
        ts_parser = TacStParser("/tmp/tcoq.log")
        lemma = ts_parser.parse_partial_lemma()
        self.decoder = lemma.decoder
        self.last_res = res

        if self.is_success(res):
            # Set contex and conclusion
            decl = lemma.decls[-1]
            self.ctx = decl.ctx.traverse()
            self.concl_idx = decl.concl_idx
            
            goal_c = self.decoder.decode_exp_by_key(self.concl_idx)
            left_c, right_c = self.sep_eq_goal(goal_c)
            print("DOING", self.policy._pp(goal_c))
            print("LEFT", self.policy._pp(left_c))
            print("RIGHT", self.policy._pp(right_c))

    def proof_complete(self):
        # NOTE(deh): only works for straight-line proofs
        res = self.top.sendone("reflexivity.")
        if self.is_success(res):
            self.top.sendone("Qed.")
            return True
        else:
            return False

    def sep_eq_goal(self, c):
        # 0 is I(Coq.Init.Logic.eq.0, )
        left_c = c.cs[1]
        right_c = c.cs[2]
        return left_c, right_c

    def _dump_ctx(self):
        for ident, typ_idx in self.ctx:
            self._log("id({}): {}".format(ident, typ_idx, self.decoder.decode_exp_by_key(typ_idx)))
        if self.concl_idx != -1:
            c = self.decoder.decode_exp_by_key(self.concl_idx)
            self._log("concl({}): {}".format(self.concl_idx, c))

    def attempt_proof_step(self):
        self.num_steps += 1

        # 1. Obtain goal
        goal_c = self.decoder.decode_exp_by_key(self.concl_idx)
        left_c, right_c = self.sep_eq_goal(goal_c)
        
        # 2. Compute and take next step
        # NOTE(deh): we assume the thing to simplify is on the left
        step = self.policy.next_proof_step(left_c)
        print("STEP", step)
        res = self.top.sendone(step)
        self._log(res)
        if self.is_success(res):
            self.proof += [step]
        else:
            return None
        
        # 3. Prepare for next iteration
        self.load_tcoq_result(res)
        # self._dump_ctx()
        
        return self.is_success(res)

    def attempt_proof(self):
        while not self.proof_complete():
            if self.attempt_proof_step():
                self.good_choices += 1
        self.proof += ["reflexivity."]

    def extract_proof(self):
        return "\n".join([self.lemma, "Proof."] + self.proof + ["Qed."])


class FakeTacEdge(object):
    def __init__(self, name):
        self.name = name


class PyCoqAlgTrainedProver(PyCoqAlgProver):
    def __init__(self, policy, lemma, trainer):
        super().__init__(policy, lemma)
        self.trainer = trainer
        # Module shenanigans
        acc = {}
        for k, v in self.trainer.model.const_to_idx.items():
            acc[Name(k.base.replace(FILE, "Top"))] = v
        self.trainer.model.const_to_idx = acc
        self.trainer.tacst_folder[0].tactr.decoder = self.decoder
        
        self.pos_of_pred = {}
        for k in range(20):
            self.pos_of_pred[k] = 0
        self.bad_steps = 0
        self.bad_ast = 0

    def replace_const(self, decoded):
        acc = {}
        for k, v in decoded.items():
            c = decoded[k]
            if isinstance(c, ConstExp):
                acc[k] = ConstExp(Name(c.const.base.replace("Top", FILE)), c.ui)
                print("REPLACE", acc[k])
            else:
                acc[k] = c
                # acc[k].const.base = decoded[k].const.base.replace("Top", FILE)
        return acc

    def get_proof_step(self, goal_c):
        edge = FakeTacEdge("rewrite")
        poseval_pt = PosEvalPt(0, self.ctx, self.concl_idx, [edge], 0, 0, 0)
        poseval_pt.tac_bin = 0

        (pos_logits, dir_logits), _, _, _ = self.trainer.forward([(0, poseval_pt)])
        print("Pos logits", pos_logits)
        print("Dir logits", dir_logits)
        pos_values, pos_indices = pos_logits[0].max(0)
        print("Pos Values", pos_values, "Pos Index", pos_indices)
        dir_values, dir_indices = dir_logits[0].max(0)
        print("Dir Values", dir_values, "Dir Index", dir_indices)

        np_pos_logits = pos_logits[0].data.numpy()
        pos_pred = np_pos_logits.argsort()[::-1]
        for idx, pos in enumerate(pos_pred):
            rw_c = AstOp().rewrite(pos, dir_indices.data[0], goal_c)
            if rw_c != None:
                self.pos_of_pred[idx] += 1
                break
            else:
                return None
        # print("REWRITING", self.policy._pp(goal_c), self.policy._pp(rw_c))
        # assert False
        if dir_indices.data[0] == 0:
            rw_dir = "id_r"
        else:
            rw_dir = "id_l"
        return "surgery {} ({}) ({}).".format(rw_dir, self.policy._pp(goal_c), self.policy._pp(rw_c))

    def get_proof_step2(self, goal_c):
        edge = FakeTacEdge("rewrite")
        poseval_pt = PosEvalPt(0, self.ctx, self.concl_idx, [edge], 0, 0, 0)
        poseval_pt.tac_bin = 0

        posdir_logits, _, _, _ = self.trainer.forward([(0, poseval_pt)])
        posdir_values, posdir_indices = posdir_logits[0].max(0)
        np_posdir_logits = posdir_logits[0].data.numpy()
        posdir_pred = np_posdir_logits.argsort()[::-1]

        for idx, posdir in enumerate(posdir_pred):
            if posdir % 2 == 0:
                pos = int(posdir / 2)
                rw_dir = "id_r"
                rw_c = AstOp().rewrite(pos, 0, goal_c)
            else:
                pos = int((posdir - 1) / 2)
                rw_dir = "id_l"
                rw_c = AstOp().rewrite(pos, 1, goal_c)

            if rw_c == None:
                return None
            else:
                return "surgery {} ({}) ({}).".format(rw_dir, self.policy._pp(goal_c), self.policy._pp(rw_c))

    def attempt_proof_step(self):
        self.num_steps += 1

        # 1. Obtain goal
        # print("PROOF KEYS", self.decoder.decoded.keys())
        # print("TRAINER KEYS", self.trainer.tacst_folder[0].tactr.decoder.decoded.keys())
        goal_c = self.decoder.decode_exp_by_key(self.concl_idx)
        left_c, right_c = self.sep_eq_goal(goal_c)
        
        step_det = self.policy.next_proof_step(AstOp().copy(left_c))
        print("STEP", step_det)

        step_infer = self.get_proof_step2(AstOp().copy(left_c))
        print("PREDICTED STEP", step_infer)

        # res = self.top.sendone(step_det)
        # self._log(res)
        # if self.is_success(res):
        #     self.proof += [step_det]
        # else:
        #     assert False

        if step_infer == None:
            self.bad_ast += 1
            self.bad_points.add(self.num_steps)
            self.proof += [step_det]
            res = self.top.sendone(step_det)
        else:
            res = self.top.sendone(step_infer)
            self._log(res)
            if self.is_success(res):
                self.proof += [step_infer]
            else:
                self.bad_steps += 1
                self.bad_points.add(self.num_steps)
                self.proof += [step_det]
                res = self.top.sendone(step_det)


        # # 2. Compute and take next step
        # # NOTE(deh): we assume the thing to simplify is on the left
        
        
        # res = self.top.sendone(step)
        # self._log(res)

        # # 3. Prepare for next iteration
        # # self.load_tcoq_result(res)
        # # self.replace_const(self.decoder.decoded)
        # # self.trainer.tacst_folder[0].tactr.decoder = self.decoder
        # # print("HERE", self.decoder.decoded.keys())

        # # 4. Check?
        # if self.is_success(res):
        #     self.proof += [step]
        # else:
        #     # goal_c = self.decoder.decode_exp_by_key(self.concl_idx)
        #     # print("DETERMINISTIC DOING", self.policy._pp(goal_c))
        #     # left_c, right_c = self.sep_eq_goal(goal_c)
        #     step = self.policy.next_proof_step(left_c)
        #     print("DETERMINISTIC STEP", step)
        #     res = self.top.sendone(step)
        #     self._log(res)
        #     self.proof += [step]

        # # 3. Prepare for next iteration
        # self.load_tcoq_result(res)
        # self.replace_const(self.decoder.decoded)
        # self.trainer.tacst_folder[0].tactr.decoder = self.decoder
        
        # 3. Prepare for next iteration
        self.load_tcoq_result(res)
        self.trainer.tacst_folder[0].tactr.decoder = self.decoder
        # self.trainer.tacst_folder[0].tactr.decoder.decoded = self.replace_const(self.decoder.decoded)
        # self._dump_ctx()
        
        return self.is_success(res)


# -------------------------------------------------
# Data stuff

class DiffAst(object):
    def __init__(self):
        self.pos = 0
        self.found = False

    def diff_ast(self, c1, c2):
        self.pos = 0
        self.found = False
        self._diff_ast(c1, c2)
        if not self.found:
            assert False
        return self.pos        

    def _diff_ast(self, c1, c2):
        if isinstance(c1, GRef) and isinstance(c2, GRef):
            if not self.found:
                self.pos += 1
        elif isinstance(c1, GVar) and isinstance(c2, GVar):
            if not self.found:
                self.pos += 1
        elif isinstance(c1, GApp) and isinstance(c2, GApp):
            if not self.found:
                self.pos += 1
                self._diff_ast(c1.g, c2.g)
                for c1_p, c2_p in zip(c1.gs, c2.gs):
                    if not self.found:
                        self._diff_ast(c1_p, c2_p)
        else:
            self.found = True
            return self.pos


def get_lemmas(lemma_ids):
    # foobar = ["rewrite_eq_{}".format(lemid) for lemid in lemma_ids]

    lemmas = {}
    with open("{}.v".format(FILE), 'r') as f:
        for line in f:
            line = line.strip()
            if "Lemma rewrite_eq" in line:
                idx = line.find(':')
                lemma2 = line[6:idx]
                for lemid in lemma_ids:
                    if "rewrite_eq_{}".format(lemid) == lemma2:
                        lemmas[lemid] = line
                        break
    print("LEMMAS", lemma_ids.difference(set(lemmas.keys())))
    return lemmas


def to_goalattn_dataset(poseval_dataset):    
    def clean(orig):
        dataset = []
        positions = [0 for _ in range(20)]
        for tactr_id, pt in orig:
            # Item 3 contains [TacEdge]
            tac = pt.tacst[3][-1]
            if tac.name.startswith("surgery"):
                args = tac.ftac.tac_args
                rw_dir = ParseSexpr().parse_glob_constr(args[0])
                orig_ast = ParseSexpr().parse_glob_constr(args[1])
                rw_ast = ParseSexpr().parse_glob_constr(args[2])
                pos = DiffAst().diff_ast(orig_ast, rw_ast)
                # print("DIFF", pos, orig_ast, rw_ast)
                # Put the tactic in tac_bin
                # Put the position of the ast in the subtr_bin
                positions[pos] += 1
                if "{}.id_r".format(FILE) in tac.ftac.gids:
                    pt.tac_bin = 0
                    pt.subtr_bin = pos
                    dataset += [(tactr_id, pt)]
                elif "{}.id_l".format(FILE) in tac.ftac.gids:
                    pt.tac_bin = 1
                    pt.subtr_bin = pos
                    dataset += [(tactr_id, pt)]
                else:
                    assert False
        print(positions)
        return dataset

    def clean2(orig):
        dataset = []
        positions = [0 for _ in range(40)]
        for tactr_id, pt in orig:
            # Item 3 contains [TacEdge]
            tac = pt.tacst[3][-1]
            if tac.name.startswith("surgery"):
                args = tac.ftac.tac_args
                rw_dir = ParseSexpr().parse_glob_constr(args[0])
                orig_ast = ParseSexpr().parse_glob_constr(args[1])
                rw_ast = ParseSexpr().parse_glob_constr(args[2])
                pos = DiffAst().diff_ast(orig_ast, rw_ast)
                # print("DIFF", pos, orig_ast, rw_ast)
                # Put the tactic in tac_bin
                # Put the position of the ast in the subtr_bin
                if "{}.id_r".format(FILE) in tac.ftac.gids:
                    pt.tac_bin = 0
                    pt.subtr_bin = 2 * pos
                    positions[2 * pos] += 1
                    dataset += [(tactr_id, pt)]
                elif "{}.id_l".format(FILE) in tac.ftac.gids:
                    pt.tac_bin = 1
                    pt.subtr_bin = 2 * pos + 1
                    positions[2 * pos + 1] += 1
                    dataset += [(tactr_id, pt)]
                else:
                    assert False
        print(positions)
        return dataset

    train = clean2(poseval_dataset.train)
    test = clean2(poseval_dataset.test)
    seen = set()
    for tactr_id, pt in test:
        seen.add(tactr_id)
    print("TEST", len(seen), seen)
    test_lemmas = get_lemmas(seen)
    val = clean2(poseval_dataset.val)
    seen = set()
    for tactr_id, pt in val:
        seen.add(tactr_id)
    print("VALID", len(seen), seen)
    val_lemmas = get_lemmas(seen)
    print("LEN", len(val_lemmas))
    return Dataset(train, test, val), test_lemmas, val_lemmas


# LEMMA = "Lemma rewrite_eq_0: forall b, ( e <+> ( ( ( ( b ) <+> m ) <+> m ) <+> m ) ) <+> m = b."
# LEMMA = "Lemma rewrite_eq_0: forall b: G, ((b <+> m) <+> (m <+> ((e <+> (m <+> m)) <+> (e <+> ((e <+> e) <+> m))))) = b."
# LEMMA = "Lemma rewrite_eq_0: forall b: G, ((e <+> (b <+> (e <+> m))) <+> m) = b."
# LEMMA = "Lemma rewrite_eq_49: forall b: G, (b <+> (((e <+> e) <+> (e <+> e)) <+> m)) <+> (e <+> m) = b."
# LEMMA = "Lemma rewrite_eq_0: forall b: G, (b <+> (m <+> (e <+> (e <+> ((e <+> e) <+> m))))) = b."
# LEMMA = "Lemma rewrite_eq_432: forall b: G, (((e <+> m) <+> ((e <+> m) <+> m)) <+> (((e <+> m) <+> b) <+> (e <+> m))) = b."

# LEMMA = "Lemma rewrite_eq_191: forall b: G, ((e <+> m) <+> ((e <+> (e <+> e)) <+> (e <+> ((e <+> m) <+> (b <+> m))))) = b."
# LEMMA = "Lemma rewrite_eq_259: forall b: G, ((((e <+> m) <+> e) <+> (e <+> e)) <+> ((e <+> m) <+> ((e <+> m) <+> b))) = b."
# LEMMA = "Lemma rewrite_eq_83: forall b: G, ((e <+> (b <+> m)) <+> (((e <+> m) <+> (e <+> m)) <+> (m <+> (m <+> m)))) = b."
LEMMA = "Lemma rewrite_eq_4: forall b: G, (((e <+> (e <+> (((e <+> m) <+> m) <+> (m <+> m)))) <+> m) <+> (e <+> b)) = b."


def run(trainer, test_lemmas, val_lemmas):
    # try:
    #     rewriter = PyCoqAlgTrainedProver(RandAlgPolicy(), LEMMA, trainer)
    #     rewriter.attempt_proof()
    #     print("BAD STEPS", rewriter.bad_steps)
    #     print("TOTAL STEPS", rewriter.num_steps)
    #     print("POSOFPRED", rewriter.pos_of_pred)
    # except:
    #     print("FAILURE")
    #     print(rewriter.last_res)
    #     print("POSOFPRED", rewriter.pos_of_pred)

    stats = {}
    bad = set()
    cnt = 0
    for lem_id, lemma in val_lemmas.items():
        #try:
        rewriter = PyCoqAlgTrainedProver(RandAlgPolicy(), lemma, trainer)
        rewriter.attempt_proof()
        print("BAD STEPS", rewriter.bad_steps)
        print("TOTAL STEPS", rewriter.num_steps)
        stats[lem_id] = {"lemma": lemma, "bad": rewriter.bad_steps, "total": rewriter.num_steps, "badpoints": list(rewriter.bad_points), "ast": rewriter.bad_ast}
        assert rewriter.num_steps == 9
        # except:
        #     bad.add(lemma)
        #     cnt += 1
        #     stats[lem_id] = {"lemma": lemma, "bad": rewriter.bad_steps, "total": rewriter.num_steps, "badpoints": list(rewriter.bad_points), "ast": rewriter.bad_ast}

    with open('mllogs/simprw.log', 'w') as f:
        f.write(json.dumps([v for k, v in stats.items()]))

    print(len(bad), bad, len(val_lemmas.items()))
    print(len(bad), cnt)


"""
1. [X] Generate a bunch of lemmas
2. [X] Run it through current surgery
3. [X] Dump it into file and run coqc
4. [Y] Fix reconstructor to blacklist surgery
5. Write goal AST attention model
   predict <id_l | id_r> and <loc>
   surgery <id_l | id_r> <loc>
6. Train model
7. [Y] Policy that uses trained model 
"""

random.seed(0)

# orig: ((e <+> (b <+> (e <+> m))) <+> m)
# (f (f e (f b (f e m))) m)
#
# ((f (f e (f b (f e m))) m))
# ((f (f e (f b m)) m))


# b + (e + m) -> b m


"""
1. Percentage of rewrites that are doable
2. Percentage of test lemmas that lead to a complete proof / locally stuck state
3. Try smaller lemmas
4. Try larger lemmas

b + (m + e)
b + (m + (e + m))
b + (m + m)
b + m
b
"""


def test_this():
    # ui = UniverseInstance([])
    f = GRef(ConstRef("Top.f"), [])
    e = GRef(ConstRef("Top.e"), [])
    m = GRef(ConstRef("Top.m"), [])
    b = GVar("b")
    em = GApp(f, [e, m])
    bem = GApp(f, [b, em])
    ebem = GApp(f, [e, bem])
    bm = GApp(f, [b, m])
    ebm = GApp(f, [e, bm])
    print("DIFF", DiffAst().diff_ast(bem, bm))
    print("DIFF", DiffAst().diff_ast(bm, bem))
    print("DIFF", DiffAst().diff_ast(ebem, ebm))
    print("DIFF", DiffAst().diff_ast(ebm, ebem))
    
    ui = UniverseInstance([])
    f2 = ConstExp(Name("Top.f"), ui)
    e2 = ConstExp(Name("Top.e"), ui)
    m2 = ConstExp(Name("Top.m"), ui)
    b2 = VarExp("b")
    em2 = AppExp(f2, [e2, m2])
    bem2 = AppExp(f2, [b2, em2])
    ebem2 = AppExp(f2, [e2, bem2])
    bm2 = AppExp(f2, [b2, m2])
    ebm2 = AppExp(f2, [e2, bm2])
    print("REWRITE", AstOp().rewrite(3, 0, bem2))
    print("REWRITE", AstOp().rewrite(3, 1, bem2))


if __name__ == "__main__":
    num_theorems = 500
    sent_len = 10

    # test_this()

    # lemma = GenAlgExpr().gen_lemma(sent_len)
    # print(lemma)
    
    # policy = RandAlgPolicy()
    # rewriter = PyCoqAlgProver(policy, LEMMA)
    # rewriter.attempt_proof()
    # print(rewriter.extract_proof())

    with open('{}.v'.format(FILE), 'w') as f:
        f.write(PREFIX)
        gen = GenAlgExpr()
        seen = set()
        while True:
            if len(seen) == num_theorems:
                break
            lemma = gen.gen_lemma(sent_len)
            print(lemma)
            if lemma not in seen:
                seen.add(lemma)
                policy = RandAlgPolicy()
                rewriter = PyCoqAlgProver(policy, lemma)
                rewriter.attempt_proof()
                print(rewriter.extract_proof())
                f.write(rewriter.extract_proof())
                f.write('\n\n')


"""
    def _select22(self, mode, c):
        self.elim_e = False
        self.elim_m = False
        return self._select2(mode, c)

    def _select2(self, mode, c):
        if self.elim_e or self.elim_m:
            return c
        typ = type(c)
        if typ is VarExp:
            return c
        elif typ is ConstExp:
            return c
        elif typ is AppExp:
            left_c = c.cs[0]
            right_c = c.cs[1]
            if isinstance(left_c, ConstExp) and left_c.const == Name("Top.e") and mode == "LEFT":
                self.elim_e = True
                return right_c
            elif isinstance(right_c, ConstExp) and right_c.const == Name("Top.m") and mode == "RIGHT":
                self.elim_m = True
                return left_c
            else:
                c1 = self._select2("RIGHT", c.cs[0])
                c2 = self._select2("LEFT", c.cs[1])
                return AppExp(c.c, [c1, c2])
"""
