import pickle
import random

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

(*
Ltac surgery dir e1 e2 :=
  match goal with
  | [ |- _ ] =>
    let H := fresh in
    (have H : e1 = e2 by repeat (rewrite dir); reflexivity); rewrite H; clear H
  end.
*)

Ltac surgery dir e1 e2 :=
  let H := fresh in
  (have H : e1 = e2 by repeat (rewrite dir); reflexivity); rewrite H; clear H.

"""


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
        self.pos = 0
        return self._rewrite(rw_dir, c)

    def _rewrite(self, rw_dir, c):
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
                    return c.cs[0]
                else:
                    return c.cs[1]
            self.pos += 1
            c_p = self._rewrite(rw_dir, c)
            c1 = self._rewrite(rw_dir, c.cs[0])
            c2 = self._rewrite(rw_dir, c.cs[1])
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
        self.top.sendone("intros.")
        self.load_tcoq_result()

        # Proof state
        self.proof = ["intros."]
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

    def sep_eq_goal(self, c):
        # 0 is I(Coq.Init.Logic.eq.0, )
        left_c = c.cs[1]
        right_c = c.cs[2]
        return left_c, right_c

    def _dump_ctx(self):
        for ident, typ_idx in self.ctx:
            self.log("id({}): {}".format(ident, typ_idx, self.decoder.decode_exp_by_key(typ_idx)))
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
            assert False
        
        # 3. Prepare for next iteration
        self.load_tcoq_result()
        # self._dump_ctx()
        
        return self.is_success(res)

    def attempt_proof(self):
        while not self.proof_complete():
            if self.attempt_proof_step():
                self.good_choices += 1
        self.proof += ["reflexivity."]

    def extract_proof(self):
        return "\n".join([self.lemma, "Proof."] + self.proof + ["Qed."])


class PyCoqAlgTrainedProver(PyCoqAlgProver):
    def __init__(self, policy, lemma, trainer):
        super().__init__(policy, lemma)
        self.trainer = trainer

    def get_proof_step(self, goal_c):
        edge = FakeTacEdge("rewrite")
        poseval_pt = PosEvalPt(0, self.ctx, self.concl_idx, [edge], 0, 0)
        poseval_pt.tac_bin = 0
        (pos_logits, dir_logits), _, _, _ = self.trainer.forward([(0, poseval_pt)])
        pos_values, pos_indices = pos_logits[0].max(0)
        print("Pos Values", pos_values, "Pos Index", pos_indices)
        dir_values, dir_indices = dir_logits[0].max(0)
        print("Dir Values", dir_values, "Dir Index", dir_indices)

        rw_c = AstOp.rewrite(pos_indices, dir_indices, goal_c)
        if dir_indices == 0:
            rw_dir = "id_r"
        else:
            rw_dir = "id_l"
        return "surgery {} ({}) ({}).".format(rw_dir, self._pp(goal_c), self._pp(rw_c))

    def attempt_proof_step(self):
        self.num_steps += 1

        # 1. Obtain goal
        goal_c = self.decoder.decode_exp_by_key(self.concl_idx)
        left_c, right_c = self.sep_eq_goal(goal_c)
        
        # 2. Compute and take next step
        # NOTE(deh): we assume the thing to simplify is on the left
        step = self.get_proof_step()
        print("STEP", step)
        res = self.top.sendone(step)
        self._log(res)
        if self.is_success(res):
            self.proof += [step]
        else:
            step = self.policy.next_proof_step(left_c)
            print("STEP", step)
            res = self.top.sendone(step)
            self._log(res)
            self.proof += [step]
        
        # 3. Prepare for next iteration
        self.load_tcoq_result()
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


def to_goalattn_dataset(poseval_dataset):
    def clean(orig):
        dataset = []
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
                if "theorems.id_r" in tac.ftac.gids:
                    pt.tac_bin = 0
                    pt.subtr_bin = pos
                    dataset += [(tactr_id, pt)]
                elif "theorems.id_l" in tac.ftac.gids:
                    pt.tac_bin = 1
                    pt.subtr_bin = pos
                    dataset += [(tactr_id, pt)]
        return dataset
    train = clean(poseval_dataset.train)
    test = clean(poseval_dataset.test)
    val = clean(poseval_dataset.val)
    return Dataset(train, test, val)


# LEMMA = "Lemma rewrite_eq_0: forall b, ( e <+> ( ( ( ( b ) <+> m ) <+> m ) <+> m ) ) <+> m = b."
# LEMMA = "Lemma rewrite_eq_0: forall b: G, ((b <+> m) <+> (m <+> ((e <+> (m <+> m)) <+> (e <+> ((e <+> e) <+> m))))) = b."
# LEMMA = "Lemma rewrite_eq_0: forall b: G, ((e <+> (b <+> (e <+> m))) <+> m) = b."
# LEMMA = "Lemma rewrite_eq_49: forall b: G, (b <+> (((e <+> e) <+> (e <+> e)) <+> m)) <+> (e <+> m) = b."

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

if __name__ == "__main__":
    num_theorems = 5
    sent_len = 10

    # lemma = GenAlgExpr().gen_lemma(sent_len)
    # print(lemma)
    # policy = RandAlgPolicy()
    # rewriter = PyCoqAlgProver(policy, LEMMA)
    # rewriter.attempt_proof()
    # print(rewriter.extract_proof())

    with open('theorems2.v', 'w') as f:
        f.write(PREFIX)
        gen = GenAlgExpr()
        for i in range(num_theorems):
            lemma = gen.gen_lemma(sent_len)
            print(lemma)
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
