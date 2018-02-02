import pickle
import random

import torch

from coq.ast import *
from lib.myfile import MyFile
from pycoqtop.coqtop import CoqTop
from recon.parse_raw import TacStParser, FullTac


"""
[Note]

Don't forget to set environment variable of where to load the
intermediate results.

    export TCOQ_DUMP=/tmp/tcoq.log

1. Use algorithm in gen_rewrite to create a bunch of proofs
[x] 2. Use PyCoqTop + algorithm in python to solve proof with surgery
[x] 3. Modify formatter to just look at surgery
[x] 4. Need functions that 
   - numbers nodes in an AST
   - takes position in an AST and gets left/right children
   - implement surgery
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
            raise NameError("Shouldn't happen {}".format(c))

    def _traverses(self, cs):
        for c in cs:
            self._traverse(c)

    # def traverse_nonleaf(self, c):
    #     self.acc = []
    #     self._traverse_nonleaf(c)
    #     return self.acc

    # def _traverse_nonleaf(self, c):
    #     typ = type(c)
    #     if typ is VarExp:
    #         pass
    #     elif typ is ConstExp:
    #         pass
    #     elif typ is AppExp:
    #         self.acc += [c]
    #         # self._traverse_nonleaf(c.c)
    #         self._traverse_nonleafs(c.cs)
    #     else:
    #         raise NameError("Shouldn't happen {}".format(c))

    # def _traverse_nonleafs(self, cs):
    #     for c in cs:
    #         self._traverse_nonleaf(c)


class AstOp(object):
    def __init__(self):
        pass
    
    def _tag(self, c_orig, c_new):
        c_new.tag = c_orig.tag
        return c_new

    def copy(self, c):
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

    def staple(self, c_skel, c_loc, c_subst):
        if c_skel.tag == c_loc.tag:
            return c_subst

        typ = type(c_skel)
        if typ is VarExp:
            return c_skel
        elif typ is ConstExp:
            return c_skel
        elif typ is AppExp:
            c_p = self.staple(c_skel.c, c_loc, c_subst)
            cs_p = self.staples(c_skel.cs, c_loc, c_subst)
            return self._tag(c_skel, AppExp(c_p, cs_p))
        else:
            raise NameError("Shouldn't happen {}".format(c))

    def staples(self, cs, c_loc, c_subst):
        return [self.staple(c, c_loc, c_subst) for c in cs]


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

    def _select(self, c):
        c = AstOp().copy(c)
        inorder = [(pos, c_p) for pos, c_p in enumerate(InOrder().traverse(c))]
        nonleaves = [(pos, c_p) for pos, c_p in inorder if not is_leaf(c_p)]
        pos_b = self._locate_b(c, inorder)

        cnt = 0
        while cnt < 20:
            cnt += 1
            # 1. Pick a random place in the AST
            pos_rw, c_rw = random.choice(nonleaves)
            left_c = c_rw.cs[0]
            right_c = c_rw.cs[1]

            # 2. Check to see if we are on the left or right side of b
            #    b <+> (e <+> m) -> b <+> e   (stuck)
            #    b <+> (e <+> m) -> b <+> m   (success)
            if pos_rw < pos_b:
                # 3. On left, check to see if we can rewrite left or right
                print("LEFT", pos_rw, pos_b, "ORIG", self._pp(c), "left", self._pp(left_c), "right", self._pp(right_c))
                if isinstance(right_c, ConstExp) and right_c.const == Name("Top.m"):
                    return "id_r", AstOp().staple(c, c_rw, c_rw.cs[0])
                elif isinstance(left_c, ConstExp) and left_c.const == Name("Top.e"):
                    return "id_l", AstOp().staple(c, c_rw, c_rw.cs[1])
            elif pos_rw > pos_b:
                print("RIGHT", pos_rw, pos_b, "ORIG", self._pp(c), "left", self._pp(left_c), "right", self._pp(right_c))
                # 3. On right, check to see if we can rewrite left or right
                if isinstance(left_c, ConstExp) and left_c.const == Name("Top.e"):
                    return "id_l", AstOp().staple(c, c_rw, c_rw.cs[1])
                elif isinstance(right_c, ConstExp) and right_c.const == Name("Top.m"):
                    return "id_r", AstOp().staple(c, c_rw, c_rw.cs[0])
            else:
                # 3. At root, check to see if we can rewrite left or right
                if isinstance(left_c, ConstExp) and left_c.const == Name("Top.e"):
                    return "id_l", AstOp().staple(c, c_rw, c_rw.cs[1])
                elif isinstance(right_c, ConstExp) and right_c.const == Name("Top.m"):
                    return "id_r", AstOp().staple(c, c_rw, c_rw.cs[0])

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


class PyCoqAlgProver(object):
    """A random policy that
    1. Picks a random place in the AST
    2. Attempts a left or right rewrite
    """
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



# LEMMA = "Lemma rewrite_eq_0: forall b, ( e <+> ( ( ( ( b ) <+> m ) <+> m ) <+> m ) ) <+> m = b."
# LEMMA = "Lemma rewrite_eq_0: forall b: G, ((b <+> m) <+> (m <+> ((e <+> (m <+> m)) <+> (e <+> ((e <+> e) <+> m))))) = b."
LEMMA = "Lemma rewrite_eq_0: forall b: G, ((e <+> (b <+> (e <+> m))) <+> m) = b."

"""
1. [Y] Generate a bunch of lemmas
2. [Y] Run it through current surgery
3. [Y] Dump it into file and run coqc
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
    num_theorems = 1
    sent_len = 10

    lemma = GenAlgExpr().gen_lemma(sent_len)
    print(lemma)
    policy = RandAlgPolicy()
    rewriter = PyCoqAlgProver(policy, lemma)
    rewriter.attempt_proof()
    print(rewriter.extract_proof())
    # with open('theorems.v', 'w') as f:
    #     lemma = GenAlgExpr().gen_lemma(10)
    #     for i in range(num_theorems):
    #         policy = RandAlgPolicy()
    #         print(lemma)
    #         rewriter = PyCoqAlgProver(policy, lemma)
    #         rewriter.attempt_proof()
    #         print(rewriter.extract_proof())
    #         f.write(rewriter.extract_proof())
    #         f.write('\n')
