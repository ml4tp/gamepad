from enum import IntEnum
import random

from coq.constr import *
from coq.constr_util import PreOrder


"""
[Note]

Utility classes/functions for simple-rewrite problem.
"""


# -------------------------------------------------
# Auxilliary

class IdLaw(IntEnum):
    ID_R = 0    # forall b: G, b <+> m = b
    ID_L = 1    # forall b: G, e <+> b = b


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


# -------------------------------------------------
# Problem generation

class SimpRWGen(object):
    """Generates random simple rewrite problems of a specified length.
    """

    def __init__(self):
        self.lemma_cnt = 0

    def gen_lemma(self, length):
        """
        Generates a simple rewrite problem of the specified length.
        """
        lemma_cnt = self.lemma_cnt
        self.lemma_cnt += 1

        ty = self._gen_expr_b(length)
        return "Lemma rewrite_eq_{}: forall b: G, {} = b.".format(lemma_cnt, ty)

    # -------------------------------------------------
    # Helper

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

    def _gen_expr_b(self, length):
        if length == 1:
            return "b"
        elif length > 1:
            return self._select(length, self._gen_expr_b, self._gen_expr_e, self._gen_expr_m)
        else:
            raise NameError("Cannot generate expr that reduces to b")

    def _gen_expr_e(self, length):
        if length == 1:
            return "e"
        elif length > 1:
            return self._select(length, self._gen_expr_e, self._gen_expr_e, self._gen_expr_m)
        else:
            raise NameError("Cannot generate expr that reduces to e")

    def _gen_expr_m(self, length):
        if length == 1:
            return "m"
        elif length > 1:
            return self._select(length, self._gen_expr_m, self._gen_expr_e, self._gen_expr_m)
        else:
            raise NameError("Cannot generate expr that reduces to m")


# -------------------------------------------------
# AST operations

class SimpRWRewriter(object):
    """Performs a rewrite with either left-identity or right-identity at a specified position.
    """

    def __init__(self):
        self.pos = 0            # Position to rewrite
        self.found = False      # Found the position?

    def rewrite(self, pos, rw_dir, c):
        """Rewrites at position <pos> with identity <rw_dir> in AST c.

        :param pos: int
            Position to rewrite at.
        :param rw_dir: IdLaw
            Identity law to apply.
        :param c: Exp
            Expression to rewrite.
        :return: Exp or None
            Rewritten expression or None if position to rewrite is not found.
        """
        # Reset state
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
                self.pos += 1
                self.found = True
                if rw_dir is IdLaw.ID_R:
                    # use id_r, i.e., eliminate on the right
                    return c.cs[0]
                else:
                    # use id_l, i.e., eliminate on the left
                    return c.cs[1]
            else:
                self.pos += 1
                c_p = self._rewrite(pos, rw_dir, c.c)
                c1 = self._rewrite(pos, rw_dir, c.cs[0])
                c2 = self._rewrite(pos, rw_dir, c.cs[1])
                return AppExp(c_p, [c1, c2])
        else:
            raise NameError("Shouldn't happen {}".format(c))


# -------------------------------------------------
# Simple rewrite pretty printer

class SimpRWPP(object):
    """Pretty-printer for simple-rewrite problem.
    """
    def __init__(self):
        pass

    def strip(self, name):
        # Convert Top.name into name
        loc = name.rfind('.')
        return name[loc+1:]

    def pp(self, c):
        typ = type(c)
        if typ is VarExp:
            return self.strip(str(c.x))
        elif typ is ConstExp:
            return self.strip(str(c.const))
        elif typ is AppExp:
            s_op = self.pp(c.c)
            s_left = self.pp(c.cs[0])
            s_right = self.pp(c.cs[1])
            return "({} {} {})".format(s_op, s_left, s_right)
        else:
            raise NameError("Shouldn't happen {}".format(c))


# -------------------------------------------------
# Simple rewrite solver

class SimpRWSolver(object):
    """A solver for the simple-rewrite problem.

    The solver iterates:
    1. Figuring out whether a sub-expression should reduce to an e or m
    2. Applying a left or right identity law
    """
    def __init__(self):
        # Internal state
        self.preorder = PreOrder()
        self.simprw_printer = SimpRWPP()

        # Solver state
        self.elim_m = False
        self.elim_e = False

    def next_proof_step(self, goal_c):
        """Produces a pretty-printed Coq tactic invocation of whether to apply a left or right identity rewrite.
        """
        rw_dir, rw_c = self._select_step(goal_c)
        pp_orig = self.simprw_printer.pp(goal_c)
        pp_rw = self.simprw_printer.pp(rw_c)
        return "surgery {} ({}) ({}).".format(rw_dir, pp_orig, pp_rw)

    # -------------------------------------------------
    # Helper

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
                # 1. Should reduce to a <e>.
                if isinstance(right_c, ConstExp) and right_c.const == Name("Top.m"):
                    self.elim_m = True
                    return left_c
                elif isinstance(left_c, ConstExp) and left_c.const == Name("Top.e") and right_c.is_leaf():
                    self.elim_e = True
                    return right_c
                else:
                    c1 = self._reduce("e", left_c)
                    c2 = self._reduce("m", right_c)
                    return AppExp(c.c, [c1, c2])
            elif red == "m":
                # 2. Should reduce to a <m>.
                if isinstance(left_c, ConstExp) and left_c.const == Name("Top.e"):
                    self.elim_e = True
                    return right_c
                elif isinstance(right_c, ConstExp) and right_c.const == Name("Top.m") and left_c.is_leaf():
                    self.elim_m = True
                    return left_c
                else:
                    c1 = self._reduce("e", left_c)
                    c2 = self._reduce("m", right_c)
                    return AppExp(c.c, [c1, c2])
            elif red == "em":
                # 3. Should reduce to a <e>, and if it cannot, then reduce to a <m>.
                preorder_p = [(pos, c_p) for pos, c_p in enumerate(self.preorder.traverse(right_c))]
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
                # 4. Should reduce to a <m>, and if it cannot, then reduce to a <e>.
                preorder_p = [(pos, c_p) for pos, c_p in enumerate(self.preorder.traverse(left_c))]
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
                raise NameError("Shouldn't happen {}".format(red))
        else:
            raise NameError("Shouldn't happen {}.".format(c))

    def _select_step(self, c):
        # Select a reduction
        self.elim_m = False
        self.elim_e = False
        c_p = self._reduce("e", c)

        if self.elim_e:
            return "id_l", c_p
        elif self.elim_m:
            return "id_r", c_p
        else:
            raise NameError("Shouldn't happen")
