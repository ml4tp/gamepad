from enum import Enum

from lib.myhist import MyHist


"""
[Note]

Python representation of Coq's Kernel AST

Notes:
1. Check hashes (but we aren't using them currently)
2. Currently, not using hierarchical names
"""


# -------------------------------------------------
# Helper-classes

class Name(object):
    def __init__(self, base, hierch=None):
        assert isinstance(base, str)
        assert not hierch or isinstance(hierch, Name)
        self.base = base
        self.hierch = hierch

    def __eq__(self, other):
        return isinstance(other, Name) and self.base == other.base and self.hierch == other.hierch

    def __hash__(self):
        return 3 * hash(self.base) + hash(self.hierch)

    def __str__(self):
        if self.hierch:
            return "{}.{}".format(self.base, str(self.hierch))
        else:
            return self.base


class UniverseInstance(object):
    def __init__(self, univs):
        for univ in univs:
            assert isinstance(univ, str)
        self.univs = univs

    def __eq__(self, other):
        return isinstance(other, UniverseInstance) and all([u1 == u2 for u1, u2 in zip(self.univs, other.univs)])

    def __hash__(self):
        return hash("".join(self.univs))

    def __str__(self):
        return ",".join([univ for univ in self.univs])


class Inductive(object):
    def __init__(self, mutind, pos):
        assert isinstance(mutind, Name)
        assert isinstance(pos, int)
        self.mutind = mutind      # Name of the inductive type
        self.pos = pos            # Position of the inductive type

    def __eq__(self, other):
        return isinstance(other, Inductive) and self.mutind == other.mutind and self.pos == other.pos

    def __hash__(self):
        return hash(self.mutind) + hash(self.pos)

    def __str__(self):
        return "{}.{}".format(str(self.mutind), self.pos)


class CaseInfo(object):
    def __init__(self, ind, npar, cstr_ndecls, cstr_nargs):
        assert isinstance(ind, Inductive)
        assert isinstance(npar, int)

        # Note(deh): Comment taken from Coq 8.6.1 source-code
        # inductive type to which belongs the value that is being matched
        self.ind = ind
        # number of parameters of the above inductive type
        self.npar = npar
        # For each constructor, the corresponding integer determines
        # the number of values that can be bound in a match-construct.
        # NOTE: parameters of the inductive type are therefore excluded
        # from the count
        self.cstr_ndecls = cstr_ndecls
        # for each constructor, the corresponding integers determines
        # the number of values that can be applied to the constructor,
        # in addition to the parameters of the related inductive type
        # NOTE: "lets" are therefore excluded from the count
        # NOTE: parameters of the inductive type are also excluded
        # from the count
        self.cstr_nargs = cstr_nargs

    def __eq__(self, other):
        return isinstance(other, CaseInfo) and self.ind == other.ind

    def __str__(self):
        s_cstr_ndecls = ",".join([str(x) for x in self.cstr_ndecls])
        s_cstr_nargs = ",".join([str(x) for x in self.cstr_nargs])
        x = self.ind, self.npar, s_cstr_ndecls, s_cstr_nargs
        return "{}; {}; [{}]; [{}]".format(*x)


# -------------------------------------------------
# Expressions

class Exp(object):
    def __init__(self):
        self.tag = None

    def __eq__(self, other):
        raise NotImplementedError

    def __hash__(self):
        raise NotImplementedError

    def _tag(self, c):
        c.tag = self.tag
        return c

    def apted_tree(self):
        raise NotImplementedError

    def copy(self):
        raise NotImplementedError

    def is_leaf(self):
        raise NotImplementedError


class RelExp(Exp):
    """AST for a debruin-index referenced variable.

    Low-level format:
        R %d

    Coq:
        A -> B

    Notes:
        A DeBruijn index. (Starts at 1 ...)
        fun x => x             =  fun 1
        fun x => fun => y y x  =  fun fun 1 2
    """
    def __init__(self, idx):
        assert isinstance(idx, int) and idx >= 1
        super().__init__()
        self.idx = idx

    def __eq__(self, other):
        return isinstance(other, RelExp) and self.idx == other.idx

    def __hash__(self):
        return self.idx

    def __str__(self):
        return "R({})".format(self.idx)

    def apted_tree(self):
        return "{{R{}}}".format(self.idx)

    def copy(self):
        return self._tag(RelExp(self.idx))

    def is_leaf(self):
        return True


class VarExp(Exp):
    """AST for named variable.

    Low-level format:
        V %s

    Coq:
        x
    """
    def __init__(self, x):
        assert isinstance(x, str)
        super().__init__()
        self.x = x

    def __eq__(self, other):
        return isinstance(other, VarExp) and self.x == other.x

    def __hash__(self):
        return hash(self.x)

    def __str__(self):
        return "V({})".format(self.x)

    def apted_tree(self):
        return "{{V{}}}".format(self.x)

    def copy(self):
        return self._tag(VarExp(self.x))

    def is_leaf(self):
        return True


class MetaExp(Exp):
    """AST for variable in the meta-language. Should never occur.

    Low-level format:
        M %d

    Coq:
        should not occur
    """
    def __init__(self, mv):
        assert isinstance(mv, int)
        super().__init__()
        self.mv = mv

    def __eq__(self, other):
        return isinstance(other, MetaExp) and self.mv == other.mv

    def __hash__(self):
        return self.mv

    def __str__(self):
        return "M({})".format(self.mv)

    def apted_tree(self):
        return "{{M{}}}".format(self.mv)

    def copy(self):
        return self._tag(MetaExp(self.mv))

    def is_leaf(self):
        return True


class EvarExp(Exp):
    """AST for an existential variable.

    Low-level format:
        E %d [%s]

    Coq:
        ?x1
    """
    def __init__(self, exk, cs):
        assert isinstance(exk, int)
        for c_p in cs:
            assert isinstance(c_p, Exp)
        super().__init__()
        self.exk = exk
        self.cs = cs

    def __eq__(self, other):
        return (isinstance(other, EvarExp) and self.exk == other.exk and
                all([c1 == c2 for c1, c2 in zip(self.cs, other.cs)]))

    def __hash__(self):
        return sum([hash(c) for c in self.cs])

    def __str__(self):
        return "E({}, {})".format(self.exk, ",".join([str(c) for c in self.cs]))

    def apted_tree(self):
        return "{{E{}}}".format(self.exk)

    def copy(self):
        return self._tag(EvarExp(self.exk, [c.copy() for c in self.cs]))

    def is_leaf(self):
        # TODO(deh): hmmm ...
        return False


class SortExp(Exp):
    """AST for the kind of a term, i.e., Set/Prop, or Type-0, Type-1, ...

    Low-level format:
        S %s

    Coq:
        Set
        Prop
        Type (level is not shown)
    """
    def __init__(self, sort):
        assert isinstance(sort, str)
        super().__init__()
        self.sort = sort

    def __eq__(self, other):
        return isinstance(other, SortExp) and self.sort == other.sort

    def __hash__(self):
        return hash(self.sort)

    def __str__(self):
        return "S({})".format(self.sort)

    def apted_tree(self):
        return "{{S{}}}".format(self.sort)

    def copy(self):
        return self._tag(SortExp(self.sort))

    def is_leaf(self):
        return True


class CastExp(Exp):
    """AST for casting an expression <c> to the type <ty>.

    Low-level format:
        CA %d %s %d

    Coq:
        ??
    """
    def __init__(self, c, ck, ty):
        assert isinstance(c, Exp)
        # TODO(deh): cast kind?
        assert isinstance(ty, Exp)
        super().__init__()
        self.c = c
        self.ck = ck
        self.ty = ty

    def __eq__(self, other):
        return isinstance(other, CastExp) and self.c == other.c and self.ck == other.ck and self.ty == other.ty

    def __hash__(self):
        return hash(self.c) + hash(self.ty)

    def __str__(self):
        return "CA({}, {}, {})".format(str(self.c), self.ck, str(self.ty))

    def apted_tree(self):
        return "{{CA{}{}}}".format(self.c.apted_tree(), self.ty.apted_tree())

    def copy(self):
        return self._tag(CastExp(self.c.copy(), self.ck, self.ty.copy()))

    def is_leaf(self):
        return False


class ProdExp(Exp):
    """AST for dependent product type of Pi <name>: <ty1>. <ty2>.

    Low-level format:
        P %s %d %d

    Coq:
        \forall x: c1. c2
    """
    def __init__(self, name, ty1, ty2):
        assert isinstance(name, Name)
        assert isinstance(ty1, Exp)
        assert isinstance(ty2, Exp)
        super().__init__()
        self.name = name
        self.ty1 = ty1
        self.ty2 = ty2

    def __eq__(self, other):
        return (isinstance(other, ProdExp) and self.name == other.name and
                self.ty1 == other.ty1 and self.ty2 == other.ty2)

    def __hash__(self):
        return hash(self.ty1) + hash(self.ty2)

    def __str__(self):
        return "P({}, {}, {})".format(self.name, str(self.ty1), str(self.ty2))

    def apted_tree(self):
        return "{{P{{{}}}{}{}}}".format(self.name, self.ty1.apted_tree(), self.ty2.apted_tree())

    def copy(self):
        return self._tag(ProdExp(self.name, self.ty1.copy(), self.ty2.copy()))

    def is_leaf(self):
        return False


class LambdaExp(Exp):
    """AST for Lambda expression.

    Low-level format:
        L %s %d %d

    Coq:
        fun (name : ty) => c
    """
    def __init__(self, name, ty, c):
        assert isinstance(name, Name)
        assert isinstance(ty, Exp)
        assert isinstance(c, Exp)
        super().__init__()
        self.name = name
        self.ty = ty
        self.c = c

    def __eq__(self, other):
        return (isinstance(other, LambdaExp) and self.name == other.name and
                self.ty == other.ty and self.c == other.c)

    def __hash__(self):
        return hash(self.ty) + hash(self.c)

    def __str__(self):
        return "L({}, {}, {})".format(self.name, str(self.ty), str(self.c))

    def apted_tree(self):
        return "{{L{{{}}}{}{}}}".format(self.name, self.ty.apted_tree(), self.c.apted_tree())

    def copy(self):
        return self._tag(LambdaExp(self.name, self.ty.copy(), self.c.copy()))

    def is_leaf(self):
        return False


class LetInExp(Exp):
    """AST for Let expression.

    Low-level format:
        LI %s %d %d %d

    Coq:
        let x = c1 in c2
    """
    def __init__(self, name, c1, ty, c2):
        assert isinstance(name, Name)
        assert isinstance(c1, Exp)
        assert isinstance(ty, Exp)
        assert isinstance(c2, Exp)
        super().__init__()
        self.name = name
        self.c1 = c1
        self.ty = ty
        self.c2 = c2

    def __eq__(self, other):
        return (isinstance(other, LetInExp) and self.name == other.name and
                self.c1 == other.c1 and self.ty == other.ty and self.c2 == other.c2)

    def __hash__(self):
        return hash(self.c1) + hash(self.ty) + hash(self.c2)

    def __str__(self):
        return "LI({}, {}, {}, {})".format(self.name, str(self.c1), str(self.ty), str(self.c2))

    def apted_tree(self):
        return "{{LI{{{}}}{}{}}}".format(self.name, self.c1.apted_tree(), self.ty.apted_tree(), self.c2.apted_tree())

    def copy(self):
        return self._tag(LetInExp(self.name, self.c1.copy(), self.ty.copy(), self.c2.copy()))

    def is_leaf(self):
        return False


class AppExp(Exp):
    """AST for application expression.

    Low-level format:
        A %d [%s]

    Coq:
        S (S (S O))     (equal to the number 3)
    """
    def __init__(self, c, cs):
        assert isinstance(c, Exp)
        for c_p in cs:
            assert isinstance(c_p, Exp)
        super().__init__()
        self.c = c
        self.cs = cs

    def __eq__(self, other):
        return (isinstance(other, AppExp) and self.c == other .c and
                all([c1 == c2 for c1, c2 in zip(self.cs, other.cs)]))

    def __hash__(self):
        return hash(self.c) + sum([hash(c) for c in self.cs])

    def __str__(self):
        return "A({}, {})".format(str(self.c), ",".join([str(c) for c in self.cs]))

    def apted_tree(self):
        s_cs = "".join([c.apted_tree() for c in self.cs])
        return "{{A{}{}}}".format(self.c.apted_tree(), s_cs)

    def copy(self):
        return self._tag(AppExp(self.c.copy(), [c.copy() for c in self.cs]))

    def is_leaf(self):
        return False


class ConstExp(Exp):
    """AST for constant expression with global identifier <const>.

    Low-level format:
        C %s [%s]

    Coq:
        Coq.logic.eq_refl
    """
    def __init__(self, const, ui):
        assert isinstance(const, Name)  # TODO(deh): Name.Constant?
        assert isinstance(ui, UniverseInstance)
        super().__init__()
        self.const = const
        self.ui = ui

    def __eq__(self, other):
        return isinstance(other, ConstExp) and self.const == other.const and self.ui == other.ui

    def __hash__(self):
        return hash(self.const)

    def __str__(self):
        return "C({}, {})".format(self.const, self.ui)

    def apted_tree(self):
        return "{{C{}}}".format(str(self.const))

    def copy(self):
        return self._tag(ConstExp(self.const, self.ui))

    def is_leaf(self):
        return True


class IndExp(Exp):
    """AST for an inductive type with name and position <ind>.

    Low-level format:
        I %s %d [%s]

    Coq:
        Inductive nat : Set := O | S : nat -> nat.
    """
    def __init__(self, ind, ui):
        assert isinstance(ind, Inductive)
        assert isinstance(ui, UniverseInstance)
        super().__init__()
        self.ind = ind   # Name of the inductive type
        self.ui = ui

    def __eq__(self, other):
        return isinstance(other, IndExp) and self.ind == other.ind and self.ui == other.ui

    def __hash__(self):
        return hash(self.ind)

    def __str__(self):
        return "I({}, {})".format(self.ind, self.ui)

    def apted_tree(self):
        return "{{I{}}}".format(self.ind)

    def copy(self):
        return self._tag(IndExp(self.ind, self.ui))

    def is_leaf(self):
        return True


class ConstructExp(Exp):
    """AST for constructor <conid> of an inductive type <ind>.

    Low-level format:
        CO %s %d %d [%s]

    Coq:
        Inductive nat : Set := O | S : nat -> nat.
        O or S are constructors
    """
    def __init__(self, ind, conid, ui):
        assert isinstance(conid, int)
        assert isinstance(ui, UniverseInstance)
        super().__init__()
        self.ind = ind         # Name of the inductive type
        self.conid = conid     # Constructor number (1-indexing)
        self.ui = ui

    def __eq__(self, other):
        return (isinstance(other, ConstructExp) and self.ind == other.ind and
                self.conid == other.conid and self.ui == other.ui)

    def __hash__(self):
        return hash(self.ind) + self.conid

    def __str__(self):
        return "CO({}, {}, {})".format(self.ind, self.conid, self.ui)

    def apted_tree(self):
        return "{{CO{}{}}}".format(self.ind, self.conid)

    def copy(self):
        return self._tag(ConstructExp(self.ind, self.conid, self.ui))

    def is_leaf(self):
        return True


class CaseExp(Exp):
    """AST for case expression.

    Low-level format:
        CS [%s] %d %d [%s]

    Coq:
        match c return e' with
        | pat1 => c1
        | ...
        | patn => cn
    """
    def __init__(self, ci, ret, match, cases):
        assert isinstance(ci, CaseInfo)
        assert isinstance(ret, Exp)
        assert isinstance(match, Exp)
        for c_p in cases:
            assert isinstance(c_p, Exp)
        super().__init__()
        # Note(deh): Comment taken from Coq 8.6.1 source-code
        # [mkCase ci p c ac] stands for
        # match [c] as [x] in [I args] return [p] with [ac]
        # presented as describe in [ci].
        self.ci = ci          # case info
        self.ret = ret        # dependent return
        self.match = match    # what you match on
        self.cases = cases    # cases

    def __eq__(self, other):
        return (isinstance(other, CaseExp) and self.ci == other.ci and self.ret == other.ret and
                self.match == other.match and all([c1 == c2 for c1, c2 in zip(self.cases, other.cases)]))

    def __hash__(self):
        return hash(self.ret) + hash(self.match) + sum([hash(c) for c in self.cases])

    def __str__(self):
        s_cases = ",".join([str(c) for c in self.cases])
        return "CS({}, {}, {}, {})".format(self.ci, str(self.ret), str(self.match), s_cases)

    def apted_tree(self):
        s_cases = "".join([c.apted_tree() for c in self.cases])
        return "{{CS{}{}{}}}".format(self.ret.apted_tree(), self.match.apted_tree(), s_cases)

    def copy(self):
        return self._tag(CaseExp(self.ci, self.ret.copy(), self.match.copy(), [c.copy() for c in self.cases]))

    def is_leaf(self):
        return False


class FixExp(Exp):
    """AST for a fixpoint expression.

    Low-level fomrat:
        F [%s] %d [%s] [%s] [%s]

    Coq:
        Fix even n :=
          match n with
          | O => True
          | S n => odd n
        and odd n :=
          match n with
          | O => False
          | S n => even n

        Fix [even, odd] [nat -> bool, nat -> bool] [c1, c2]
    """
    def __init__(self, iarr, idx, names, tys, cs):
        for i in iarr:
            assert isinstance(i, int)
        assert isinstance(idx, int)
        for name in names:
            assert isinstance(name, Name)
        for ty in tys:
            assert isinstance(ty, Exp)
        for c_p in cs:
            assert isinstance(c_p, Exp)

        # Note(deh): Comment taken from Coq 8.6.1 source-code
        # [recindxs = [|i1,...in|]]
        # [funnames = [|f1,.....fn|]]
        # [typarray = [|t1,...tn|]]
        # [bodies   = [|b1,.....bn|]]
        # then [mkFix ((recindxs,i), funnames, typarray, bodies) ]
        # constructs the {% $ %}i{% $ %}th function of the block
        # (counting from 0)
        # [Fixpoint f1 [ctx1] = b1
        # with     f2 [ctx2] = b2
        # ...
        # with     fn [ctxn] = bn.]
        # where the length of the {% $ %}j{% $ %}th context is
        # {% $ %}ij{% $ %}.
        super().__init__()
        self.iarr = iarr
        self.idx = idx
        self.names = names
        self.tys = tys
        self.cs = cs

    def __eq__(self, other):
        return (isinstance(other, FixExp) and self.idx == other.idx and
                all([i1 == i2 for i1, i2 in zip(self.iarr, other.iarr)]) and
                all([name1 == name2 for name1, name2 in zip(self.names, other.names)]) and
                all([ty1 == ty2 for ty1, ty2 in zip(self.tys, other.tys)]) and
                all([c1 == c2 for c1, c2 in zip(self.cs, other.cs)]))

    def __hash__(self):
        return sum([hash(c) for c in self.cs]) + sum([hash(ty) for ty in self.tys])

    def __str__(self):
        s1 = ",".join([name for name in self.names])
        s2 = ",".join([str(ty) for ty in self.tys])
        s3 = ",".join([str(c) for c in self.cs])
        return "F({}, {}, {}, {}, {})".format(self.iarr, self.idx, s1, s2, s3)

    def apted_tree(self):
        s_names = "".join(["{{{}}}".format(name) for name in self.names])
        s_tys = "".join([ty.apted_tree() for ty in self.tys])
        s_cs = "".join([c.apted_tree() for c in self.cs])
        return "{{F{}{}{}}}".format(s_names, s_tys, s_cs)

    def copy(self):
        return self._tag(FixExp(self.iarr, self.idx, self.names,
                                [ty.copy() for ty in self.tys], [c.copy() for c in self.cs]))

    def is_leaf(self):
        return False


class CoFixExp(Exp):
    """AST for cofixpoint expression.

    Low-level format:
        CF %d [%s] [%s] [%s]

    Coq:
        Same as Fix but must be productive.
    """
    def __init__(self, idx, names, tys, cs):
        assert isinstance(idx, int)
        for name in names:
            assert isinstance(name, Name)
        for ty in tys:
            assert isinstance(ty, Exp)
        for c_p in cs:
            assert isinstance(c_p, Exp)
        super().__init__()
        self.idx = idx
        self.names = names
        self.tys = tys
        self.cs = cs

    def __eq__(self, other):
        return (isinstance(other, CoFixExp) and self.idx == other.idx and
                all([name1 == name2 for name1, name2 in zip(self.names, other.names)]) and
                all([ty1 == ty2 for ty1, ty2 in zip(self.tys, other.tys)]) and
                all([c1 == c2 for c1, c2 in zip(self.cs, other.cs)]))

    def __hash__(self):
        return sum([hash(c) for c in self.cs]) + sum([hash(ty) for ty in self.tys])

    def __str__(self):
        s1 = ",".join([name for name in self.names])
        s2 = ",".join([str(ty) for ty in self.tys])
        s3 = ",".join([str(c) for c in self.cs])
        return "CF({}, {}, {}, {})".format(self.idx, s1, s2, s3)

    def apted_tree(self):
        s_names = "".join(["{{{}}}".format(name) for name in self.names])
        s_tys = "".join([ty.apted_tree() for ty in self.tys])
        s_cs = "".join([c.apted_tree() for c in self.cs])
        return "{{CF{}{}{}}}".format(s_names, s_tys, s_cs)

    def copy(self):
        return self._tag(CoFixExp(self.idx, self.names, [ty.copy() for ty in self.tys], [c.copy() for c in self.cs]))

    def is_leaf(self):
        return False


class ProjExp(Exp):
    """AST for record projection expression.

    Low-level format:
        PJ %s %d

    Coq:
        x.proj
    """
    def __init__(self, proj, c):
        assert isinstance(proj, Name)  # TODO(deh): Name.Projection?
        assert isinstance(c, Exp)
        super().__init__()
        self.proj = proj
        self.c = c

    def __eq__(self, other):
        return isinstance(other, ProjExp) and self.proj == other.proj and self.c == other.c

    def __hash__(self):
        return hash(self.proj) + hash(self.c)

    def __str__(self):
        return "PJ({}, {})".format(self.proj, str(self.c))

    def apted_tree(self):
        return "{{PJ{{{}}}{}}}".format(self.proj, self.c.apted_tree())

    def copy(self):
        return self._tag(ProjExp(self.proj, self.c.copy()))

    def is_leaf(self):
        return False


# -------------------------------------------------
# Other

class Kind(Enum):
    TERM = 0
    TYPE = 1


COQEXP = ['RelExp',
          'VarExp',
          'MetaExp',
          'EvarExp',
          'SortExp',
          'CastExp',
          'ProdExp',
          'LambdaExp',
          'LetInExp',
          'AppExp',
          'ConstExp',
          'IndExp',
          'ConstructExp',
          'CaseExp',
          'FixExp',
          'CoFixExp',
          'ProjExp']


COQEXP_HIST = MyHist(COQEXP)
