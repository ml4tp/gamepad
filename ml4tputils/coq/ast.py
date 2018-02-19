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
        return self.base == other.base and self.hierch == other.hierch

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
        return all([u1 == u2 for u1, u2 in zip(self.univs, other.univs)])

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
        return self.mutind == other.mutind and self.pos == other.pos

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

    def __hash__(self):
        raise NotImplementedError


class RelExp(Exp):
    """R %d
    A DeBruijn index. (Starts at 1 ...)
    fun x -> x        =  fun 1
    fun x -> fun -> y y x  =  fun fun 1 2
    """
    def __init__(self, idx):
        assert isinstance(idx, int) and idx >= 1
        super().__init__()
        self.idx = idx

    def __hash__(self):
        return self.idx

    def __str__(self):
        return "R({})".format(self.idx)


class VarExp(Exp):
    """V %s
    A named representation for a bound variable.
    fun x -> x
    """
    def __init__(self, x):
        assert isinstance(x, str)
        super().__init__()
        self.x = x

    def __hash__(self):
        return hash(self.x)

    def __str__(self):
        return "V({})".format(self.x)


class MetaExp(Exp):
    """M %d
    A variable in the meta-language. Should not be referenced.
    """
    def __init__(self, mv):
        assert isinstance(mv, int)
        super().__init__()
        self.mv = mv

    def __hash__(self):
        return self.mv

    def __str__(self):
        return "M({})".format(self.mv)


class EvarExp(Exp):
    """E %d [%s]
    An existential variable in the object-language. For example,
    ?1 + 2 = 4 : nat
    means that ?1 is an existential variable such that
    it plus 2 is 4 at type nat.
    """
    def __init__(self, exk, cs):
        assert isinstance(exk, int)
        for c_p in cs:
            assert isinstance(c_p, Exp)
        super().__init__()
        self.exk = exk
        self.cs = cs

    def __hash__(self):
        return sum([hash(c) for c in self.cs])

    def __str__(self):
        return "E({}, {})".format(self.exk,
                                  ",".join([str(c) for c in self.cs]))


class SortExp(Exp):
    """S %s
    The kind of a term, i.e., Set/Prop, or Type-0, Type-1, ...
    """
    def __init__(self, sort):
        assert isinstance(sort, str)
        super().__init__()
        self.sort = sort

    def __hash__(self):
        return hash(self.sort)

    def __str__(self):
        return "S({})".format(self.sort)


class CastExp(Exp):
    """CA %d %s %d
    Cast an expression <c> to the type <ty>.
    """
    def __init__(self, c, ck, ty):
        assert isinstance(c, Exp)
        # TODO(deh): cast kind?
        assert isinstance(ty, Exp)
        super().__init__()
        self.c = c
        self.ck = ck
        self.ty = ty

    def __hash__(self):
        return hash(self.c) + hash(self.ty)

    def __str__(self):
        return "CA({}, {}, {})".format(str(self.c), self.ck, str(self.ty))


class ProdExp(Exp):
    """P %s %d %d
    A dependent product type of Pi <name>: <ty1>. <ty2>.
    """
    def __init__(self, name, ty1, ty2):
        assert isinstance(name, Name)
        assert isinstance(ty1, Exp)
        assert isinstance(ty2, Exp)
        super().__init__()
        self.name = name
        self.ty1 = ty1
        self.ty2 = ty2

    def __hash__(self):
        return hash(self.ty1) + hash(self.ty2)

    def __str__(self):
        return "P({}, {}, {})".format(self.name, str(self.ty1), str(self.ty2))


class LambdaExp(Exp):
    """L %s %d %d
    \name : ty. c
    """
    def __init__(self, name, ty, c):
        assert isinstance(name, Name)
        assert isinstance(ty, Exp)
        assert isinstance(c, Exp)
        super().__init__()
        self.name = name
        self.ty = ty
        self.c = c

    def __hash__(self):
        return hash(self.ty) + hash(self.c)

    def __str__(self):
        return "L({}, {}, {})".format(self.name, str(self.ty), str(self.c))


class LetInExp(Exp):
    """LI %s %d %d %d
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

    def __hash__(self):
        return hash(self.c1) + hash(self.ty) + hash(self.c2)

    def __str__(self):
        return "LI({}, {}, {}, {})".format(self.name, str(self.c1),
                                           str(self.ty), str(self.c2))


class AppExp(Exp):
    """A %d [%s]
    c [c1 ... cn]
    """
    def __init__(self, c, cs):
        assert isinstance(c, Exp)
        for c_p in cs:
            assert isinstance(c_p, Exp)
        super().__init__()
        self.c = c
        self.cs = cs

    def __hash__(self):
        return hash(self.c) + sum([hash(c) for c in self.cs])

    def __str__(self):
        return "A({}, {})".format(str(self.c),
                                  ",".join([str(c) for c in self.cs]))


class ConstExp(Exp):
    """C %s [%s]
    A constant expression with global identifier <const>.
    """
    def __init__(self, const, ui):
        assert isinstance(const, Name)  # TODO(deh): Name.Constant?
        assert isinstance(ui, UniverseInstance)
        super().__init__()
        self.const = const
        self.ui = ui

    def __hash__(self):
        return hash(self.const)

    def __str__(self):
        return "C({}, {})".format(self.const, self.ui)


class IndExp(Exp):
    """I %s %d [%s]
    An inductive type with name and position <ind>.
    """
    def __init__(self, ind, ui):
        assert isinstance(ind, Inductive)
        assert isinstance(ui, UniverseInstance)
        super().__init__()
        self.ind = ind   # Name of the inductive type
        self.ui = ui

    def __hash__(self):
        return hash(self.ind)

    def __str__(self):
        return "I({}, {})".format(self.ind, self.ui)


class ConstructExp(Exp):
    """CO %s %d %d [%s]
    A constructor <conid> of an inductive type <ind>.
    """
    def __init__(self, ind, conid, ui):
        assert isinstance(conid, int)
        assert isinstance(ui, UniverseInstance)
        super().__init__()
        self.ind = ind         # Name of the inductive type
        self.conid = conid     # Constructor number (1-indexing)
        self.ui = ui

    def __hash__(self):
        return hash(self.ind) + self.conid

    def __str__(self):
        return "CO({}, {}, {})".format(self.ind, self.conid, self.ui)


class CaseExp(Exp):
    """CS [%s] %d %d [%s]
    case <match> return <ret> of
      <c1>
      ...
      <cn>
    """
    def __init__(self, ci, ret, match, cases):
        # TODO(deh): case info?
        assert isinstance(ci, CaseInfo)
        assert isinstance(ret, Exp)
        assert isinstance(match, Exp)
        for c_p in cases:
            assert isinstance(c_p, Exp)
        super().__init__()
        # NOTE(deh): Comment taken from Coq 8.6.1 source-code
        # [mkCase ci p c ac] stands for
        # match [c] as [x] in [I args] return [p] with [ac]
        # presented as describe in [ci].
        self.ci = ci          # case info
        self.ret = ret        # dependent return
        self.match = match    # what you match on
        self.cases = cases    # cases

    def __hash__(self):
        return (hash(self.ret) + hash(self.match) +
                sum([hash(c) for c in self.cases]))

    def __str__(self):
        s_cases = ",".join([str(c) for c in self.cases])
        return "CS({}, {}, {}, {})".format(self.ci, str(self.ret),
                                           str(self.match), s_cases)


class FixExp(Exp):
    """F [%s] %d [%s] [%s] [%s]
    For example,
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

    def __hash__(self):
        return (sum([hash(c) for c in self.cs]) +
                sum([hash(ty) for ty in self.tys]))

    def __str__(self):
        s1 = ",".join([name for name in self.names])
        s2 = ",".join([str(ty) for ty in self.tys])
        s3 = ",".join([str(c) for c in self.cs])
        return "F({}, {}, {}, {}, {})".format(self.iarr, self.idx, s1, s2, s3)


class CoFixExp(Exp):
    """CF %d [%s] [%s] [%s]
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

    def __hash__(self):
        return (sum([hash(c) for c in self.cs]) +
                sum([hash(ty) for ty in self.tys]))

    def __str__(self):
        s1 = ",".join([name for name in self.names])
        s2 = ",".join([str(ty) for ty in self.tys])
        s3 = ",".join([str(c) for c in self.cs])
        return "CF({}, {}, {}, {})".format(self.idx, s1, s2, s3)


class ProjExp(Exp):
    """PJ %s %d
    Projection from a record.
    """
    def __init__(self, proj, c):
        assert isinstance(proj, Name)  # TODO(deh): Name.Projection?
        assert isinstance(c, Exp)
        super().__init__()
        self.proj = proj
        self.c = c

    def __hash__(self):
        return hash(self.proj) + hash(self.c)

    def __str__(self):
        return "PJ({}, {})".format(self.proj, str(self.c))


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


# -------------------------------------------------
# Junk

"""
class DecodeName(object):
    def __init__(self):
        self.names = {}

    def _hcons(self, tok):
        if tok in self.names:

    def str_to_name(self, s):
        toks = s.split('.')
        if len(toks) == 0:
            raise NameError("Cannot convert empty string {}".format(s))
        elif len(toks) == 1:
            return Name(toks[0])
        else:
            name = Name(toks[-1])
            toks = toks[:-1]
            for tok in toks[::-1]:
                name = Name(tok, name)
        return name
"""