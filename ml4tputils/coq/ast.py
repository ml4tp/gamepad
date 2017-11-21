"""
[Note]

Python representation of Coq ASTs

TODO(deh): check hashes
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
        return hash(str(self))

    def __str__(self):
        if self.hierch:
            return "{}.{}".format(self.base, self.hierch)
        else:
            return self.base


class UniverseInstance(object):
    def __init__(self, univs):
        for univ in univs:
            assert isinstance(univ, str)
        self.univs = univs

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

        self.ind = ind
        self.npar = npar
        self.cstr_ndecls = cstr_ndecls
        self.cstr_nargs = cstr_nargs

    def __str__(self):
        s_cstr_ndecls = ",".join([str(x) for x in self.cstr_ndecls])
        s_cstr_nargs = ",".join([str(x) for x in self.cstr_nargs])
        return "{}; {}; {}; [{}]; [{}]".format(self.mutind, self.pos,
               self.npar, s_cstr_ndecls, s_cstr_nargs)
"""
case_info =
  { ci_ind        : inductive;      (* inductive type to which belongs the value that is being matched *)
    ci_npar       : int;            (* number of parameters of the above inductive type *)
    ci_cstr_ndecls : int array;     (* For each constructor, the corresponding integer determines
                                       the number of values that can be bound in a match-construct.
                                       NOTE: parameters of the inductive type are therefore excluded from the count *)
    ci_cstr_nargs : int array;      (* for each constructor, the corresponding integers determines
                                       the number of values that can be applied to the constructor,
                                       in addition to the parameters of the related inductive type
                                       NOTE: "lets" are therefore excluded from the count
                                       NOTE: parameters of the inductive type are also excluded from the count *)
    ci_pp_info    : case_printing   (* not interpreted by the kernel *)
  }
"""


# -------------------------------------------------
# Expressions

class Exp(object):
    def __init__(self):
        self.tag = None

    def size(self):
        raise NotImplementedError

    def __hash__(self):
        raise NotImplementedError


class RelExp(Exp):
    """R %d"""
    def __init__(self, idx):
        assert isinstance(idx, int)
        super().__init__()
        self.idx = idx

    def size(self):
        return 1

    def __hash__(self):
        return self.idx

    def __str__(self):
        return "R({})".format(self.idx)


class VarExp(Exp):
    """V %s"""
    def __init__(self, x):
        assert isinstance(x, str)
        super().__init__()
        self.x = x

    def size(self):
        return 1

    def __hash__(self):
        return hash(self.x)

    def __str__(self):
        return "V({})".format(self.x)


class MetaExp(Exp):
    """M %d"""
    def __init__(self, mv):
        assert False
        assert isinstance(mv, int)
        super().__init__()
        self.mv = mv

    def size(self):
        # NOTE(deh): wtf?
        return 1

    def __hash__(self):
        return self.mv

    def __str__(self):
        return "M({})".format(self.mv)


class EvarExp(Exp):
    """E %d [%s]"""
    def __init__(self, exk, cs):
        assert isinstance(exk, int)
        for c_p in cs:
            assert isinstance(c_p, Exp)
        super().__init__()
        self.exk = exk
        self.cs = cs

    def size(self):
        # NOTE(deh): wtf?
        return 1 + sum([c.size() for c in self.cs])

    def __hash__(self):
        return sum([hash(c) for c in self.cs])

    def __str__(self):
        return "E({}, {})".format(self.exk, ",".join([str(c) for c in self.cs]))


class SortExp(Exp):
    """S %s"""
    def __init__(self, sort):
        # TODO(deh): what is it's type?
        super().__init__()
        self.sort = sort

    def size(self):
        return 1

    def __hash__(self):
        return hash(self.sort)

    def __str__(self):
        return "S({})".format(self.sort)


class CastExp(Exp):
    """CA %d %s %d"""
    def __init__(self, c, ck, ty):
        assert isinstance(c, Exp)
        # TODO(deh): cast kind?
        assert isinstance(ty, Exp)
        super().__init__()
        self.c = c
        self.ck = ck
        self.ty = ty

    def size(self):
        return 1 + self.c.size() + self.ty.size()

    def __hash__(self):
        return hash(self.c) + sum([hash(c) for c in self.cs])

    def __str__(self):
        return "CA({}, {}, {})".format(str(self.c), self.ck, str(self.ty))


class ProdExp(Exp):
    """P %s %d %d"""
    def __init__(self, name, ty1, ty2):
        assert isinstance(name, Name)
        assert isinstance(ty1, Exp)
        assert isinstance(ty2, Exp)
        super().__init__()
        self.name = name
        self.ty1 = ty1
        self.ty2 = ty2

    def size(self):
        return 1 + self.ty1.size() + self.ty2.size()

    def __hash__(self):
        return hash(self.ty1) + hash(self.ty2)

    def __str__(self):
        return "P({}, {}, {})".format(self.name, str(self.ty1), str(self.ty2))


class LambdaExp(Exp):
    """L %s %d %d"""
    def __init__(self, name, ty, c):
        assert isinstance(name, Name)
        assert isinstance(ty, Exp)
        assert isinstance(c, Exp)
        super().__init__()
        self.name = name
        self.ty = ty
        self.c = c

    def size(self):
        return 1 + self.ty.size() + self.c.size()

    def __hash__(self):
        return hash(self.ty) + hash(self.c)

    def __str__(self):
        return "L({}, {}, {})".format(self.name, str(self.ty), str(self.c))


class LetInExp(Exp):
    """LI %s %d %d %d"""
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

    def size(self):
        return 1 + self.c1.size() + self.ty.size() + self.c2.size()

    def __hash__(self):
        return hash(self.c1) + hash(self.ty) + hash(self.c2)

    def __str__(self):
        return "LI({}, {}, {}, {})".format(self.name, str(self.c1), str(self.ty), str(self.c2))


class AppExp(Exp):
    """A %d [%s]"""
    def __init__(self, c, cs):
        assert isinstance(c, Exp)
        for c_p in cs:
            assert isinstance(c_p, Exp)
        super().__init__()
        self.c = c
        self.cs = cs

    def size(self):
        return 1 + self.c.size() + sum([c.size() for c in self.cs])

    def __hash__(self):
        return hash(self.c) + sum([hash(c) for c in self.cs])

    def __str__(self):
        return "A({}, {})".format(str(self.c), ",".join([str(c) for c in self.cs]))


class ConstExp(Exp):
    """C %s [%s]"""
    def __init__(self, const, ui):
        assert isinstance(const, Name) # TODO(deh): Name.Constant?
        assert isinstance(ui, UniverseInstance)
        super().__init__()
        self.const = const
        self.ui = ui

    def size(self):
        return 1

    def __hash__(self):
        return hash(self.const)

    def __str__(self):
        return "C({}, {})".format(self.const, self.ui)


class IndExp(Exp):
    """I %s %d [%s]"""
    def __init__(self, ind, ui):
        assert isinstance(ind, Inductive)
        assert isinstance(ui, UniverseInstance)
        super().__init__()
        self.ind = ind   # Name of the inductive type
        self.ui = ui

    def size(self):
        # TODO(deh): wtf?
        return 1

    def __hash__(self):
        return hash(self.mutind) + self.pos

    def __str__(self):
        return "I({}, {}, {})".format(self.mutind, self.pos, self.ui)


class ConstructExp(Exp):
    """CO %s %d %d [%s]"""
    def __init__(self, ind, conid, ui):
        assert isinstance(conid, int)
        assert isinstance(ui, UniverseInstance)
        super().__init__()
        self.ind = ind         # Name of the inductive type
        self.conid = conid     # Constructor number (1-indexing)
        self.ui = ui

    def size(self):
        # TODO(deh): wtf?
        return 1

    def __hash__(self):
        return hash(self.mutind) + self.pos + self.conid

    def __str__(self):
        return "CO({}, {}, {}, {})".format(self.mutind, self.pos,
                                           self.conid, self.ui)


class CaseExp(Exp):
    """CS [%s] %d %d [%s]"""
    def __init__(self, ci, ret, match, cases):
        # TODO(deh): case info?
        assert isinstance(ci, CaseInfo)
        assert isinstance(ret, Exp)
        assert isinstance(match, Exp)
        for c_p in cases:
            assert isinstance(c_p, Exp)
        super().__init__()
        # [mkCase ci p c ac] stands for
        # match [c] as [x] in [I args] return [p] with [ac] 
        # presented as describe in [ci].
        self.ci = ci          # case info
        self.ret = ret        # dependent return
        self.match = match    # what you match on
        self.cases = cases    # cases

    def size(self):
        return 1 + self.ret.size() + self.match.size() + sum([c.size() for c in self.cases])

    def __hash__(self):
        return hash(self.ret) + hash(self.match) + sum([hash(c) for c in self.cases])

    def __str__(self):
        return "CS({}, {}, {}, {})".format(self.ci, str(self.ret), str(self.match), ",".join([str(c) for c in self.cases]))


class FixExp(Exp):
    """"F [%s] %d [%s] [%s] [%s]"""
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

        # [recindxs = [|i1,...in|]]
        # [funnames = [|f1,.....fn|]]
        # [typarray = [|t1,...tn|]]
        # [bodies   = [|b1,.....bn|]]
        # then [mkFix ((recindxs,i), funnames, typarray, bodies) ]
        # constructs the {% $ %}i{% $ %}th function of the block (counting from 0)
        # [Fixpoint f1 [ctx1] = b1
        # with     f2 [ctx2] = b2
        # ...
        # with     fn [ctxn] = bn.]
        # where the length of the {% $ %}j{% $ %}th context is {% $ %}ij{% $ %}.
        super().__init__()
        self.iarr = iarr
        self.idx = idx
        self.names = names
        self.tys = tys
        self.cs = cs

    def size(self):
        return 1 + sum([ty.size() for ty in self.tys]) + sum([c.size() for c in self.cs])

    def __hash__(self):
        return sum([hash(c) for c in self.cs]) + sum([hash(ty) for ty in self.tys])

    def __str__(self):
        s1 = ",".join([name for name in self.names])
        s2 = ",".join([str(ty) for ty in self.tys])
        s3 = ",".join([str(c) for c in self.cs])
        return "F({}, {}, {}, {}, {})".format(self.iarr, self.idx, s1, s2, s3)


class CoFixExp(Exp):
    """CF %d [%s] [%s] [%s]"""
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

    def size(self):
        return 1 + sum([ty.size() for ty in self.tys]) + sum([c.size() for c in self.cs])

    def __hash__(self):
        return sum([hash(c) for c in self.cs]) + sum([hash(ty) for ty in self.tys])

    def __str__(self):
        s1 = ",".join([name for name in self.names])
        s2 = ",".join([str(ty) for ty in self.tys])
        s3 = ",".join([str(c) for c in self.cs])
        return "CF({}, {}, {}, {})".format(self.idx, s1, s2, s3)


class ProjExp(Exp):
    """PJ %s %d"""
    def __init__(self, proj, c):
        assert isinstance(proj, Name) # TODO(deh): Name.Projection?
        assert isinstance(c, Exp)
        super().__init__()
        self.proj = proj
        self.c = c

    def size(self):
        return 1 + self.c.size()

    def __hash__(self):
        return hash(self.proj) + hash(self.c)

    def __str__(self):
        return "PJ({}, {})".format(self.proj, str(self.c))
