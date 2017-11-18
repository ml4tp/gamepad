"""
[Note]

Python representation of Coq ASTs
"""


# -------------------------------------------------
# Helper-classes

class UniverseInstance(object):
    def __init__(self, univs):
        for univ in univs:
            assert isinstance(univ, str)
        self.univs = univs

    def __str__(self):
        return ",".join([univ for univ in self.univs])


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
        assert isinstance(name, str)
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
        assert isinstance(name, str)
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
        assert isinstance(name, str)
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
        assert isinstance(const, str) # TODO(deh): Name.Constant?
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
    def __init__(self, mutind, i, ui):
        assert isinstance(mutind, str) # TODO(deh): Name.MutInd?
        assert isinstance(i, int)
        assert isinstance(ui, UniverseInstance)
        super().__init__()
        self.mutind = mutind
        self.i = i
        self.ui = ui

    def size(self):
        # TODO(deh): wtf?
        return 1

    def __hash__(self):
        return hash(self.mutind) + self.i

    def __str__(self):
        return "I({}, {}, {})".format(self.mutind, self.i, self.ui)


class ConstructExp(Exp):
    """CO %s %d %d [%s]"""
    def __init__(self, mutind, i, j, ui):
        assert isinstance(mutind, str) # TODO(deh): Name.MutInd?
        assert isinstance(i, int)
        assert isinstance(j, int)
        assert isinstance(ui, UniverseInstance)
        super().__init__()
        self.mutind = mutind
        self.i = i
        self.j = j
        self.ui = ui

    def size(self):
        # TODO(deh): wtf?
        return 1

    def __hash__(self):
        return hash(self.mutind) + self.i + self.j

    def __str__(self):
        return "CO({}, {}, {}, {})".format(self.mutind, self.i, self.j, self.ui)


class CaseExp(Exp):
    """CS [%s] %d %d [%s]"""
    def __init__(self, ci, c1, c2, cs):
        # TODO(deh): case info?
        assert isinstance(c1, Exp)
        assert isinstance(c2, Exp)
        for c_p in cs:
            assert isinstance(c_p, Exp)
        super().__init__()
        self.ci = ci
        self.c1 = c1
        self.c2 = c2
        self.cs = cs

    def size(self):
        return 1 + self.c1.size() + self.c2.size() + sum([c.size() for c in self.cs])

    def __hash__(self):
        return hash(self.c1) + hash(self.c2) + sum([hash(c) for c in self.cs])

    def __str__(self):
        return "CS({}, {}, {}, {})".format(self.ci, str(self.c1), str(self.c2), ",".join([str(c) for c in self.cs]))


class FixExp(Exp):
    """"F [%s] %d [%s] [%s] [%s]"""
    def __init__(self, iarr, idx, names, tys, cs):
        for i in iarr:
            assert isinstance(i, int)
        assert isinstance(idx, int)
        for name in names:
            assert isinstance(name, str)
        for ty in tys:
            assert isinstance(ty, Exp)
        for c_p in cs:
            assert isinstance(c_p, Exp)
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
            assert isinstance(name, str)
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
        # TODO(deh): Name.Projection?
        assert isinstance(proj, str)
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
