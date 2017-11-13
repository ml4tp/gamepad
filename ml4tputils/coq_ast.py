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


# -------------------------------------------------
# Expressions

class Exp(object):
    pass


class RelExp(Exp):
    """R %d"""
    def __init__(self, idx):
        assert isinstance(idx, int)
        self.idx = idx


class VarExp(Exp):
    """V %s"""
    def __init__(self, x):
        assert isinstance(x, str)
        self.x = x


class MetaExp(Exp):
    """M %d"""
    def __init__(self, mv):
        assert isinstance(mv, int)
        self.mv = mv


class EvarExp(Exp):
    """E %d [%s]"""
    def __init__(self, exk, cs):
        assert isinstance(exk, int)
        for c in cs:
            assert isinstance(c, Exp)
        self.exk = exk
        self.cs = cs


class SortExp(Exp):
    """S %s"""
    def __init__(self, sort):
        # TODO(deh): what is it's type?
        self.sort = sort


class CastExp(Exp):
    """CA %d %s %d"""
    def __init__(self, c, ck, ty):
        assert isinstance(c, Exp)
        # TODO(deh): cast kind?
        assert isinstance(ty, Exp)
        self.c = c
        self.ck = ck
        self.ty = ty


class ProdExp(Exp):
    """P %s %d %d"""
    def __init__(self, name, ty1, ty2):
        assert isinstance(name, str)
        assert isinstance(ty1, Exp)
        assert isinstance(ty2, Exp)
        self.name = name
        self.ty1 = ty1
        self.ty2 = ty2


class LambdaExp(Exp):
    """L %s %d %d"""
    def __init__(self, name, ty, c):
        assert isinstance(name, str)
        assert isinstance(ty, Exp)
        assert isinstance(c, Exp)
        self.name = name
        self.ty = ty
        self.c = c


class LetInExp(Exp):
    """LI %s %d %d %d"""
    def __init__(self, name, c1, ty, c2):
        assert isinstance(name, str)
        assert isinstance(c1, Exp)
        assert isinstance(ty, Exp)
        assert isinstance(c2, Exp)
        self.name = name
        self.c1 = c1
        self.ty = ty
        self.c2 = c2


class AppExp(Exp):
    """A %d [%s]"""
    def __init__(self, c, cs):
        assert isinstance(c, Exp)
        for c in cs:
            assert isinstance(c, Exp)
        self.c = c
        self.cs = cs


class ConstExp(Exp):
    """C %s [%s]"""
    def __init__(self, const, ui):
        assert isinstance(const, str) # TODO(deh): Name.Constant?
        assert isinstance(ui, UniverseInstance)
        self.const = const
        self.ui = ui


class IndExp(Exp):
    """I %s %d [%s]"""
    def __init__(self, mutind, i, ui):
        assert isinstance(mutind, str) # TODO(deh): Name.MutInd?
        assert isinstance(i, int)
        assert isinstance(ui, UniverseInstance)
        self.mutind = mutind
        self.i = i
        self.ui = ui


class ConstructExp(Exp):
    """CO %s %d %d [%s]"""
    def __init__(self, mutind, i, j, ui):
        assert isinstance(mutind, str) # TODO(deh): Name.MutInd?
        assert isinstance(i, int)
        assert isinstance(j, int)
        assert isinstance(ui, UniverseInstance)
        self.mutind = mutind
        self.i = i
        self.j = j
        self.ui = ui

class CaseExp(Exp):
    """CS [%s] %d %d [%s]"""
    def __init__(self, ci, c1, c2, cs):
        # TODO(deh): case info?
        assert isinstance(c1, Exp)
        assert isinstance(c2, Exp)
        for c in cs:
            assert isinstance(c, Exp)
        self.ci = ci
        self.c1 = c1
        self.c2 = c2
        self.cs = cs


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
        for c in cs:
            assert isinstance(c, Exp)
        self.iarr = iarr
        self.idx = idx
        self.names = names
        self.tys = tys
        self.cs = cs


class CoFixExp(Exp):
    """"CF %d [%s] [%s] [%s]"""
    def __init__(self, idx, names, tys, cs):
        assert isinstance(idx, int)
        for name in names:
            assert isinstance(name, str)
        for ty in tys:
            assert isinstance(ty, Exp)
        for c in cs:
            assert isinstance(c, Exp)
        self.idx = idx
        self.names = names
        self.tys = tys
        self.cs = cs


class ProjExp(Exp):
    """"PJ %s %d"""
    def __init__(self, proj, c):
        # TODO(deh): Name.Projection?
        assert isinstance(proj, str)
        assert isinstance(c, Exp)
        self.proj = proj
        self.c = c


# -------------------------------------------------
# Reconstructing low-level expressions

class CoqExpRecon(object):
    def __init__(self, constrs_table):
        self.constrs_table = constrs_table
        self.worklist = []
        self.table = {}

    def recon_ast(self, key):
        if key in self.table:
            return self.table[key]

        entry = self.constrs_table[key]
        toks = entry.split()
        kind = toks[0].strip()
        if kind == "R":
            """R %d"""
            idx = int(toks[1].strip())

            c = RelExp(idx)
            self.table[key] = c
            return c
        elif kind == "V":
            """V %s"""
            x = toks[1].strip()

            c = VarExp(x)
            self.table[key] = c
            return c
        elif kind == "M":
            """M %d"""
            idx = int(toks[1].strip())

            c = MetaExp(idx)
            self.table[key] = c
            return c
        elif kind == "E":
            """E %d [%s]"""
            exk = int(toks[1].strip())
            cs_idxs = toks[2].strip()
            
            cs = self.recon_asts(cs_idxs)
            c = EvarExp(exk, cs)
            self.table[key] = c
            return c
        elif kind == "S":
            """S %s"""
            sort = toks[1].strip()

            c = SortExp(sort)
            self.table[key] = c
            return c
        elif kind == "CA":
            """CA %d %s %d"""
            c_idx = int(toks[1].strip())
            ck = toks[2].strip()
            ty_idx = int(toks[3].strip())

            c = self.recon_ast(c_idx)
            ty = self.recon_ast(ty_idx)
            c_p = CastExp(c, ck, ty)
            self.table[key] = c_p
            return c_p
        elif kind == "P":
            """P %s %d %d"""
            name = toks[1].strip()
            ty1_idx = int(toks[2].strip())
            ty2_idx = int(toks[3].strip())
            
            ty1 = self.recon_ast(ty1_idx)
            ty2 = self.recon_ast(ty2_idx)
            c = ProdExp(name, ty1, ty2)
            self.table[key] = c
            return c
        elif kind == "L":
            """L %s %d %d"""
            name = toks[1].strip()
            ty_idx = int(toks[2].strip())
            c_idx = int(toks[3].strip())

            ty = self.recon_ast(ty_idx)
            c = self.recon_ast(c_idx)
            c_p = LambdaExp(name, ty, c)
            self.table[key] = c_p
            return c_p
        elif kind == "LI":
            """LI %s %d %d %d"""
            name = toks[1].strip()
            c1_idx = int(toks[2].strip())
            ty_idx = int(toks[3].strip())
            c2_idx = int(toks[4].strip())

            c1 = self.recon_ast(c1_idx)
            ty = self.recon_ast(ty_idx)
            c2 = self.recon_ast(c2_idx)
            c_p = LambdaExp(name, c1, ty, c2)
            self.table[key] = c_p
            return c_p
        elif kind == "A":
            """A %d [%s]"""
            c_idx = int(toks[1].strip())
            cs_idxs = toks[2].strip()

            c = self.recon_ast(c_idx)
            cs = self.recon_asts(cs_idxs)
            c_p = AppExp(c, cs)
            self.table[key] = c_p
            return c_p
        elif kind == "C":
            """C %s [%s]"""
            const = toks[1].strip()
            ui = toks[2].strip()
            
            ui_p = self.recon_universe_instance(ui)
            c_p = ConstExp(const, ui_p)
            self.table[key] = c_p
            return c_p
        elif kind == "I":
            """I %s %d [%s]"""
            mutind = toks[1].strip()
            i = int(toks[2].strip())
            ui = toks[3].strip()

            ui_p = self.recon_universe_instance(ui)
            c_p = IndExp(mutind, i, ui)
            self.table[key] = c_p
            return c_p
        elif kind == "CO":
            """CO %s %d %d [%s]"""
            mutind = toks[1].strip()
            i = int(toks[2].strip())
            j = int(toks[3].strip())
            ui = toks[4].strip()

            ui_p = self.recon_universe_instance(ui)
            c_p = ConstructExp(mutind, i, j, ui)
            self.table[key] = c_p
            return c_p
        elif kind == "CS":
            """CS [%s] %d %d [%s]"""
            case_info = toks[1].strip()
            c1_idx = toks[2].strip()
            c2_idx = toks[3].strip()
            cs_idxs = toks[4].strip()

            c1 = self.recon_ast(c1_idx)
            c2 = self.recon_ast(c2_idx)
            cs = self.recon_asts(cs_idxs)
            c_p = CaseExp(case_info, c1, c2, c2)
            self.table[key] = c_p
            return c_p
        elif kind == "F":
            """"F [%s] %d [%s] [%s] [%s]"""
            _iarr = toks[1].strip()
            _idx = int(toks[2].strip())
            names = toks[3].strip()
            ty_idxs = toks[4].strip()
            cs_idxs = toks[5].strip()
            
            iarr = self.recon_iarr(_iarr)
            names = self.recon_names(_names)
            tys = self.recon_asts(ty_idxs)
            cs = self.recon_asts(cs_idxs)
            c_p = FixExp(iarr, idx, names, tys, cs)
            self.table[key] = c_p
            return c_p
        elif kind == "CF":
            idx = int(toks[2].strip())
            _names = toks[3].strip()
            ty_idxs = toks[4].strip()
            cs_idxs = toks[5].strip()

            names = self.recon_names(_names)
            tys = self.recon_asts(ty_idxs)
            cs = self.recon_asts(cs_idxs)
            c_p = CoFixExp(idx, names, tys, cs)
            self.table[key] = c_p
            return c_p
        elif kind == "PJ":
            proj = toks[1].strip()
            c_idx = toks[2].strip()

            c = self.recon_ast(c_idx)
            c_p = Proj(proj, c)
            self.table[key] = c_p
            return c_p
        else:
            raise NameError("Kind {} not supported.".format(kind))

    def recon_asts(self, c_idxs):
        c_idxs = c_idxs[1:-1]
        keys = [idx.strip() for idx in c_idxs.split()]
        return [self.recon_ast(key) for key in keys]

    def recon_universe_instance(self, ui):
        ui = ui[1:-1]
        return [u.strip() for u in ui.split()]

    def recon_names(self, names):
        names = names[1:-1]
        return [name.strip() for name in names.split()]

    def recon_iarr(self, iarr):
        iarr = iarr[1:-1]
        return [int(i.strip()) for i in iarr.split()]
