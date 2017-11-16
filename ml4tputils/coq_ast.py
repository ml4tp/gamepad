import networkx as nx
import matplotlib.pyplot as plt
import re

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
        for c in cs:
            assert isinstance(c, Exp)
        super().__init__()
        self.exk = exk
        self.cs = cs

    def size(self):
        # NOTE(deh): wtf?
        return 1 + sum([c.size() for c in self.cs])

    def __hash__(self):
        return sum([hash(c) for c in self.cs])

    def __str__(self):
        return "E({}, {})".format(self.exk, self.cs)


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
        return "CA({}, {}, {})".format(self.c, self.ck, self.ty)


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
        return "P({}, {}, {})".format(self.name, self.ty1, self.ty2)


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
        return "L({}, {}, {})".format(self.name, self.ty, self.c)


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
        return "LI({}, {}, {}, {})".format(self.name, self.c1, self.ty, self.c2)


class AppExp(Exp):
    """A %d [%s]"""
    def __init__(self, c, cs):
        assert isinstance(c, Exp)
        for c in cs:
            assert isinstance(c, Exp)
        super().__init__()
        self.c = c
        self.cs = cs

    def size(self):
        return 1 + self.c.size() + sum([c.size() for c in self.cs])

    def __hash__(self):
        return hash(self.c) + sum([hash(c) for c in self.cs])

    def __str__(self):
        return "A({}, {})".format(self.c, self.cs)


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
        return hash(self.mutind) + i

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
        return hash(self.mutind) + i + j

    def __str__(self):
        return "CO({}, {}, {}, {})".format(self.mutind, self.i, self.j, self.ui)


class CaseExp(Exp):
    """CS [%s] %d %d [%s]"""
    def __init__(self, ci, c1, c2, cs):
        # TODO(deh): case info?
        assert isinstance(c1, Exp)
        assert isinstance(c2, Exp)
        for c in cs:
            assert isinstance(c, Exp)
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
        return "CS({}, {}, {}, {})".format(self.ci, self.c1, self.c2, self.cs)


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
        return "F({}, {}, {}, {}, {})".format(self.iarr, self.idx, self.names, self.tys, self.cs)


class CoFixExp(Exp):
    """CF %d [%s] [%s] [%s]"""
    def __init__(self, idx, names, tys, cs):
        assert isinstance(idx, int)
        for name in names:
            assert isinstance(name, str)
        for ty in tys:
            assert isinstance(ty, Exp)
        for c in cs:
            assert isinstance(c, Exp)
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
        return "CF({}, {}, {}, {})".format(self.idx, self.names, self.tys, self.cs)


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
        return "PJ({}, {})".format(self.proj, self.c)


# -------------------------------------------------
# Decoding low-level expressions

class DecodeCoqExp(object):
    def __init__(self, typs_table, bods_table, constrs_table):
        # Internal state
        self.typs_table = typs_table          # Dict[id, int]
        self.bods_table = bods_table          # Dict[id, int]
        self.constrs_table = constrs_table    # Dict[int, string]

        # Work state
        self.size_table = {}

        # Shared representation
        self.concr_ast = {}
        self.f_decoded = False
        self._decode_constrs()

    def decode_ast(self, key):
        return self.concr_ast[key]

    """
    def decode_ctx_bod(self, ident):
        assert isinstance(ident, str)
        idx = self.bods_table[ident]
        e = self.decode_ast(idx)
        if idx not in self.size_table:
            self.size_table[idx] = e.size()
        return e

    def decode_ctx_typ(self, ident):
        assert isinstance(ident, str)
        idx = self.typs_table[ident]
        e = self.decode_ast(idx)
        if idx not in self.size_table:
            self.size_table[idx] = e.size()
        return e

    def decode_ctx_typ_size(self, ident):
        idx = self.typs_table[ident]
        if idx in self.size_table:
            return self.size_table[idx]
        else:
            idx = self.typs_table[ident]
            e = self.decode_ast(idx)
            # print("COMPUTING SIZE OF {}".format(ident))
            size = e.size()
            # print("DONE")
            self.size_table[idx] = size
            return size

    def decode_goal(self, idx):
        e = self.decode_ast(idx)
        if idx not in self.size_table:
            self.size_table[idx] = e.size()
        return e

    def decode_goal_size(self, idx):
        if idx in self.size_table:
            return self.size_table[idx]
        else:
            e = self.decode_ast(idx)
            size = e.size()
            self.size_table[idx] = size
            return size
    """

    # ------------------------------------------
    # Internal decoding
    def _decode_constrs(self, f_display=False):
        # Initialize state
        self.edges = []
        self.rawasts = {}

        G = nx.DiGraph()
        for key, entry in self.constrs_table.items():
            G.add_node(key)
            e = self._decode_rawast(key, entry)
        G.add_edges_from(self.edges)
        if f_display:
            nx.drawing.nx_pylab.draw_kamada_kawai(G, with_labels=True)
            plt.show()

        keys = list(nx.algorithms.dag.topological_sort(G))
        for key in keys:
            c = self._decode_ast(key)
            if key not in self.concr_ast:
                self.concr_ast[key] = c

        # Clear state
        self.edges = []
        self.rawasts = {}

        self.f_decoded = True

    def _add_edges(self, idx, idxs):
        self.edges += [(idx, idx_p) for idx_p in idxs]

    def _santize_keys(self, c_idxs):
        c_idxs = c_idxs[1:-1]
        return [int(idx.strip()) for idx in c_idxs.split()]

    def _split_entry(self, entry):
        # NOTE(deh): FML fucking bullshit python
        toks = re.findall(r'\[[^}]*?\]|\S+', entry)
        return toks

    def _decode_rawast(self, key, entry):
        """First pass decoding to build dependency graph"""
        toks = self._split_entry(entry)
        kind = toks[0].strip()
        if kind == "R":
            # R %d
            idx = int(toks[1].strip())

            self.rawasts[key] = ("R", idx)
        elif kind == "V":
            # V %s
            x = toks[1].strip()

            self.rawasts[key] = ("V", x)
        elif kind == "M":
            # M %d
            idx = int(toks[1].strip())

            self.rawasts[key] = ("M", idx)
        elif kind == "E":
            # E %d [%s]
            exk = int(toks[1].strip())
            cs_idxs = self._santize_keys(toks[2].strip())
            
            self.rawasts[key] = ("E", exk, cs_idxs)
            self._add_edges(key, cs_idxs)
        elif kind == "S":
            # S %s
            sort = toks[1].strip()

            self.rawasts[key] = ("S", sort)
        elif kind == "CA":
            # CA %d %s %d
            c_idx = int(toks[1].strip())
            ck = toks[2].strip()
            ty_idx = int(toks[3].strip())

            self.rawasts[key] = ("CA", c_idx, ck, ty_idx)
            self._add_edges(key, [c_idx, ty_idx])
        elif kind == "P":
            # P %s %d %d
            name = toks[1].strip()
            ty1_idx = int(toks[2].strip())
            ty2_idx = int(toks[3].strip())
            
            self.rawasts[key] = ("P", name, ty1_idx, ty2_idx)
            self._add_edges(key, [ty1_idx, ty2_idx])
        elif kind == "L":
            # L %s %d %d
            name = toks[1].strip()
            ty_idx = int(toks[2].strip())
            # TODO(deh): Kludge, coq printing has bug
            c_idx = int(toks[3].strip())
            # c_idx = int((toks[3].strip())[:-1])

            self.rawasts[key] = ("L", name, ty_idx, c_idx)
            self._add_edges(key, [ty_idx, c_idx])
        elif kind == "LI":
            # LI %s %d %d %d
            name = toks[1].strip()
            c1_idx = int(toks[2].strip())
            ty_idx = int(toks[3].strip())
            c2_idx = int(toks[4].strip())

            self.rawasts[key] = ("LI", name, c1_idx, ty_idx, c2_idx)
            self._add_edges(key, [c1_idx, ty_idx, c2_idx])
        elif kind == "A":
            # A %d [%s]
            c_idx = int(toks[1].strip())
            cs_idxs = self._santize_keys(toks[2].strip())

            self.rawasts[key] = ("A", c_idx, cs_idxs)
            self._add_edges(key, [c_idx] + cs_idxs)
        elif kind == "C":
            # C %s [%s]
            const = toks[1].strip()
            ui = self._decode_universe_instance(toks[2].strip())
            
            self.rawasts[key] = ("C", const, ui)
        elif kind == "I":
            # I %s %d [%s]
            mutind = toks[1].strip()
            i = int(toks[2].strip())
            ui = self._decode_universe_instance(toks[3].strip())

            self.rawasts[key] = ("I", mutind, i, ui)
        elif kind == "CO":
            # CO %s %d %d [%s]
            mutind = toks[1].strip()
            i = int(toks[2].strip())
            j = int(toks[3].strip())
            ui = self._decode_universe_instance(toks[4].strip())

            self.rawasts[key] = ("CO", mutind, i, j, ui)
        elif kind == "CS":
            # CS [%s] %d %d [%s]
            case_info = toks[1].strip()
            c1_idx = int(toks[2].strip())
            c2_idx = int(toks[3].strip())
            cs_idxs = self._santize_keys(toks[4].strip())

            self.rawasts[key] = ("CS", case_info, c1_idx, c2_idx, cs_idxs)
            self._add_edges(key, [c1_idx, c2_idx] + cs_idxs)
        elif kind == "F":
            # F [%s] %d [%s] [%s] [%s]
            iarr = self._decode_iarr(toks[1].strip())
            idx = int(toks[2].strip())
            names = self._decode_names(toks[3].strip())
            ty_idxs = self._santize_keys(toks[4].strip())
            cs_idxs = self._santize_keys(toks[5].strip())
            
            self.rawasts[key] = ("F", iarr, idx, names, ty_idxs, cs_idxs)
            self._add_edges(key, ty_idxs + cs_idxs)
        elif kind == "CF":
            idx = int(toks[2].strip())
            names = self._decode_names(toks[3].strip())
            ty_idxs = self._santize_keys(toks[4].strip())
            cs_idxs = self._santize_keys(toks[5].strip())

            self.rawasts[key] = ("CF", idx, names, ty_idxs, cs_idxs)
            self._add_edges(key, ty_idxs + cs_idxs)
        elif kind == "PJ":
            proj = toks[1].strip()
            c_idx = int(toks[2].strip())

            self.rawasts[key] = ("PJ", proj, c_idx)
            self._add_edges(key, [c_idx])
        else:
            raise NameError("Kind {} not supported.".format(kind))

    def _decode_universe_instance(self, ui):
        ui = ui[1:-1]
        # TODO(deh): check latest coq format
        return UniverseInstance([u.strip() for u in ui.split(",")])

    def _decode_names(self, names):
        names = names[1:-1]
        # TODO(deh): check latest coq format
        return [name.strip() for name in names.split(",")]

    def _decode_iarr(self, iarr):
        iarr = iarr[1:-1]
        # TODO(deh): check latest coq format
        return [int(i.strip()) for i in iarr.split(",")]

    def _mkcon(self, key, c):
        c.tag = key
        self.concr_ast[key] = c
        return c

    def _decode_ast(self, key):
        """Complete decoding"""
        if key in self.concr_ast:
            return self.concr_ast[key]

        toks = self.rawasts[key]
        kind = toks[0]
        rest = toks[1:]
        if kind == "R":
            # R %d
            idx = rest[0]
            return self._mkcon(key, RelExp(idx))
        elif kind == "V":
            # V %s
            x = rest[0]
            return self._mkcon(key, VarExp(x))
        elif kind == "M":
            # M %d
            idx = int(toks[1].strip())
            return self._mkcon(key, MetaExp(rest[0]))
        elif kind == "E":
            # E %d [%s]
            exk, cs_idxs = rest
            cs = self._decode_asts(cs_idxs)
            return self._mkcon(key, EvarExp(exk, cs))
        elif kind == "S":
            # S %s
            sort = rest[0]
            return self._mkcon(key, SortExp(sort))
        elif kind == "CA":
            # CA %d %s %d
            c_idx, ck, ty_idx = rest
            c = self._decode_ast(c_idx)
            ty = self._decode_ast(ty_idx)
            return self._mkcon(key, CastExp(c, ck, ty))
        elif kind == "P":
            # P %s %d %d
            name, ty1_idx, ty2_idx = rest
            ty1 = self._decode_ast(ty1_idx)
            ty2 = self._decode_ast(ty2_idx)
            return self._mkcon(key, ProdExp(name, ty1, ty2))
        elif kind == "L":
            # L %s %d %d
            name, ty_idx, c_idx = rest

            ty = self._decode_ast(ty_idx)
            c = self._decode_ast(c_idx)
            return self._mkcon(key, LambdaExp(name, ty, c))
        elif kind == "LI":
            # LI %s %d %d %d
            name, c1_idx, ty_idx, c2_idx = rest
            c1 = self._decode_ast(c1_idx)
            ty = self._decode_ast(ty_idx)
            c2 = self._decode_ast(c2_idx)
            return self._mkcon(key, LetInExp(name, c1, ty, c2))
        elif kind == "A":
            # A %d [%s]
            c_idx, cs_idxs = rest
            c = self._decode_ast(c_idx)
            cs = self._decode_asts(cs_idxs)
            return self._mkcon(key, AppExp(c, cs))
        elif kind == "C":
            # C %s [%s]
            const, ui = rest 
            return self._mkcon(key, ConstExp(const, ui))
        elif kind == "I":
            # I %s %d [%s]
            mutind, i, ui = rest
            return self._mkcon(key, IndExp(mutind, i, ui))
        elif kind == "CO":
            # CO %s %d %d [%s]
            mutind, i, j, ui = rest
            return self._mkcon(key, ConstructExp(mutind, i, j, ui))
        elif kind == "CS":
            # CS [%s] %d %d [%s]
            case_info, c1_idx, c2_idx, cs_idxs = rest
            c1 = self._decode_ast(c1_idx)
            c2 = self._decode_ast(c2_idx)
            cs = self._decode_asts(cs_idxs)
            return self._mkcon(key, CaseExp(case_info, c1, c2, cs))
        elif kind == "F":
            # F [%s] %d [%s] [%s] [%s]
            iarr, idx, names, ty_idxs, cs_idxs = rest
            tys = self._decode_asts(ty_idxs)
            cs = self._decode_asts(cs_idxs)
            return self._mkcon(key, FixExp(iarr, idx, names, tys, cs))
        elif kind == "CF":
            # CF %d [%s] [%s] [%s]
            idx, names, ty_idxs, cs_idxs = rest
            tys = self._decode_asts(ty_idxs)
            cs = self._decode_asts(cs_idxs)
            return self._mkcon(key, CoFixExp(idx, names, tys, cs))
        elif kind == "PJ":
            # PJ %s %d
            proj, c_idx = rest
            c = self._decode_ast(c_idx)
            return self._mkcon(key, ProjExp(proj, c))
        else:
            raise NameError("Kind {} not supported.".format(kind))

    def _decode_asts(self, keys):
        return [self._decode_ast(key) for key in keys]

    def pp(self, tab=0):
        s = "\n".join(["{}: {}".format(ident, self.decode_ctx_typ(ident)) for ident, ty in self.typs_table.items()])
        return s


# -------------------------------------------------
# Computing sizes of coq-expressions efficiently

class SizeCoqExp(object):
    def __init__(self, concr_ast):
        self.concr_ast = concr_ast
        self.size_ast = {}

    def _sizecon(self, key, size):
        self.size_ast[key] = size
        return size

    def decode_size(self, key):
        return self.size(self.concr_ast[key])

    def size(self, c):
        key = c.tag
        if key in self.size_ast:
            return self.size_ast[key]

        if isinstance(c, RelExp):
            return self._sizecon(key, 1)
        elif isinstance(c, VarExp):
            return self._sizecon(key, 1)
        elif isinstance(c, MetaExp):
            return self._sizecon(key, 1)
        elif isinstance(c, EvarExp):
            size = 1 + self.sizes(c.cs)
            return self._sizecon(key, size)
        elif isinstance(c, SortExp):
            return self._sizecon(key, 1)
        elif isinstance(c, CastExp):
            size = 1 + self.size(c.c) + self.size(c.ty)
            return self._sizecon(key, size)
        elif isinstance(c, ProdExp):
            size = 1 + self.size(c.ty1) + self.size(c.ty2)
            return self._sizecon(key, size)
        elif isinstance(c, LambdaExp):
            size = 1 + self.size(c.ty) + self.size(c.c)
            return self._sizecon(key, size)
        elif isinstance(c, LetInExp):
            size = 1 + self.size(c.c1) + self.size(c.ty) + self.size(c.c2)
            return self._sizecon(key, size)
        elif isinstance(c, AppExp):
            size = 1 + self.size(c.c) + self.sizes(c.cs)
            return self._sizecon(key, size)
        elif isinstance(c, ConstExp):
            # TODO(deh): HMM?
            return self._sizecon(key, 1) 
        elif isinstance(c, IndExp):
            # TODO(deh): HMM?
            return self._sizecon(key, 1)
        elif isinstance(c, ConstructExp):
            # TODO(deh): HMM?
            return self._sizecon(key, 1)
        elif isinstance(c, CaseExp):
            size = 1 + self.size(c.c1) + self.size(c.c2) + self.sizes(c.cs)
            return self._sizecon(key, size)
        elif isinstance(c, FixExp):
            size = 1 + self.sizes(c.tys) + self.sizes(c.cs)
            return self._sizecon(key, size)
        elif isinstance(c, CoFixExp):
            size = 1 + self.sizes(c.tys) + self.sizes(c.cs)
            return self._sizecon(key, size)
        elif isinstance(c, ProjExp):
            size = 1 + self.size(c.c)
            return self._sizecon(key, size)
        else:
            raise NameError("Kind {} not supported".format(c))

    def sizes(self, cs):
        return sum([self.size(c) for c in cs])


"""
def decode_ast_size(self, c):
        if isinstance(c, RelExp):
            # 1
        elif isinstance(c, VarExp):
            # 1
        elif isinstance(c, MetaExp):
            # 1
        elif isinstance(c, EvarExp):
            # c.cs
        elif isinstance(c, SortExp):
            # 1
        elif isinstance(c, CastExp):
            # c.c, c.ty
        elif isinstance(c, ProdExp):
            # c.ty1, c.ty2
        elif isinstance(c, LambdaExp):
            # c.ty, c.cs
        elif isinstance(c, LetInExp):
            # c.c1, c.ty, c.c2
        elif isinstance(c, AppExp):
            # c.c, c.cs
        elif isinstance(c, ConstExp):
            # 1
        elif isinstance(c, IndExp):
            # 1
        elif isinstance(c, ConstructExp):
            # 1
        elif isinstance(c, CaseExp):
            # c.c1, c.c2, c.cs
        elif isinstance(c, FixExp):
            # c.tys, c.cs
        elif isinstance(c, CoFixExp):
            # c.tys, c.cs
        elif isinstance(c, ProjExp):
            # c.c
        else:
            raise NameError("Kind {} not supported".format(c))
"""

"""
def decode_asts(self, c_idxs):
    c_idxs = c_idxs[1:-1]
    keys = [int(idx.strip()) for idx in c_idxs.split()]
    return [self.decode_ast(key) for key in keys]

def decode_ast2(self, key, entry):
    print("DECODING2 key={}   entry=\"{}\"".format(key, entry))
    toks = self._split_entry(entry)
    kind = toks[0].strip()
    if kind == "R":
        # R %d
        idx = int(toks[1].strip())

        c_p = RelExp(idx)
        self.table[key] = c_p
        return c_p
    elif kind == "V":
        # V %s
        x = toks[1].strip()

        c_p = VarExp(x)
        self.table[key] = c_p
        return c_p
    elif kind == "M":
        # M %d
        idx = int(toks[1].strip())

        c_p = MetaExp(idx)
        self.table[key] = c_p
        return c_p
    elif kind == "E":
        # E %d [%s]
        exk = int(toks[1].strip())
        cs_idxs = toks[2].strip()
        
        cs = self.decode_asts(cs_idxs)
        c_p = EvarExp(exk, cs)
        self.table[key] = c_p
        return c_p
    elif kind == "S":
        # S %s
        sort = toks[1].strip()

        c_p = SortExp(sort)
        self.table[key] = c_p
        return c_p
    elif kind == "CA":
        # CA %d %s %d
        c_idx = int(toks[1].strip())
        ck = toks[2].strip()
        ty_idx = int(toks[3].strip())

        c = self.decode_ast(c_idx)
        ty = self.decode_ast(ty_idx)
        c_p = CastExp(c, ck, ty)
        self.table[key] = c_p
        return c_p
    elif kind == "P":
        # P %s %d %d
        name = toks[1].strip()
        ty1_idx = int(toks[2].strip())
        ty2_idx = int(toks[3].strip())
        
        ty1 = self.decode_ast(ty1_idx)
        ty2 = self.decode_ast(ty2_idx)
        c_p = ProdExp(name, ty1, ty2)
        self.table[key] = c_p
        return c_p
    elif kind == "L":
        # L %s %d %d
        name = toks[1].strip()
        ty_idx = int(toks[2].strip())
        # TODO(deh): Kludge, coq printing has bug
        # c_idx = int(toks[3].strip())
        c_idx = int((toks[3].strip())[:-1])

        ty = self.decode_ast(ty_idx)
        c = self.decode_ast(c_idx)
        c_p = LambdaExp(name, ty, c)
        self.table[key] = c_p
        return c_p
    elif kind == "LI":
        # LI %s %d %d %d
        name = toks[1].strip()
        c1_idx = int(toks[2].strip())
        ty_idx = int(toks[3].strip())
        c2_idx = int(toks[4].strip())

        c1 = self.decode_ast(c1_idx)
        ty = self.decode_ast(ty_idx)
        c2 = self.decode_ast(c2_idx)
        c_p = LetInExp(name, c1, ty, c2)
        self.table[key] = c_p
        return c_p
    elif kind == "A":
        # A %d [%s]
        c_idx = int(toks[1].strip())
        cs_idxs = toks[2].strip()

        c = self.decode_ast(c_idx)
        cs = self.decode_asts(cs_idxs)
        c_p = AppExp(c, cs)
        self.table[key] = c_p
        return c_p
    elif kind == "C":
        # C %s [%s]
        const = toks[1].strip()
        ui = self.decode_universe_instance(toks[2].strip())
        
        c_p = ConstExp(const, ui)
        self.table[key] = c_p
        return c_p
    elif kind == "I":
        # I %s %d [%s]
        mutind = toks[1].strip()
        i = int(toks[2].strip())
        ui = self.decode_universe_instance(toks[3].strip())

        c_p = IndExp(mutind, i, ui)
        self.table[key] = c_p
        return c_p
    elif kind == "CO":
        # CO %s %d %d [%s]
        mutind = toks[1].strip()
        i = int(toks[2].strip())
        j = int(toks[3].strip())
        ui = self.decode_universe_instance(toks[4].strip())

        c_p = ConstructExp(mutind, i, j, ui)
        self.table[key] = c_p
        return c_p
    elif kind == "CS":
        # CS [%s] %d %d [%s]
        case_info = toks[1].strip()
        c1_idx = int(toks[2].strip())
        c2_idx = int(toks[3].strip())
        cs_idxs = toks[4].strip()

        c1 = self.decode_ast(c1_idx)
        c2 = self.decode_ast(c2_idx)
        cs = self.decode_asts(cs_idxs)
        c_p = CaseExp(case_info, c1, c2, cs)
        self.table[key] = c_p
        return c_p
    elif kind == "F":
        # F [%s] %d [%s] [%s] [%s]
        _iarr = toks[1].strip()
        idx = int(toks[2].strip())
        _names = toks[3].strip()
        ty_idxs = toks[4].strip()
        cs_idxs = toks[5].strip()
        
        iarr = self.decode_iarr(_iarr)
        names = self.decode_names(_names)
        tys = self.decode_asts(ty_idxs)
        cs = self.decode_asts(cs_idxs)
        c_p = FixExp(iarr, idx, names, tys, cs)
        self.table[key] = c_p
        return c_p
    elif kind == "CF":
        idx = int(toks[2].strip())
        _names = toks[3].strip()
        ty_idxs = toks[4].strip()
        cs_idxs = toks[5].strip()

        names = self.decode_names(_names)
        tys = self.decode_asts(ty_idxs)
        cs = self.decode_asts(cs_idxs)
        c_p = CoFixExp(idx, names, tys, cs)
        self.table[key] = c_p
        return c_p
    elif kind == "PJ":
        proj = toks[1].strip()
        c_idx = int(toks[2].strip())

        c = self.decode_ast(c_idx)
        c_p = Proj(proj, c)
        self.table[key] = c_p
        return c_p
    else:
        raise NameError("Kind {} not supported.".format(kind))
"""
