import networkx as nx
import matplotlib.pyplot as plt
import re

from coq.ast import *
from coq.util import ChkCoqExp

"""
[Note]

Decode shared representation of Coq in .dump into table.
"""


# -------------------------------------------------
# Decoding low-level expressions

class DecodeCoqExp(object):
    def __init__(self, ctx_typs, ctx_bods, constr_share):
        # Internal state
        self.ctx_typs = ctx_typs           # Dict[id, int]
        self.ctx_bods = ctx_bods           # Dict[id, int]
        self.constr_share = constr_share   # Dict[int, string]

        # Shared representation
        self.decoded = {}
        self.f_decoded = False
        self._decode_constrs()
        ChkCoqExp(self.decoded).chk_decoded()

    def decode_exp_by_key(self, key):
        return self.decoded[key]

    def decode_exp_by_ctxid(self, ident):
        return self.decode_exp_by_key(self.ctx_typs[ident])

    def _decode_constrs(self, f_display=False):
        # Initialize state
        self.edges = []
        self.rawasts = {}

        # Lex raw-ast and build dependency graph
        G = nx.DiGraph()
        for key, entry in self.constr_share.items():
            G.add_node(key)
            self._parse_rawast(key, entry)
        G.add_edges_from(self.edges)
        if f_display:
            nx.drawing.nx_pylab.draw_kamada_kawai(G, with_labels=True)
            plt.show()

        # Use topological sort of dependencies to decode ast
        keys = list(nx.algorithms.dag.topological_sort(G))
        for key in keys:
            c = self._decode_ast(key)
            self._mkcon(key, c)

        # Clear state
        self.edges = []
        self.rawasts = {}

        self.f_decoded = True

    # -------------------------------------------------
    # First pass decoding
    def _add_edges(self, idx, idxs):
        self.edges += [(idx, idx_p) for idx_p in idxs]

    def _santize_keys(self, c_idxs):
        c_idxs = c_idxs[1:-1]
        return [int(idx.strip()) for idx in c_idxs.split()]

    def _split_entry(self, entry):
        # NOTE(deh): FML fucking bullshit python
        toks = re.findall(r'\[[^}]*?\]|\S+', entry)
        return toks

    def _parse_rawast(self, key, entry):
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
            name = self._parse_rawname(toks[1].strip())
            ty1_idx = int(toks[2].strip())
            ty2_idx = int(toks[3].strip())

            self.rawasts[key] = ("P", name, ty1_idx, ty2_idx)
            self._add_edges(key, [ty1_idx, ty2_idx])
        elif kind == "L":
            # L %s %d %d
            name = self._parse_rawname(toks[1].strip())
            ty_idx = int(toks[2].strip())
            c_idx = int(toks[3].strip())

            self.rawasts[key] = ("L", name, ty_idx, c_idx)
            self._add_edges(key, [ty_idx, c_idx])
        elif kind == "LI":
            # LI %s %d %d %d
            name = self._parse_rawname(toks[1].strip())
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
            const = self._parse_rawname(toks[1].strip())
            ui = self._parse_rawuniverse_instance(toks[2].strip())

            self.rawasts[key] = ("C", const, ui)
        elif kind == "I":
            # I %s %d [%s]
            mutind = self._parse_rawname(toks[1].strip())
            pos = int(toks[2].strip())
            ui = self._parse_rawuniverse_instance(toks[3].strip())

            self.rawasts[key] = ("I", mutind, pos, ui)
        elif kind == "CO":
            # CO %s %d %d [%s]
            mutind = self._parse_rawname(toks[1].strip())
            pos = int(toks[2].strip())
            conid = int(toks[3].strip())
            ui = self._parse_rawuniverse_instance(toks[4].strip())

            self.rawasts[key] = ("CO", mutind, pos, conid, ui)
        elif kind == "CS":
            # CS [%s] %d %d [%s]
            idx = entry.find(']]')
            hd = entry[2:idx]
            tl = entry[idx+2:]
            toks = self._split_entry(tl)
            case_info = self._parse_rawcase_info(hd.strip())
            c1_idx = int(toks[0].strip())
            c2_idx = int(toks[1].strip())
            cs_idxs = self._santize_keys(toks[2].strip())
            """
            case_info = self._parse_rawcase_info(toks[1].strip())
            c1_idx = int(toks[2].strip())
            c2_idx = int(toks[3].strip())
            cs_idxs = self._santize_keys(toks[4].strip())
            """

            self.rawasts[key] = ("CS", case_info, c1_idx, c2_idx, cs_idxs)
            self._add_edges(key, [c1_idx, c2_idx] + cs_idxs)
        elif kind == "F":
            # F [%s] %d [%s] [%s] [%s]
            iarr = self._parse_rawiarr(toks[1].strip())
            idx = int(toks[2].strip())
            names = self._parse_rawnames(toks[3].strip())
            ty_idxs = self._santize_keys(toks[4].strip())
            cs_idxs = self._santize_keys(toks[5].strip())

            self.rawasts[key] = ("F", iarr, idx, names, ty_idxs, cs_idxs)
            self._add_edges(key, ty_idxs + cs_idxs)
        elif kind == "CF":
            idx = int(toks[2].strip())
            names = self._parse_rawnames(toks[3].strip())
            ty_idxs = self._santize_keys(toks[4].strip())
            cs_idxs = self._santize_keys(toks[5].strip())

            self.rawasts[key] = ("CF", idx, names, ty_idxs, cs_idxs)
            self._add_edges(key, ty_idxs + cs_idxs)
        elif kind == "PJ":
            proj = self.decode_rawname(toks[1].strip())
            c_idx = int(toks[2].strip())

            self.rawasts[key] = ("PJ", proj, c_idx)
            self._add_edges(key, [c_idx])
        else:
            raise NameError("Kind {} not supported.".format(kind))

    def _parse_rawname(self, name):
        # TODO(deh): Hierarchical parsing?
        return Name(name.strip())

    def _parse_rawnames(self, names):
        names = names[1:-1]
        return [self._parse_rawname(name) for name in names.split()]

    def _parse_rawuniverse_instance(self, ui):
        ui = ui[1:-1]
        return UniverseInstance([u.strip() for u in ui.split()])

    def _parse_rawiarr(self, iarr):
        iarr = iarr[1:-1]
        return [int(i.strip()) for i in iarr.split()]

    def _parse_rawcase_info(self, ci):
        ci = ci[1:-1]
        toks = self._split_entry(ci)
        mutind = self._parse_rawname(toks[0])
        pos = int(toks[1])
        npar = int(toks[2].strip())
        # TODO(deh): check latest coq format
        cstr_ndecls = self._parse_rawiarr(toks[3].strip())
        # cstr_ndecls = toks[3].strip()
        # TODO(deh): check latest coq format
        cstr_nargs = self._parse_rawiarr(toks[4].strip())
        # cstr_nargs = toks[4].strip()
        return CaseInfo(Inductive(mutind, pos), npar, cstr_ndecls, cstr_nargs)

    # -------------------------------------------------
    # Second pass of decoding
    def _mkcon(self, key, c):
        if key in self.decoded:
            return self.decoded[key]
        else:
            c.tag = key
            self.decoded[key] = c
            return c

    def _decode_ast(self, key):
        """Complete decoding"""
        if key in self.decoded:
            return self.decoded[key]

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
            mutind, pos, ui = rest
            return self._mkcon(key, IndExp(Inductive(mutind, pos), ui))
        elif kind == "CO":
            # CO %s %d %d [%s]
            mutind, pos, conid, ui = rest
            return self._mkcon(key,
                               ConstructExp(Inductive(mutind, pos), conid, ui))
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
        s = "\n".join(["{}: {}".format(ident, self.decode_ctx_typ(ident)) for ident, ty in self.ctx_typs.items()])
        return s
