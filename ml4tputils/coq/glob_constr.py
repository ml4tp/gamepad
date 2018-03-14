"""
[Note]

Contains Coq glob_constr AST (almost kernel, but no type inference).
This AST is used for tactic arguments.
"""


# -------------------------------------------------
# Global Reference

class GlobalReference(object):
    pass


class VarRef(object):
    def __init__(self, x):
        self.x = x

    def __str__(self):
        return self.x


class ConstRef(object):
    def __init__(self, const):
        self.const = const

    def __str__(self):
        return self.const


class IndRef(object):
    def __init__(self, mutind, i):
        self.mutind = mutind
        self.i = i

    def __str__(self):
        return "{}.{}".format(self.mutind, self.i)


class ConstructRef(object):
    def __init__(self, mutind, i, j):
        self.mutind = mutind
        self.i = i
        self.j = j

    def __str__(self):
        return "{}.{}.{}".format(self.mutind, self.i, self.j)


# -------------------------------------------------
# Expressions

class GExp(object):
    def __init__(self):
        self.tag = None


class PredicatePattern(object):
    def __init__(self, name, m_ind_and_names):
        self.name = name
        self.m_ind_and_names = m_ind_and_names


class TomatchTuple(object):
    def __init__(self, g, pp):
        assert isinstance(g, GExp)
        assert isinstance(pp, PredicatePattern)
        self.g = g
        self.pp = pp


class CasesClause(object):
    def __init__(self, ids, cps, g):
        assert isinstance(g, GExp)
        self.ids = ids
        self.cps = cps
        self.g = g


class GRef(GExp):
    """| GRef of (Loc.t * global_reference * glob_level list option)
      (** An identifier that represents a reference to an object defined
          either in the (global) environment or in the (local) context. *)
    """
    def __init__(self, gref, levs):
        super().__init__()
        self.gref = gref
        self.levs = levs

    def __str__(self):
        return str(self.gref)


class GVar(GExp):
    """| GVar of (Loc.t * Id.t)
      (** An identifier that cannot be regarded as "GRef".
          Bound variables are typically represented this way. *)
    """
    def __init__(self, x):
        assert isinstance(x, str)
        super().__init__()
        self.x = x

    def __str__(self):
        return self.x


class GEvar(GExp):
    """| GEvar of Loc.t * existential_name * (Id.t * glob_constr) list
    """
    def __init__(self, ev, id_and_globs):
        super().__init__()
        self.ev = ev
        self.id_and_globs = id_and_globs


class GPatVar(GExp):
    """| GPatVar of Loc.t * (bool * patvar) (** Used for patterns only *)
    """
    def __init__(self, b, pv):
        assert isinstance(b, bool)
        super().__init__()
        self.b = b
        self.pv = pv


class GApp(GExp):
    """| GApp of Loc.t * glob_constr * glob_constr list
    """
    def __init__(self, g, gs):
        assert isinstance(g, GExp)
        for g_p in gs:
            assert isinstance(g_p, GExp)
        super().__init__()
        self.g = g
        self.gs = gs

    def __str__(self):
        return "({} {})".format(str(self.g), " ".join([str(g) for g in self.gs]))


class GLambda(GExp):
    """| GLambda of Loc.t * Name.t * binding_kind *  glob_constr * glob_constr
    """
    def __init__(self, name, bk, g_ty, g_bod):
        assert isinstance(g_ty, GExp)
        assert isinstance(g_bod, GExp)
        super().__init__()
        self.name = name
        self.bk = bk
        self.g_ty = g_ty
        self.g_bod = g_bod
    

class GProd(GExp):
    """| GProd of Loc.t * Name.t * binding_kind * glob_constr * glob_constr
    """
    def __init__(self, name, bk, g_ty, g_bod):
        assert isinstance(g_ty, GExp)
        assert isinstance(g_bod, GExp)
        super().__init__()
        self.name = name
        self.bk = bk
        self.g_ty = g_ty
        self.g_bod = g_bod


class GLetIn(GExp):
    """| GLetIn of Loc.t * Name.t * glob_constr * glob_constr
    """
    def __init__(self, name, g_ty, g_bod):
        assert isinstance(g_ty, GExp)
        assert isinstance(g_bod, GExp)
        super().__init__()
        self.name = name
        self.g_ty = g_ty
        self.g_bod = g_bod


class GCases(GExp):
    """| GCases of Loc.t * case_style * glob_constr option * tomatch_tuples * cases_clauses
      (** [GCases(l,style,r,tur,cc)] = "match 'tur' return 'r' with 'cc'" (in [MatchStyle]) *)
    """
    def __init__(self, csty, m_g, tmts, ccs):
        # for tmt in tmts:
        #     assert isinstance(tmt, TomatchTuple)
        # for cc in ccs:
        #     assert isinstance(cc, CasesClause)
        super().__init__()
        self.csty = csty
        self.m_g = m_g
        self.tmts = tmts
        self.ccs = ccs


class GLetTuple(GExp):
    """| GLetTuple of Loc.t * Name.t list * (Name.t * glob_constr option) *
      glob_constr * glob_constr
    """
    def __init__(self, names, m_name_and_ty, g1, g2):
        assert isinstance(g1, GExp)
        assert isinstance(g2, GExp)
        super().__init__()
        self.names = names
        self.m_name_and_ty = m_name_and_ty
        self.g1 = g1
        self.g2 = g2


class GIf(GExp):
    """| GIf of Loc.t * glob_constr * (Name.t * glob_constr option) * glob_constr * glob_constr
    """
    def __init__(self, g1, m_name_and_ty, g2, g3):
        assert isinstance(g1, GExp)
        assert isinstance(g2, GExp)
        assert isinstance(g3, GExp)
        super().__init__()
        self.g1 = g1
        self.m_name_and_ty = m_name_and_ty
        self.g2 = g2
        self.g3 = g3


class GRec(GExp):
    """| GRec of Loc.t * fix_kind * Id.t array * glob_decl list array *
      glob_constr array * glob_constr array
    """
    def __init__(self, fix_kind, ids, gdecl_args, gc_tys, gc_bods):
        for gc in gc_tys:
            assert isinstance(gc, GExp)
        for gc in gc_bods:
            assert isinstance(gc, GExp)
        super().__init__()
        self.fix_kind = fix_kind       # TODO(deh): fix_kind?
        self.ids = ids
        self.gdecl_args = gdecl_args   # TODO(deh): glob_decl?
        self.gc_tys = gc_tys
        self.gc_bods = gc_bods


class GSort(GExp):
    """| GSort of Loc.t * glob_sort
    """
    def __init__(self, gsort):
        super().__init__()
        self.gsort = gsort


class GHole(GExp):
    """| GHole of (Loc.t * Evar_kinds.t * intro_pattern_naming_expr * Genarg.glob_generic_argument option)
    """
    def __init__(self, ek, ipne, m_ga):
        super().__init__()
        self.ek = ek
        self.ipne = ipne
        self.m_ga = m_ga


class GCast(GExp):
    """| GCast of Loc.t * glob_constr * glob_constr cast_type
    """
    def __init__(self, g, g_cty):
        assert isinstance(g, GExp)
        super().__init__()
        self.g = g
        self.g_cty = g_cty
