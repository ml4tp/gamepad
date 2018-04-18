from coq.constr import Name, Inductive
from lib.myhist import MyHist


"""
[Note]

Contains Coq glob_constr AST (almost kernel, but no type inference).
This AST is used for tactic arguments.
"""


class GExp(object):
    """Base glob_constr expression"""
    def __init__(self):
        self.tag = None


# -------------------------------------------------
# Global Reference

class GlobalReference(object):
    pass


class VarRef(GlobalReference):
    def __init__(self, x):
        self.x = x

    def __str__(self):
        return self.x


class ConstRef(GlobalReference):
    def __init__(self, const):
        assert isinstance(const, Name)
        self.const = const

    def __str__(self):
        return self.const


class IndRef(GlobalReference):
    def __init__(self, ind):
        assert isinstance(ind, Inductive)
        self.ind = ind

    def __str__(self):
        return "{}".format(self.ind)


class ConstructRef(GlobalReference):
    def __init__(self, ind, conid):
        assert isinstance(ind, Inductive)
        assert isinstance(conid, int)
        self.ind = ind
        self.conid = conid

    def __str__(self):
        return "{}.{}".format(self.ind, self.conid)


# -------------------------------------------------
# CasesPattern

class CasesPattern(object):
    def get_names(self):
        raise NotImplementedError


class PatVar(CasesPattern):
    def __init__(self, name):
        assert isinstance(name, Name)
        self.name = name

    def get_names(self):
        return [self.name]


class PatCstr(CasesPattern):
    def __init__(self, ind, j, cps, name):
        assert isinstance(ind, Inductive)
        assert isinstance(j, int)
        for cp in cps:
            assert isinstance(cp, CasesPattern)
        assert isinstance(name, Name)
        self.ind = ind
        self.j = j
        self.cps = cps
        self.name = name

    def get_names(self):
        acc = []
        for cp in self.cps:
            acc += cp.get_names()
        return acc


# -------------------------------------------------
# Other auxilliary data-structures

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
        for cp in cps:
            assert isinstance(cp, CasesPattern)
        assert isinstance(g, GExp)
        self.ids = ids
        self.cps = cps
        self.g = g


class CastType(object):
    def __init__(self, kind, m_gc):
        assert m_gc is None or isinstance(m_gc, GExp)
        self.kind = kind
        self.m_gc = m_gc


# -------------------------------------------------
# Expressions

class GRef(GExp):
    """| GRef of (Loc.t * global_reference * glob_level list option)
      (** An identifier that represents a reference to an object defined
          either in the (global) environment or in the (local) context. *)
    """
    def __init__(self, gref, levs):
        assert isinstance(gref, GlobalReference)
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
    def __init__(self, g, gs, iargs):
        assert isinstance(g, GExp)
        for g_p in gs:
            assert isinstance(g_p, GExp)
        super().__init__()
        self.g = g
        self.gs = gs
        self.iargs = iargs

    def __str__(self):
        return "({} {})".format(str(self.g), " ".join([str(g) for g in self.gs]))


class GLambda(GExp):
    """| GLambda of Loc.t * Name.t * binding_kind *  glob_constr * glob_constr
    """
    def __init__(self, name, bk, g_ty, g_bod):
        # TODO(deh): Fix parsing to parse name
        assert isinstance(name, Name)
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
        assert isinstance(name, Name)
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
    def __init__(self, name, g1, g2):
        assert isinstance(name, Name)
        assert isinstance(g1, GExp)
        assert isinstance(g2, GExp)
        super().__init__()
        self.name = name
        self.g1 = g1
        self.g2 = g2


class GCases(GExp):
    """| GCases of Loc.t * case_style * glob_constr option * tomatch_tuples * cases_clauses
      (** [GCases(l,style,r,tur,cc)] = "match 'tur' return 'r' with 'cc'" (in [MatchStyle]) *)
    """
    def __init__(self, csty, m_g, tmts, ccs):
        for tmt in tmts:
            assert isinstance(tmt, TomatchTuple)
        for cc in ccs:
            assert isinstance(cc, CasesClause)
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
        for name in names:
            assert isinstance(name, Name)
        assert isinstance(g1, GExp)
        assert isinstance(g2, GExp)
        assert isinstance(m_name_and_ty[0], Name)
        assert m_name_and_ty[1] is None or isinstance(m_name_and_ty[1], GExp)
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
        assert isinstance(m_name_and_ty[0], Name)
        assert m_name_and_ty[1] is None or isinstance(m_name_and_ty[1], GExp)
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
        assert isinstance(g_cty, CastType)
        super().__init__()
        self.g = g
        self.g_cty = g_cty


# -------------------------------------------------
# Other

COQGC = ['GRef', 'GVar', 'GEvar', 'GPatVar', 'GApp', 'GLambda', 'GProd', 'GLetIn', 'GCases',
         'GLetTuple', 'GIf', 'GRec', 'GSort', 'GHole', 'GCast']


COQGC_HIST = MyHist(COQGC)
