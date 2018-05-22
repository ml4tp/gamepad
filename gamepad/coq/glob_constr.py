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

    def apted_tree(self):
        raise NotImplementedError


# -------------------------------------------------
# Global Reference

class GlobalReference(object):
    pass


class VarRef(GlobalReference):
    def __init__(self, x):
        assert isinstance(x, str)
        self.x = x

    def __str__(self):
        return self.x


class ConstRef(GlobalReference):
    def __init__(self, const):
        assert isinstance(const, Name)
        self.const = const

    def __str__(self):
        return str(self.const)


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

    def apted_tree(self):
        raise NotImplementedError


class PatVar(CasesPattern):
    def __init__(self, name):
        assert isinstance(name, Name)
        self.name = name

    def __str__(self):
        return str(self.name)

    def get_names(self):
        return [self.name]

    def apted_tree(self):
        return "{{{}}}".format(self.name)


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

    def __str__(self):
        return str(self.name)

    def get_names(self):
        acc = []
        for cp in self.cps:
            acc += cp.get_names()
        return acc

    def apted_tree(self):
        acc = ""
        for cp in self.cps:
            acc += cp.apted_tree()
        return acc


# -------------------------------------------------
# Other auxilliary data-structures

class PredicatePattern(object):
    def __init__(self, name, m_ind_and_names):
        self.name = name
        self.m_ind_and_names = m_ind_and_names

    def __str__(self):
        return "{}".format(self.name)

    def apted_tree(self):
        return "{{{}}}".format(self.name)


class TomatchTuple(object):
    def __init__(self, g, pp):
        assert isinstance(g, GExp)
        assert isinstance(pp, PredicatePattern)
        self.g = g
        self.pp = pp

    def __str__(self):
        return "({} {})".format(str(self.g), str(self.pp))

    def apted_tree(self):
        return "{{{}}}".format(self.g.apted_tree(), self.pp.apted_tree())


class CasesClause(object):
    def __init__(self, ids, cps, g):
        for cp in cps:
            assert isinstance(cp, CasesPattern)
        assert isinstance(g, GExp)
        self.ids = ids
        self.cps = cps
        self.g = g

    def __str__(self):
        s_ids = "({})".format(" ".join([str(ident) for ident in self.ids]))
        s_cps = "({})".format(" ".join([str(cp) for cp in self.cps]))
        return "({} {} {})".format(s_ids, s_cps, str(self.g))

    def apted_tree(self):
        s_ids = "".join(["{{{}}}".format(ident) for ident in self.ids])
        s_cps = "".join([cp.apted_tree() for cp in self.cps])
        return "{{CC{}{}{}}}".format(s_ids, s_cps, self.g.apted_tree())


class CastType(object):
    def __init__(self, kind, m_gc):
        assert m_gc is None or isinstance(m_gc, GExp)
        self.kind = kind
        self.m_gc = m_gc

    def __str__(self):
        return "(CT {} {})".format(self.kind, self.m_gc)

    def apted_tree(self):
        if self.m_gc is None:
            return "{{CT{}{{{}}}}}".format(self.kind, "N")
        else:
            return "{{CT{}{{{}}}}}".format(self.kind, self.m_gc.apted_tree())


class GlobDecl(object):
    def __init__(self, name, bk, m_gc, gc):
        assert isinstance(name, Name)
        # binding kind?
        assert m_gc is None or isinstance(m_gc, GExp)
        assert isinstance(gc, GExp)
        self.name = name
        self.bk = bk
        self.m_gc = m_gc
        self.gc = gc


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
        return "(! {})".format(str(self.gref))

    def apted_tree(self):
        return "{{!{}}}".format(str(self))


class GVar(GExp):
    """| GVar of (Loc.t * Id.t)
      (** An identifier that cannot be regarded as "GRef".
          Bound variables are typically represented this way. *)
    """
    def __init__(self, x):
        assert isinstance(x, str)   # NOTE(deh): identifer object later?
        super().__init__()
        self.x = x

    def __str__(self):
        return "(V {})".format(self.x)

    def apted_tree(self):
        return "{{V{}}}".format(str(self))


class GEvar(GExp):
    """| GEvar of Loc.t * existential_name * (Id.t * glob_constr) list
    """
    def __init__(self, ev, id_and_globs):
        assert isinstance(ev, str)   # NOTE(deh): existential_name object later?
        # TODO(deh): ignoring id_and_globs for now
        super().__init__()
        self.ev = ev
        self.id_and_globs = id_and_globs

    def __str__(self):
        return "(E {})".format(str(self.ev))

    def apted_tree(self):
        return "{{E{}}}".format(str(self))


class GPatVar(GExp):
    """| GPatVar of Loc.t * (bool * patvar) (** Used for patterns only *)
    """
    def __init__(self, b, pv):
        assert isinstance(b, bool)
        assert isinstance(pv, str)    # NOTE(deh): patvar object later?
        super().__init__()
        self.b = b
        self.pv = pv

    def __str__(self):
        return "(PV {})".format(str(self.pv))

    def apted_tree(self):
        return "{{PV{}}}".format(str(self))


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
        return "(A {} {})".format(str(self.g), " ".join([str(g) for g in self.gs]))

    def apted_tree(self):
        return "{{A{}{}}}".format(self.g.apted_tree(), "".join([g.apted_tree() for g in self.gs]))


class GLambda(GExp):
    """| GLambda of Loc.t * Name.t * binding_kind *  glob_constr * glob_constr
    """
    def __init__(self, name, bk, g_ty, g_bod):
        assert isinstance(name, Name)
        assert isinstance(bk, str)     # NOTE(deh): binding_kind object later?
        assert isinstance(g_ty, GExp)
        assert isinstance(g_bod, GExp)
        super().__init__()
        self.name = name
        self.bk = bk
        self.g_ty = g_ty
        self.g_bod = g_bod

    def __str__(self):
        return "(L {} {} {})".format(self.name, str(self.g_ty), str(self.g_bod))

    def apted_tree(self):
        return "{{L{{{}}}{}{}}}".format(self.name, self.g_ty.apted_tree(), self.g_bod.apted_tree())


class GProd(GExp):
    """| GProd of Loc.t * Name.t * binding_kind * glob_constr * glob_constr
    """
    def __init__(self, name, bk, g_ty, g_bod):
        assert isinstance(name, Name)
        assert isinstance(bk, str)      # NOTE(deh): binding_kind object later?
        assert isinstance(g_ty, GExp)
        assert isinstance(g_bod, GExp)
        super().__init__()
        self.name = name
        self.bk = bk
        self.g_ty = g_ty
        self.g_bod = g_bod

    def __str__(self):
        return "(P {} {} {})".format(self.name, str(self.g_ty), str(self.g_bod))

    def apted_tree(self):
        return "{{P{{{}}}{}{}}}".format(self.name, self.g_ty.apted_tree(), self.g_bod.apted_tree())


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

    def __str__(self):
        return "(LI {} {} {})".format(self.name, str(self.g1), str(self.g2))

    def apted_tree(self):
        return "{{LI{{{}}}{}{}}}".format(self.name, self.g1.apted_tree(), self.g2.apted_tree())


class GCases(GExp):
    """| GCases of Loc.t * case_style * glob_constr option * tomatch_tuples * cases_clauses
      (** [GCases(l,style,r,tur,cc)] = "match 'tur' return 'r' with 'cc'" (in [MatchStyle]) *)
    """
    def __init__(self, csty, m_g, tmts, ccs):
        assert isinstance(csty, str)    # NOTE(deh): cast style object later?
        assert m_g is None or isinstance(m_g, GExp)
        for tmt in tmts:
            assert isinstance(tmt, TomatchTuple)
        for cc in ccs:
            assert isinstance(cc, CasesClause)
        super().__init__()
        self.csty = csty
        self.m_g = m_g
        self.tmts = tmts
        self.ccs = ccs

    def __str__(self):
        s_tmts = "({})".format(" ".join([str(tmt) for tmt in self.tmts]))
        s_ccs = "({})".format(" ".join([str(cc) for cc in self.ccs]))
        return "(C {} {})".format(s_tmts, s_ccs)

    def apted_tree(self):
        s_tmts = "".join([tmt.apted_tree() for tmt in self.tmts])
        s_ccs = "".join([cc.apted_tree() for cc in self.ccs])
        return "{{C{}{}}}".format(s_tmts, s_ccs)


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

        # Destruct g1 into fst and snd components
        self.g1_fst = GApp(GRef(ConstRef(Name("Coq.Init.Datatypes.fst")), []), [g1], [None])
        self.g1_snd = GApp(GRef(ConstRef(Name("Coq.Init.Datatypes.snd")), []), [g1], [None])

        self.g2 = g2

    def __str__(self):
        s_names = "( )".format(" ".join([str(name) for name in self.names]))
        return "(LT {} {} {})".format(s_names, str(self.g1_fst), str(self.g1_snd), str(self.g2))

    def apted_tree(self):
        s_names = " ".join([str(name) for name in self.names])
        return "{{LT{{{}}}{}{}{}}}".format(s_names, self.g1_fst.apted_tree(), self.g1_snd.apted_tree(), self.g2.apted_tree())


class GIf(GExp):
    """| GIf of Loc.t * glob_constr * (Name.t * glob_constr option) * glob_constr * glob_constr
    """
    def __init__(self, g1, m_name_and_ty, g2, g3):
        assert isinstance(g1, GExp)
        assert isinstance(m_name_and_ty[0], Name)
        assert m_name_and_ty[1] is None or isinstance(m_name_and_ty[1], GExp)
        assert isinstance(g2, GExp)
        assert isinstance(g3, GExp)
        super().__init__()
        self.g1 = g1
        self.m_name_and_ty = m_name_and_ty
        self.g2 = g2
        self.g3 = g3

    def __str__(self):
        return "(I {} {} {})".format(str(self.g1), str(self.g2), str(self.g3))

    def apted_tree(self):
        return "{{I{}{}{}}}".format(self.g1.apted_tree(), self.g2.apted_tree(), self.g3.apted_tree())


class GRec(GExp):
    """| GRec of Loc.t * fix_kind * Id.t array * glob_decl list array *
      glob_constr array * glob_constr array
    """
    def __init__(self, fix_kind, ids, gdeclss, gc_tys, gc_bods):
        # TODO(deh): ignoring fix_kind for now
        for ident in ids:
            assert isinstance(ident, str)
        for gdecls in gdeclss:
            for gdecl in gdecls:
                assert isinstance(gdecl, GlobDecl)
        for gc in gc_tys:
            assert isinstance(gc, GExp)
        for gc in gc_bods:
            assert isinstance(gc, GExp)
        super().__init__()
        self.fix_kind = fix_kind
        self.ids = ids
        self.gdeclss = gdeclss
        self.gc_tys = gc_tys
        self.gc_bods = gc_bods

    def __str__(self):
        s_ids = "({})".format(" ".join([str(ident) for ident in self.ids]))
        s_tys = "({})".format(" ".join([str(ty) for ty in self.gc_tys]))
        s_bods = "({})".format(" ".join([str(bod) for bod in self.gc_bods]))
        return "(R {} {} {})".format(s_ids, s_tys, s_bods)

    def apted_tree(self):
        s_ids = "".join([str(ident) for ident in self.ids])
        s_tys = "".join([ty.apted_tree() for ty in self.gc_tys])
        s_bods = "".join([bod.apted_tree() for bod in self.gc_bods])
        return "{{R{}{}{}}}".format(s_ids, s_tys, s_bods)


class GSort(GExp):
    """| GSort of Loc.t * glob_sort
    """
    def __init__(self, gsort):
        super().__init__()
        self.gsort = gsort

    def __str__(self):
        return "(S {})".format(str(self.gsort))

    def apted_tree(self):
        return "{{S{}}}".format(str(self))


class GHole(GExp):
    """| GHole of (Loc.t * Evar_kinds.t * intro_pattern_naming_expr * Genarg.glob_generic_argument option)
    """
    def __init__(self, ek, ipne, m_ga):
        super().__init__()
        self.ek = ek
        self.ipne = ipne
        self.m_ga = m_ga

    def __str__(self):
        return "(H {})".format(str(self.ek))

    def apted_tree(self):
        return "{{H{}}}".format(str(self))


class GCast(GExp):
    """| GCast of Loc.t * glob_constr * glob_constr cast_type
    """
    def __init__(self, g, g_cty):
        assert isinstance(g, GExp)
        assert isinstance(g_cty, CastType)
        super().__init__()
        self.g = g
        self.g_cty = g_cty

    def __str__(self):
        return "(T {} {})".format(str(self.g), str(self.g_cty))

    def apted_tree(self):
        return "{{T{}{}}}".format(self.g.apted_tree(), self.g_cty.apted_tree())


# -------------------------------------------------
# Other

COQGC = ['GRef', 'GVar', 'GEvar', 'GPatVar', 'GApp', 'GLambda', 'GProd', 'GLetIn', 'GCases',
         'GLetTuple', 'GIf', 'GRec', 'GSort', 'GHole', 'GCast']


COQGC_HIST = MyHist(COQGC)
