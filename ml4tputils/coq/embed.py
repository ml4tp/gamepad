from enum import Enum

from coq.ast import *
from lib.myutil
from lib.gensym import GenSym

"""
[Note]

Create embedding of AST into vector.
"""


# -------------------------------------------------
# Helper-classes

class Kind(Enum):
    TERM = 0
    TYPE = 1


# -------------------------------------------------
# Embedding class

class TokenCoqExp(object):
    def __init__(self, concr_ast):
        self.sort_toks = set()
        self.const_toks = set()
        self.ind_toks = set()
        self.construct_toks = set()
        self.fix_toks = set()
        self.cofix_toks = set()
        self.proj_toks = set()

    def token_ast(self, c):
        if isinstance(c, RelExp):
            # NOTE(deh): c.idx
            pass
        elif isinstance(c, VarExp):
            # NOTE(deh): c.x?
            pass
        elif isinstance(c, MetaExp):
            # NOTE(deh): c.mv?
            pass
        elif isinstance(c, EvarExp):
            # NOTE(deh): c.exk?
            self.token_asts(c.cs)
        elif isinstance(c, SortExp):
            self.sort_toks.add(c.sort)
        elif isinstance(c, CastExp):
            self.token_ast(cc)
            self.token_ast(c.ty)
        elif isinstance(c, ProdExp):
            # NOTE(deh): name?
            self.token_ast(c.ty1)
            self.token_ast(c.ty2)
        elif isinstance(c, LambdaExp):
            # NOTE(deh): name?
            self.token_ast(c.ty)
            self.token_ast(c.c)
        elif isinstance(c, LetInExp):
            # NOTE(deh): name?
            self.token_ast(c.c1)
            self.token_ast(c.ty)
            self.token_ast(c.c2)
        elif isinstance(c, AppExp):
            self.token_ast(c.c)
            self.token_asts(c.cs)
        elif isinstance(c, ConstExp):
            self.const_toks.add(c.const)
        elif isinstance(c, IndExp):
            self.ind_toks.add(c.ind)
        elif isinstance(c, ConstructExp):
            self.ind_toks.add(c.ind)
            self.construct_toks.add((c.ind, c.conid))
        elif isinstance(c, CaseExp):
            self.ind_toks.add(c.ci.ind)
            self.token_ast(c.ret)
            self.token_ast(c.match)
            self.token_asts(c.cases)
        elif isinstance(c, FixExp):
            self.fix_toks.add(c.names)
            self.token_asts(c.tys)
            self.token_asts(c.cs)
        elif isinstance(c, CoFixExp):
            self.cofix_toks.add(c.names)
            self.token_asts(c.tys)
            self.token_asts(c.cs)
        elif isinstance(c, ProjExp):
            self.proj_toks.add(c.proj)
            self.token_ast(c.c)
        else:
            raise NameError("Kind {} not supported".format(c))

    def embed_asts(self, kind, cs):
        return [self.embed_ast(kind, c) for c in cs]



class EmbedCoqExp(object):
    def __init__(self, concr_ast):
        self.concr_ast = concr_ast
        self.embeddings = {}

        self.gs_const = GenSym()
        self.gs_ind = GenSym()
        self.gs_construct = GenSym()
        self.gs_ui = GenSym()

        self.rel_embed = {}
        self.var_embed = {}
        self.mv_embed = {}
        self.ev_embed = {}
        self.sort_embed = {}
        self.const_embed = {}

    def _embedcon(self, key, embed_vec):
        self.embed[key] = embed_vec
        return embed_vec

    def _econs(self, key, table, embed_fn):
        if key in table:
            ev = table[key]
        else:
            ev = embed_fn(key)
            table[key] = ev
        return ev

    def embed_ast(self, kind, c):
        key = c.tag
        if key in self.embeddings:
            return self.embeddings[key]

        if isinstance(c, RelExp):
            ev_idx = self._econs(c.idx, self.rel_embed, self.embed_relidx)
            return self._embedcon(key, ev_idx)
        elif isinstance(c, VarExp):
            ev_x = self._econs(c.x, self.var_embed, self.embed_var)
            return self._embedcon(key, ev_x)
        elif isinstance(c, MetaExp):
            # TODO(deh): actually these probably shouldn't exist?
            ev_mv = self._econs(c.mv, self.mv_embed, self.embed_metavar)
            return self._embedcon(key, ev_mv)
        elif isinstance(c, EvarExp):
            ev_exk = self._econs(c.exk, self.ev_embed, self.embed_evar)
            ev_evs = self.embed_asts(c.cs)
            return self._embedcon(key, self.combine_evar(ev_exk, ev_evs))
        elif isinstance(c, SortExp):
            ev_sort = self._econs(c.sort, self.sort_embed, self.embed_sort)
            return self._embedcon(key, ev_sort)
        elif isinstance(c, CastExp):
            # TODO(deh): embed cast kind?
            ev_c = self.embed_ast(Kind.TERM, c.c)
            ev_ty = self.embed_ast(Kind.TYPE, c.ty)
            return self._embedcon(key, self.combine_cast(ev_c, c.ck, ev_ty))
        elif isinstance(c, ProdExp):
            ev_ty1 = self.embed_ast(Kind.TYPE, c.ty1)
            ev_ty2 = self.embed_ast(Kind.TYPE, c.ty2)
            return self._embedcon(key, self.combine_prod(ev_c, ev_ty))
        elif isinstance(c, LambdaExp):
            # TODO(deh): what to do with name?
            ev_ty = self.embed_ast(Kind.TERM, c.ty)
            ev_c = self.embed_ast(Kind.TYPE, c.c)
            return self._embedcon(key, self.combine_lam(c.name, ev_ty, ev_c))
        elif isinstance(c, LetInExp):
            # TODO(deh): what to do with name?
            ev_c1 = self.embed_ast(Kind.TERM, c.c1)
            ev_ty = self.embed_ast(Kind.TYPE, c.ty)
            ev_c2 = self.embed_ast(Kind.TERM, c.c2)
            return self._embedcon(key, self.combine_letin(c.name, ev_c1, ev_ty, ev_c2))
        elif isinstance(c, AppExp):
            ev_c = self.embed_ast(Kind.TERM, c.c)
            ev_cs = self.embed_ast(Kind.TERM, c.cs)
            return self._embedcon(key, self.combine_app(ev_c, ev_cs))
        elif isinstance(c, ConstExp):
            ev_const = self._econs(c.const, self.const_embed, self.embed_const)
            ev_ui = self.embed_ui(c.ui)
            return self._embedcon(key, self.combine_const(ev_const, ev_ui))
        elif isinstance(c, IndExp):
            # TODO(deh): HMM?
            ev_ind = self.embed_ind(c.ind)
            ev_ui = self.embed_ui(c.ui)
            return self._embedcon(key, self.combine_ind(ev_ind, ev_ui))
        elif isinstance(c, ConstructExp):
            # TODO(deh): HMM?
            ev_ind = self.embed_ind(c.ind)
            ev_conid = self.embed_construct(c.ind, c.conid)
            ev_ui = self.embed_ui(c.ui)
            return self._embedcon(key, self.combine_construct(ev_ind, ev_conid, ev_ui))
        elif isinstance(c, CaseExp):
            c.ci     # TODO(deh): case info?
            ev_ret = self.embed_ast(Kind.TERM, c.ret)
            ev_match = self.embed_ast(Kind.TERM, c.match)
            ev_cs = self.embed_asts(Kind.TERM, c.cs)
            return self._embedcon(self.combine_case(ev_ret, ev_match, ev_cs))
        elif isinstance(c, FixExp):
            c.iarr   # TODO(deh): hmm?
            c.idx    # TODO(deh): hmm?
            c.names  # TODO(deh): hmm?
            ev_tys = self.embed_asts(Kind.TYPE, c.tys)
            ev_cs = self.embed_ast(Kind.TERM, c.cs)
            return self._embedcon(self.combine_fix(c.iarr, c.idx, c.names, ev_tys, ev_cs))
        elif isinstance(c, CoFixExp):
            c.idx    # TODO(deh): hmm?
            c.names  # TODO(deh): hmm?
            ev_tys = self.embed_asts(Kind.TYPE, c.tys)
            ev_cs = self.embed_ast(Kind.TERM, c.cs)
            return self._embedcon(self.combine_cofix(c.idx, c.names, ev_tys, ev_cs))
        elif isinstance(c, ProjExp):
            c.proj   # TODO(deh): hmm?
            ev = self.embed_ast(Kind.TERM, c.c)
            return self._embedcon(self.combine_proj(c.proj, ev))
        else:
            raise NameError("Kind {} not supported".format(c))

    def embed_asts(self, kind, cs):
        return [self.embed_ast(kind, c) for c in cs]

    def embed_relidx(self, relidx):
        raise NotImplementedError

    def embed_var(self, x):
        raise NotImplementedError

    def embed_metavar(self, mv):
        raise NotImplementedError        

    def embed_evar(self, ev):
        raise NotImplementedError

    def embed_const_name(self, name):
        raise NotImplementedError

    def embed_sort(self, sort):
        raise NotImplementedError

    def embed_ui(self, ui):
        raise NotImplementedError

    def embed_uis(self, uis):
        return [self.embed_ui(ui) for ui in uis]

    def embed_ind(self, ind):
        raise NotImplementedError

    def embed_construct(self, ind, coind):
        raise NotImplementedError

    def combine_evar(self, ev_exk, ev_cs):
        raise NotImplementedError

    def combine_cast(self, ev_c, ck, ev_ty):
        raise NotImplementedError

    def combine_prod(self, ev_ty1, ev_ty2):
        raise NotImplementedError

    def combine_lam(self, name, ev_ty, ev_body):
        raise NotImplementedError

    def combine_letin(self, name, ev_c1, ev_ty, ev_c2):
        raise NotImplementedError

    def combine_app(self, ev_c, ev_cs):
        raise NotImplementedError

    def combine_ind(self, ev_ind, ev_ui):
        raise NotImplementedError

    def combine_construct(self, ev_ind, ev_conid, ev_ui):
        raise NotImplementedError

    def combine_fix(self, iarr, idx, names, ev_tys, ev_cs):
        raise NotImplementedError

    def combine_cofix(self, idx, names, ev_tys, ev_cs):
        raise NotImplementedError

    def combine_proj(self, name, ev):
        raise NotImplementedError
