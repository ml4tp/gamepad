from enum import Enum

from coq.ast import *
from lib.myutil

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

class EmbedCoqExp(object):
    def __init__(self, concr_ast):
        self.concr_ast = concr_ast
        self.embeddings = {}

        self.gs_const = GenSym()
        self.gs_ind = GenSym()
        self.gs_construct = GenSym()
        self.gs_ui = GenSym()

    def _embedcon(self, key, embed_vec):
        self.embed[key] = embed_vec
        return embed_vec

    def embed_ast(self, kind, c):
        key = c.tag
        if key in self.embeddings:
            return self.embeddings[key]

        if isinstance(c, RelExp):
            ev_idx = self.embed_relidx(c.idx)
            return self._embedcon(key, ev_idx)
        elif isinstance(c, VarExp):
            ev_x = self.embed_var(c.x)
            return self._embedcon(key, ev_x)
        elif isinstance(c, MetaExp):
            # TODO(deh): actually these probably shouldn't exist?
            ev_mv = self.embed_metavar(c.mv)
            return self._embedcon(key, ev_mv)
        elif isinstance(c, EvarExp):
            ev_evs = self.embed_evar(c.cs)
            return self._embedcon(key, ev_evs)
        elif isinstance(c, SortExp):
            ev_sort = self.embed_sort(c.sort)
            return self._embedcon(key, ev_sort)
        elif isinstance(c, CastExp):
            # TODO(deh): embed cast kind?
            # TODO(deh): how to combine?
            ev_c = self.embed_ast(Kind.TERM, c.c)
            ev_ty = self.embed_ast(Kind.TYPE, c.ty)
            return self._embedcon(self.combine_cast(ev_c, c.ck, ev_ty))
        elif isinstance(c, ProdExp):
            # TODO(deh): how to combine?
            ev_ty1 = self.embed_ast(Kind.TYPE, c.ty1)
            ev_ty2 = self.embed_ast(Kind.TYPE, c.ty2)
            return self._embedcon(self.combine_prod(ev_c, ev_ty))
        elif isinstance(c, LambdaExp):
            # TODO(deh): use name?
            ev_ty = self.embed_ast(Kind.TERM, c.ty)
            ev_c = self.embed_ast(Kind.TYPE, c.c)
            return self._embedcon(self.combine_lam(c.name, ev_ty, ev_c))
        elif isinstance(c, LetInExp):
            # TODO(deh): how to combine?
            ev_c1 = self.embed_ast(Kind.TERM, c.c1)
            ev_ty = self.embed_ast(Kind.TYPE, c.ty)
            ev_c2 = self.embed_ast(Kind.TERM, c.c2)
            return self._embedcon(self.combine_letin(c.name, ev_c1, ev_ty, ev_c2))
        elif isinstance(c, AppExp):
            # TODO(deh): how to combine?
            ev_c = self.embed_ast(Kind.TERM, c.c)
            ev_cs = self.embed_ast(Kind.TERM, c.cs)
            return self._embedcon(self.combine_app(ev_c, ev_cs))
        elif isinstance(c, ConstExp):
            # TODO(deh): how to embed constants?
            # TODO(deh): how to embed universe instances?
            # TODO(deh): how to combine?
            c.const
            c.ui
            pass
        elif isinstance(c, IndExp):
            # TODO(deh): HMM?
            return self._embedcon(key, 1)
        elif isinstance(c, ConstructExp):
            # TODO(deh): HMM?
            return self._embedcon(key, 1)
        elif isinstance(c, CaseExp):
            # TODO(deh): how to combine?
            ev_c1 = self.embed_ast(Kind.TERM, c.c1)
            ev_c2 = self.embed_ast(Kind.TERM, c.c2)
            ev_cs = self.embed_asts(Kind.TERM, c.cs)
            pass
        elif isinstance(c, FixExp):
            ev_tys = self.embed_asts(Kind.TYPE, c.tys)
            ev_cs = self.embed_ast(Kind.TERM, c.cs)
            pass
        elif isinstance(c, CoFixExp):
            ev_tys = self.embed_asts(Kind.TYPE, c.tys)
            ev_cs = self.embed_ast(Kind.TERM, c.cs)
            pass
        elif isinstance(c, ProjExp):
            c.name
            ev = self.embed_ast(Kind.TERM, c.c)
            pass
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

    def combine_cast(self, ev_c, ck, ev_ty):
        raise NotImplementedError

    def combine_prod(self, ev_ty1, ev_ty2):
        raise NotImplementedError

    def combine_lam(self, name, ev_ty, ev_body):
        raise NotImplementedError

    def combine_letin(self, name, ev_c1, ev_ty, ev_c2):
        raise NotImplementedError

