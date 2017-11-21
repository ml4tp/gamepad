from enum import Enum

from coq.ast import *
from lib.myutil
from lib.gensym import GenSym

"""
[Note]

Create embedding of AST into vector.

- Keep track of globals and locals separately
- Local names need to be shadowed appropriately
"""


# -------------------------------------------------
# Helper-classes

class Kind(Enum):
    TERM = 0
    TYPE = 1


class EmbedEnv(object):
    def __init__(self, rel_embed, var_embed, mv_embed,
                 ev_embed, fix_embed, cofix_embed):
        # Local embeddings
        self.rel_embed = rel_embed
        self.var_embed = var_embed
        self.mv_embed = mv_embed
        self.ev_embed = ev_embed
        self.fix_embed = fix_embed
        self.cofix_embed = cofix_embed

    def extend_rel(self, key, value):
        rel_embed = dict([(k, v) for k, v in self.rel_embed.items()])
        rel_embed[key] = value
        return EmbedEnv(rel_embed, self.var_embed, self.mv_embed,
                        self.ev_embed, self.fix_embed, self.cofix_embed)

    def extend_var(self, key, value):
        var_embed = dict([(k, v) for k, v in self.var_embed.items()])
        var_embed[key] = value
        return EmbedEnv(self.rel_embed, var_embed, self.mv_embed,
                        self.ev_embed, self.fix_embed, self.cofix_embed)

    def extend_mv(self, key, value):
        mv_embed = dict([(k, v) for k, v in self.mv_embed.items()])
        mv_embed[key] = value
        return EmbedEnv(self.rel_embed, self.var_embed, mv_embed,
                        self.ev_embed, self.fix_embed, self.cofix_embed)

    def extend_ev(self, key, value):
        ev_embed = dict([(k, v) for k, v in self.ev_embed.items()])
        ev_embed[key] = value
        return EmbedEnv(self.rel_embed, self.var_embed, self.mv_embed,
                        ev_embed, self.fix_embed, self.cofix_embed)

    def extend_fix(self, key, value):
        # TODO(deh): tie the knot?
        fix_embed = dict([(k, v) for k, v in self.fix_embed.items()])
        fix_embed[key] = value
        return EmbedEnv(self.rel_embed, self.var_embed, self.mv_embed,
                        self.ev_embed, fix_embed, self.cofix_embed)

    def extend_cofix(self, key, value):
        # TODO(deh): tie the knot?
        cofix_embed = dict([(k, v) for k, v in self.cofix_embed.items()])
        cofix_embed[key] = value
        return EmbedEnv(self.rel_embed, self.var_embed, self.mv_embed,
                        self.ev_embed, self.fix_embed, cofix_embed)


# -------------------------------------------------
# Embedding class

class EmbedCoqExp(object):
    def __init__(self, concr_ast):
        # Shared representation
        self.concr_ast = concr_ast

        # Global embeddings
        self.sort_embed = {}
        self.const_embed = {}
        self.ind_embed = {}
        self.construct_embed = {}

        # Keep track of shared embeddings
        self.embeddings = {}

    def _embedcon(self, key, embed_vec):
        self.embed[key] = embed_vec
        return embed_vec

    def _global_embed(self, key, table, embed_fn):
        if key in table:
            ev = table[key]
        else:
            ev = embed_fn(key)
            table[key] = ev
        return ev

    def _extend_sort(self, key, embed_fn):
        self._global_embed(key, self.sort_embed, embed_fn)

    def _extend_const(self, key, embed_fn):
        self._global_embed(key, self.const_embed, embed_fn)

    def _extend_ind(self, key, embed_fn):
        self._global_embed(key, self.ind_embed, embed_fn)

    def _extend_construct(self, key, embed_fn):
        self._global_embed(key, self.construct_embed, embed_fn)

    def _embed_ast(self, env, kind, c):
        key = c.tag
        if key in self.embeddings:
            return self.embeddings[key]

        if isinstance(c, RelExp):
            ev_idx = env.rel_embed[c.idx]
            return self._embedcon(key, self.embed_rel(ev_idx))
        elif isinstance(c, VarExp):
            ev_x = env.var_embed[c.x]
            return self._embedcon(key, self.embed_var(ev_x))
        elif isinstance(c, MetaExp):
            # NOTE(deh): this shouldn't exist in dataset
            ev_mv = env.mv_embed[c.mv]
            return self._embedcon(key, self.embed_meta(ev_mv))
        elif isinstance(c, EvarExp):
            ev_exk = env.ev_embed[c.exk]
            return self._embedcon(key, self.embed_evar(ev_exk, c.cs))
        elif isinstance(c, SortExp):
            ev_sort = self._extend_sort(c.sort, self.embed_sort_name)
            return self._embedcon(key, self.embed_sort(ev_sort))
        elif isinstance(c, CastExp):
            ev_c = self._embed_ast(env, Kind.TERM, c.c)
            ev_ty = self._embed_ast(env, Kind.TYPE, c.ty)
            return self._embedcon(key, self.embed_cast(ev_c, c.ck, ev_ty))
        elif isinstance(c, ProdExp):
            ev_ty1 = self._embed_ast(env, Kind.TYPE, c.ty1)
            ev_ty2 = self._embed_ast(env, Kind.TYPE, c.ty2)
            return self._embedcon(key, self.embed_prod(c.name, ev_ty1, ev_ty2))
        elif isinstance(c, LambdaExp):
            # TODO(deh): what to do with name?
            ev_ty = self._embed_ast(env, Kind.TERM, c.ty)
            ev_c = self._embed_ast(env.extend_var(c.name, ev_ty), Kind.TYPE, c.c)
            return self._embedcon(key, self.embed_lambda(c.name, ev_ty, ev_c))
        elif isinstance(c, LetInExp):
            # TODO(deh): what to do with name?
            ev_c1 = self._embed_ast(env, Kind.TERM, c.c1)
            ev_ty = self._embed_ast(env, Kind.TYPE, c.ty)
            ev_c2 = self._embed_ast(env.extend_var(c.name, ev_c1), Kind.TERM, c.c2)
            return self._embedcon(key, self.embed_letin(c.name, ev_c1, ev_ty, ev_c2))
        elif isinstance(c, AppExp):
            ev_c = self._embed_ast(env, Kind.TERM, c.c)
            ev_cs = self._embed_ast(env, Kind.TERM, c.cs)
            return self._embedcon(key, self.embed_app(ev_c, ev_cs))
        elif isinstance(c, ConstExp):
            ev_const = self._extend_const(c.const, self.embed_const_name)
            ev_ui = self.embed_ui(c.ui)
            return self._embedcon(key, self.embed_const(ev_const, ev_ui))
        elif isinstance(c, IndExp):
            ev_ind = self._extend_ind(c.ind, self.embed_ind_name)
            ev_ui = self.embed_ui(c.ui)
            return self._embedcon(key, self.embed_ind(ev_ind, ev_ui))
        elif isinstance(c, ConstructExp):
            ev_ind = self._extend_construct(c.ind, self.embed_conid_name)
            ev_conid = self.embed_conid_name((c.ind, c.conid))
            ev_ui = self.embed_ui(c.ui)
            return self._embedcon(key, self.embed_construct(ev_ind, ev_conid, ev_ui))
        elif isinstance(c, CaseExp):
            c.ci     # TODO(deh): case info?
            ev_ret = self._embed_ast(env, Kind.TERM, c.ret)
            ev_match = self._embed_ast(env, Kind.TERM, c.match)
            ev_cs = self._embed_asts(env, Kind.TERM, c.cs)
            return self._embedcon(self.embed_case(c.ci, ev_ret, ev_match, ev_cs))
        elif isinstance(c, FixExp):
            c.iarr   # TODO(deh): hmm?
            c.idx    # TODO(deh): hmm?
            ev_tys = []
            ev_cs = []
            for name, ty, body in zip(c.names, c.tys, c.cs):
                ev_tys += [self._embed_asts(env, Kind.TYPE, c.tys)]
                ev_c = self._embed_ast(env, Kind.TERM, c.cs)
                # TODO(deh): tie the knot appropriately
                self.fix_embed[name] = ev_c
                ev_cs += [ev_c]
            return self._embedcon(self.embed_fix(c.iarr, c.idx, c.names, ev_tys, ev_cs))
        elif isinstance(c, CoFixExp):
            c.idx    # TODO(deh): hmm?
            ev_tys = []
            ev_cs = []
            for name, ty, body in zip(c.names, c.tys, c.cs):
                ev_tys += [self._embed_asts(env, Kind.TYPE, c.tys)]
                ev_c = self._embed_ast(env, Kind.TERM, c.cs)
                # TODO(deh): tie the knot appropriately
                self.cofix_embed[name] = ev_c
                ev_cs += [ev_c]
            return self._embedcon(self.embed_cofix(c.idx, c.names, ev_tys, ev_cs))
        elif isinstance(c, ProjExp):
            c.proj   # TODO(deh): what to do with proj?
            ev = self._embed_ast(env, Kind.TERM, c.c)
            return self._embedcon(self.combine_proj(c.proj, ev))
        else:
            raise NameError("Kind {} not supported".format(c))

    def _embed_asts(self, env, kind, cs):
        return [self._embed_ast(env, kind, c) for c in cs]

    def embed_ast(self, c):
        return self._embed_ast(EmbedEnv({}, {}, {}, {}, {}, {}), Kind.TERM, c)

    def embed_rel(self, ev_idx):
        raise NotImplementedError

    def embed_var(self, ev_x):
        raise NotImplementedError

    def embed_meta(self, ev_mv):
        raise NotImplementedError        

    def embed_evar(self, ev_ev):
        raise NotImplementedError

    def embed_sort_name(self, sort):
        raise NotImplementedError

    def embed_sort(self, ev_sort):
        raise NotImplementedError

    def embed_cast(self, ev_c, ck, ev_ty):
        raise NotImplementedError

    def embed_prod(self, name, ev_ty1, ev_ty2):
        raise NotImplementedError

    def embed_lambda(self, name, ev_ty, ev_body):
        raise NotImplementedError

    def embed_letin(self, name, ev_c1, ev_ty, ev_c2):
        raise NotImplementedError

    def embed_app(self, ev_c, ev_cs):
        raise NotImplementedError

    def embed_const_name(self, const):
        raise NotImplementedError

    def embed_const(self, ev_const):
        raise NotImplementedError

    def embed_ind_name(self, ind):
        raise NotImplementedError

    def embed_ind(self, ev_ind, ev_ui):
        raise NotImplementedError

    def embed_conid_name(self, ind_and_conid):
        ind, conid = ind_and_conid
        raise NotImplementedError

    def embed_construct(self, ev_ind, ev_coind, ev_ui):
        raise NotImplementedError

    def embed_case(self, ci, ev_ret, ev_match, ev_cases):
        raise NotImplementedError

    def embed_fix(self, iarr, idx, names, ev_tys, ev_cs):
        raise NotImplementedError

    def embed_cofix(self, idx, names, ev_tys, ev_cs):
        raise NotImplementedError

    def embed_proj(self, proj, ev_c):
        raise NotImplementedError

    def embed_ui(self, ui):
        raise NotImplementedError

    def embed_uis(self, uis):
        return [self.embed_ui(ui) for ui in uis]
