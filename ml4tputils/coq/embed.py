from enum import Enum

from coq.ast import *
from lib.gensym import GenSym
from lib.myenv import MyEnv
from lib.myutil import ImplementMe

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
        self.conid_embed = {}
        self.evar_embed = {}

        self.fixbody_embed = {}   # For use in the body
        self.fix_embed = {}       # For use everywhere else

        # Keep track of shared embeddings
        self.embeddings = {}

    def embed_ast(self, env, c):
        return self._embed_ast(env, Kind.TERM, c)

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

    def _extend_conid(self, key, embed_fn):
        self._global_embed(key, self.conid_embed, embed_fn)

    def _extend_evar(self, key, embed_fn):
        self._global_embed(key, self.evar_embed, embed_fn)

    def _embed_ast(self, env, kind, c):
        key = c.tag
        if key in self.embeddings:
            return self.embeddings[key]

        if isinstance(c, RelExp):
            ev_idx = env.lookup_rel(c.idx)
            return self._embedcon(key, self.embed_rel(ev_idx))
        elif isinstance(c, VarExp):
            ev_x = env.lookup_id(c.x)
            return self._embedcon(key, self.embed_var(ev_x))
        elif isinstance(c, MetaExp):
            assert False, "NOTE(deh): MetaExp should never be in dataset"
        elif isinstance(c, EvarExp):
            ev_exk = self._extend_evar(c.exk)
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
            ev_x = self.local_var_init(c.ty)
            ev_ty = self._embed_ast(env, Kind.TERM, c.ty)
            ev_c = self._embed_ast(env.extend(c.name, ev_x),
                                   Kind.TYPE, c.c)
            return self._embedcon(key, self.embed_lambda(c.name, ev_ty, ev_c))
        elif isinstance(c, LetInExp):
            ev_c1 = self._embed_ast(env, Kind.TERM, c.c1)
            ev_ty = self._embed_ast(env, Kind.TYPE, c.ty)
            ev_c2 = self._embed_ast(env.extend(c.name, ev_c1),
                                    Kind.TERM, c.c2)
            return self._embedcon(key, self.embed_letin(c.name, ev_c1,
                                                        ev_ty, ev_c2))
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
            ev_ind = self._extend_ind(c.ind, self.embed_ind_name)
            ev_conid = self._extend_conid((c.ind, c.conid),
                                          self.embed_conid_name)
            ev_ui = self.embed_ui(c.ui)
            return self._embedcon(key, self.embed_construct(ev_ind, ev_conid,
                                                            ev_ui))
        elif isinstance(c, CaseExp):
            ev_ret = self._embed_ast(env, Kind.TERM, c.ret)
            ev_match = self._embed_ast(env, Kind.TERM, c.match)
            ev_cs = self._embed_asts(env, Kind.TERM, c.cs)
            return self._embedcon(self.embed_case(c.ci, ev_ret, ev_match,
                                                  ev_cs))
        elif isinstance(c, FixExp):
            # 1. Create initial embeddings
            for name in c.names:
                ev = self.embed_rec_name(name)
                self.fixbody_embed[name] = ev
                env = env.extend(name, ev)

            # 2. Use initial embeddings
            ev_tys = []
            ev_cs = []
            for ty, body in zip(c.tys, c.cs):
                ev_tys += [self._embed_asts(env, Kind.TYPE, c.tys)]
                ev_c = self._embed_ast(env, Kind.TERM, c.cs)
                # Tie the knot appropriately
                self.fix_embed[name] = ev_c
                ev_cs += [ev_c]
            return self._embedcon(self.embed_fix(c.iarr, c.idx, c.names,
                                                 ev_tys, ev_cs))
        elif isinstance(c, CoFixExp):
            # NOTE(deh): CoFixExp not in dataset
            raise NameError("NOTE(deh): CoFixExp not in dataset")
        elif isinstance(c, ProjExp):
            # NOTE(deh): MetaExp not in dataset
            ev = self._embed_ast(env, Kind.TERM, c.c)
            return self._embedcon(self.combine_proj(c.proj, ev))
        else:
            raise NameError("Kind {} not supported".format(c))

    def _embed_asts(self, env, kind, cs):
        return [self._embed_ast(env, kind, c) for c in cs]

    # -------------------------------------------
    # Global embedding initialization
    def embed_evar_name(self, exk):
        raise NotImplementedError

    def embed_const_name(self, const):
        raise NotImplementedError

    def embed_sort_name(self, sort):
        raise NotImplementedError

    def embed_ind_name(self, ind):
        raise NotImplementedError

    def embed_conid_name(self, ind_and_conid):
        ind, conid = ind_and_conid
        raise NotImplementedError

    def embed_rec_name(self, name):
        raise NotImplementedError

    # -------------------------------------------
    # Local embedding initialization
    def local_var_init(self, ty):
        raise NotImplementedError

    # -------------------------------------------
    # Combining embeddings
    def embed_rel(self, ev_idx):
        raise NotImplementedError

    def embed_var(self, ev_x):
        raise NotImplementedError

    def embed_evar(self, ev_ev):
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

    def embed_const(self, ev_const, ev_ui):
        raise NotImplementedError

    def embed_ind(self, ev_ind, ev_ui):
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

    # -------------------------------------------
    # Embed universes
    # NOTE(deh): can probably punt on this for now
    def embed_ui(self, ui):
        raise NotImplementedError

    def embed_uis(self, uis):
        return [self.embed_ui(ui) for ui in uis]


class EmbedCoqTacTr(object):
    def __init__(self, tactr):
        self.tactr = tactr
        self.ece = EmbedCoqExp(tactr.decoder.concr_ast)

        # Sharing
        self.ctxid_embeds = {}
        self.goal_embeds = {}

    def embed(self):
        bfs = tactr.bfs_traverse()
        acc = []
        for node in bfs:
            if node[0] == 'OPEN':
                _, gid, _, _, ctx_ids, goal_idx, edge = node
                evs = self.embed_ctx(ctx_ids)
                ev = self.embed_goal(goal_idx)
                acc += [(evs, ev)]
            else:
                # TODO(deh): what to do on terminal nodes?
                _, gid, edge = node
        return acc

    def embed_ctx(self, ctx_idents):
        evs = []
        for ident in ctx_idents:
            ev = self.embed_ctx_ident(ident)
            evs += [ev]
        return evs

    def embed_ctx_ident(self, ident):
        if ident in self.ctxid_embeds:
            return self.ctxid_embeds[ident]
        else:
            c = self.tactr.decoder.decode_exp_by_ctxid(ident)
            ev = self.ece.embed_exp(c)
            self.ctxid_embeds[ident] = ev
            return ev

    def embed_goal(self, goal_idx):
        if goal_idx in self.goal_embeds:
            return self.goal_embeds[goal_idx]
        else:
            c = self.tactr.decoder.decode_exp_by_key(goal_idx)
            ev = self.ece.embed_exp(c)
            self.goal_embeds[goal_idx] = ev
            return ev


"""
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
"""