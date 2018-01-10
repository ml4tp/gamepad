import gc
import os
import psutil
import sys
from time import time

import torch
import torch.autograd as autograd
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim

from coq.ast import *
from coq.decode import DecodeCoqExp
from lib.myenv import MyEnv
from lib.myutil import NotFound

from coq.util import SizeCoqExp

from ml.utils import ResultLogger

import pytorch_tools.torchfold as ptf


"""
[Note]

Version that uses torchfold
1. Embed Coq tactic trees into R^D vectors
2. Model uses embeddings to obtain prediction of:
    close, medium, far
"""


# -------------------------------------------------
# Helper

def ast_embed(folder, xs, init):
    hidden = init
    for i, x in enumerate(xs):
        #print("GRU Embed ",i, x.shape)
        hidden = folder.add('ast_cell_f', x, hidden) #cell(x.view(1, -1, 128), hidden)
    #print("hidden shape", hidden.shape)
    return hidden

def ctx_embed(xs, cell, init):
    hidden = init
    for i, x in enumerate(xs):
        print("GRU Embed ",i, x.shape)
        hidden = cell(x.view(-1,128), hidden) #cell(x.view(1, -1, 128), hidden)
    print("hidden shape", hidden.shape)
    return hidden

# -------------------------------------------------
# Fold over tactic state

class TacStFolder(object):
    def __init__(self, model, tactr):
        self.model = model    # Only used to access embeddings
        self.tactr = tactr    # Corresponding tactic tree

        # Folding state
        self.folder = ptf.Fold()
        self.folded = {}

    def apply(self, all_logits, all_targets):
        """Call after folding entire tactic state to force computation"""
        return self.folder.apply(self.model, [all_logits, all_targets])

    def reset(self):
        """Reset folding state"""
        self.folder = ptf.Fold()
        self.folded = {}

    # -------------------------------------------
    # Tactic state folding

    def fold_tacst(self, tacst):
        """Top-level fold function"""
        gid, ctx, concl_idx, tac = tacst
        env, foldeds = self.fold_ctx(gid, ctx)
        folded = self.fold_concl(gid, env, concl_idx)
        return self.folder.add('logits', folded, *foldeds)

    def fold_ctx(self, gid, ctx):
        foldeds = []
        env = MyEnv()
        for ident, typ_idx in ctx:
            folded = self.fold_ctx_ident(gid, env, typ_idx)
            env = env.extend(Name(ident), folded)
            foldeds += [folded]
        return env, foldeds

    def fold_ctx_ident(self, gid, env, typ_idx):
        # NOTE(deh): Do not need context sharing because of AST sharing
        c = self.tactr.decoder.decode_exp_by_key(typ_idx)
        return self.fold_ast(env, c)

    def fold_concl(self, gid, env, concl_idx):
        # NOTE(deh): Do not need conclusion sharing because of AST sharing
        c = self.tactr.decoder.decode_exp_by_key(concl_idx)
        return self.fold_ast(env, c)

    # -------------------------------------------
    # AST folding

    def fold_ast(self, env, c):
        return self._fold_ast(env, Kind.TERM, c)

    def _fold(self, key, args):
        # for i,arg in enumerate(args):
        #     print(i, arg.shape)

        folder = self.model.ast_emb_func(self.folder, args) #self.folder.add('coq_exp', *args)
        self.folded[key] = folder
        return folder

    def _fold_ast(self, env, kind, c):
        key = c.tag
        if key in self.folded:
            return self.folded[key]

        if isinstance(c, RelExp):
            # NOTE(deh): DeBruinj indicides start at 1 ...
            ev_idx = env.lookup_rel(c.idx - 1)
            return self._fold(key, [self.model.rel, ev_idx])
        elif isinstance(c, VarExp):
            ev_x = env.lookup_id(Name(c.x))
            return self._fold(key, [self.model.var, ev_x])
        elif isinstance(c, MetaExp):
            assert False, "NOTE(deh): MetaExp should never be in dataset"
        elif isinstance(c, EvarExp):
            ev_exk = self.fold_evar_name(c.exk)
            # NOTE(deh): pruposely leaving out cs
            # ev_cs = self._fold_asts(env, Kind.TYPE, c.cs)
            return self._fold(key, [self.model.evar, ev_exk])
        elif isinstance(c, SortExp):
            ev_sort = self.fold_sort_name(c.sort)
            return self._fold(key, [self.model.sort, ev_sort])
        elif isinstance(c, CastExp):
            ev_c = self._fold_ast(env, Kind.TERM, c.c)
            ev_ty = self._fold_ast(env, Kind.TYPE, c.ty)
            return self._fold(key, [self.model.cast, ev_c, ev_ty])
        elif isinstance(c, ProdExp):
            ev_x = self.fold_local_var(c.ty1)
            ev_ty1 = self._fold_ast(env, Kind.TYPE, c.ty1)
            ev_ty2 = self._fold_ast(env.extend(c.name, ev_x), Kind.TYPE, c.ty2)
            return self._fold(key, [self.model.prod, ev_ty1, ev_ty2])
        elif isinstance(c, LambdaExp):
            ev_x = self.fold_local_var(c.ty)
            ev_ty = self._fold_ast(env, Kind.TERM, c.ty)
            ev_c = self._fold_ast(env.extend(c.name, ev_x), Kind.TYPE, c.c)
            return self._fold(key, [self.model.lam, ev_ty, ev_c])
        elif isinstance(c, LetInExp):
            ev_c1 = self._fold_ast(env, Kind.TERM, c.c1)
            ev_ty = self._fold_ast(env, Kind.TYPE, c.ty)
            ev_c2 = self._fold_ast(env.extend(c.name, ev_c1), Kind.TERM, c.c2)
            return self._fold(key, [self.model.letin, ev_c1, ev_ty, ev_c2])
        elif isinstance(c, AppExp):
            ev_c = self._fold_ast(env, Kind.TERM, c.c)
            ev_cs = self._fold_asts(env, Kind.TERM, c.cs)
            return self._fold(key, [self.model.app, ev_c, *ev_cs])
        elif isinstance(c, ConstExp):
            ev_const = self.fold_const_name(c.const)
            # NOTE(deh): leaving out universe instances on purpose
            # ev_ui = self.fold_ui(c.ui)
            return self._fold(key, [self.model.const, ev_const])
        elif isinstance(c, IndExp):
            ev_ind = self.fold_ind_name(c.ind)
            # NOTE(deh): leaving out universe instances on purpose
            # ev_ui = self.fold_ui(c.ui)
            return self._fold(key, [self.model.ind, ev_ind])
        elif isinstance(c, ConstructExp):
            ev_ind = self.fold_ind_name(c.ind)
            ev_conid = self.fold_conid_name((c.ind, c.conid))
            # NOTE(deh): leaving out universe instances on purpose
            # ev_ui = self.fold_ui(c.ui)
            return self._fold(key, [self.model.construct, ev_ind, ev_conid])
        elif isinstance(c, CaseExp):
            ev_ret = self._fold_ast(env, Kind.TERM, c.ret)
            ev_match = self._fold_ast(env, Kind.TERM, c.match)
            ev_cases = self._fold_asts(env, Kind.TERM, c.cases)
            return self._fold(key, [self.model.case, ev_ret, ev_match, *ev_cases])
        elif isinstance(c, FixExp):
            # 1. Create initial embeddings
            for name in c.names:
                ev = self.fold_fix_name(name)
                # self.fixbody_embed[name] = ev
                env = env.extend(name, ev)

            # 2. Use initial embeddings
            ev_tys = []
            ev_cs = []
            for ty, body in zip(c.tys, c.cs):
                ev_tys += [self._fold_ast(env, Kind.TYPE, ty)]
                ev_c = self._fold_ast(env, Kind.TERM, body)
                # TODO(deh): wtf?
                # Tie the knot appropriately
                # self.fix_embed[name] = ev_c
                ev_cs += [ev_c]
            return self._fold(key, [self.model.fix, *ev_tys, *ev_cs])
        elif isinstance(c, CoFixExp):
            # NOTE(deh): CoFixExp not in dataset
            raise NameError("NOTE(deh): CoFixExp not in dataset")
        elif isinstance(c, ProjExp):
            # NOTE(deh): ProjExp not in dataset
            raise NameError("NOTE(deh): ProjExp not in dataset")
            # ev = self._fold_ast(env, Kind.TERM, c.c)
            # return self._fold(key, [self.model.proj, ev])
        else:
            raise NameError("Kind {} not supported".format(c))

    def _fold_asts(self, env, kind, cs):
        # TODO(deh): may need to fix this for fold to work
        return [self._fold_ast(env, kind, c) for c in cs]

    # -------------------------------------------
    # Global constant folding

    def fold_evar_name(self, exk):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.model.evar_to_idx[exk]])
        return self.folder.add('evar_embed_f', (autograd.Variable(lookup_tensor)))

    def fold_const_name(self, const):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.model.const_to_idx[const]])
        return self.folder.add('const_embed_f', (autograd.Variable(lookup_tensor)))

    def fold_sort_name(self, sort):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.model.sort_to_idx[sort]])
        return self.folder.add('sort_embed_f', (autograd.Variable(lookup_tensor)))

    def fold_ind_name(self, ind):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.model.ind_to_idx[ind.mutind]])
        return self.folder.add('ind_embed_f', (autograd.Variable(lookup_tensor)))

    def fold_conid_name(self, ind_and_conid):
        """Override Me"""
        ind, conid = ind_and_conid
        lookup_tensor = torch.LongTensor([self.model.conid_to_idx[(ind.mutind, conid)]])
        return self.folder.add('conid_embed_f', (autograd.Variable(lookup_tensor)))

    def fold_fix_name(self, name):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.model.fix_to_idx[name]])
        return self.folder.add('fix_embed_f', (autograd.Variable(lookup_tensor)))

    # -------------------------------------------
    # Local variable folding

    def fold_local_var(self, ty):
        """Override Me"""
        return self.folder.add('identity', autograd.Variable(torch.randn(1,self.model.D), requires_grad=False))


# -------------------------------------------------
# Model

class PosEvalModel(nn.Module):
    def __init__(self, sort_to_idx, const_to_idx, ind_to_idx,
                 conid_to_idx, evar_to_idx, fix_to_idx,
                 D=128, state=128, outsize=3):
        super().__init__()

        # Dimensions
        self.D = D            # Dimension of embeddings
        self.state = state    # Dimension of GRU state

        # tabs = [sort_to_idx, const_to_idx, ind_to_idx, conid_to_idx, evar_to_idx, fix_to_idx, fix_to_idx]
        # embed_size = sum([len(tab) for tab in tabs])
        # shift = 0
        # self.shifts = {}
        # for tab in tabs:
        #     shift += len(tab)
        #     self.shifts[tab]

        #self.embed_table = nn.Embedding(embed_size, D)

        # Embeddings for constants
        self.sort_to_idx = sort_to_idx
        self.sort_embed = nn.Embedding(len(sort_to_idx), D)
        self.const_to_idx = const_to_idx
        self.const_embed = nn.Embedding(len(const_to_idx), D)
        self.ind_to_idx = ind_to_idx
        self.ind_embed = nn.Embedding(len(ind_to_idx), D)
        self.conid_to_idx = conid_to_idx
        self.conid_embed = nn.Embedding(len(conid_to_idx), D)
        self.evar_to_idx = evar_to_idx
        self.evar_embed = nn.Embedding(len(evar_to_idx), D)
        self.fix_to_idx = fix_to_idx
        self.fix_embed = nn.Embedding(len(fix_to_idx), D)
        self.fixbody_embed = nn.Embedding(len(fix_to_idx), D)

        # Embeddings for Gallina AST
        self.ast_cell_init_state = autograd.Variable(torch.randn((1, self.state))) #TODO(prafulla): Change this?
        self.ast_cell = nn.GRUCell(state, state)
        self.ast_emb_func = lambda folder, xs: ast_embed(folder, xs, self.ast_cell_init_state)
        for attr in ["rel", "var", "evar", "sort", "cast", "prod",
                     "lam", "letin", "app", "const", "ind", "construct",
                     "case", "fix", "cofix", "proj1"]:
            self.__setattr__(attr, autograd.Variable(torch.randn(1, self.state)))

        # Embeddings for Tactic State (ctx, goal)
        self.ctx_cell_init_state = autograd.Variable(torch.randn((1, self.state))) #TODO(prafulla): Change this?
        self.ctx_cell = nn.GRUCell(state, state)
        self.proj = nn.Linear(state, state - 1)
        self.final = nn.Linear(state, outsize)
        self.ctx_emb_func = lambda xs: ctx_embed(xs, self.ctx_cell, self.ctx_cell_init_state)

    def identity(self, x):
        return x

    def sort_embed_f(self, id):
        return self.sort_embed(id)

    def const_embed_f(self, id):
        return self.const_embed(id)

    def ind_embed_f(self, id):
        return self.ind_embed(id)

    def conid_embed_f(self, id):
        return self.conid_embed(id)

    def evar_embed_f(self, id):
        return self.evar_embed(id)

    def fix_embed_f(self, id):
        return self.fix_embed(id)

    def fixbody_embed_f(self, id):
        return self.fixbody_embed(id)

    def ast_cell_f(self, x, hidden):
        hidden = self.ast_cell(x, hidden)
        return hidden

    def coq_exp(self, *args):
        return self.emb_func(args)

    def logits(self, *tacst_evs):
        # Adding 1 to conclusion and 0 to expressions
        # ctx_mask = torch.zeros(len(tacst_evs), 1, 1)
        # ctx_mask[0][0][0] = 1.0
        # x = torch.cat(list(tacst_evs), 0)
        # x = self.proj(x)
        # x = torch.cat([x, autograd.Variable(ctx_mask, requires_grad=False)], dim=-1)
        # xs = torch.split(x, 1)
        xs = tacst_evs
        # Run GRU on tacst
        x = self.ctx_emb_func(xs)

        # Final layer for logits
        x = self.final(x)
        print("Output shape", x.shape)
        return x.view(1, -1)
