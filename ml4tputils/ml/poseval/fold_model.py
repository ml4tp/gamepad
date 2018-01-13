import gc
import os
import psutil
import sys
from time import time

import torch.cuda
if torch.cuda.is_available():
    import torch.cuda as t
else:
    import torch as t
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

import ml.torchfold as ptf


"""
[Note]

Version that uses torchfold
1. Embed Coq tactic trees into R^D vectors
2. Model uses embeddings to obtain prediction of:
    close, medium, far
"""

# -------------------------------------------------
# Helper

def ast_embed(folder, xs, init, ln):
    hidden = init
    for i, x in enumerate(xs):
        #print("GRU Embed ",i, x.shape)
        hidden = folder.add('ast_cell_f', x, hidden) #cell(x.view(1, -1, 128), hidden)
    #print("hidden shape", hidden.shape)
    if ln:
        #print("using ln")
        hidden = folder.add('ln_f', hidden)
    return hidden

def ctx_embed(folder, xs, init):
    hidden = folder.add('ctx_identity', init)
    for i, x in enumerate(xs):
        #print("GRU Embed ",i, x.shape)
        hidden = folder.add('ctx_cell_f', x, hidden) #cell(x.view(1, -1, 128), hidden)
    #print("hidden shape", hidden.shape)
    return hidden

# -------------------------------------------------
# Fold over anything
class Folder(object):
    def __init__(self, model, foldy, cuda):
        # Folding state
        self.model = model
        self.foldy = foldy
        self.cuda = cuda
        self.max_batch_ops = {}
        self.max_batch_ops['embed_lookup_f'] = 128
        self.max_batch_ops['ast_cell_f'] = 32
        self.max_batch_ops['ctx_cell_f'] = 32
        self.max_batch_ops['final_f'] = 32
        self.reset()

    def reset(self):
        """Reset folding state"""
        if self.foldy:
            #print("Folding")
            self._folder = ptf.Fold(max_batch_ops = self.max_batch_ops)
        else:
            #print("Not folding")
            self._folder = ptf.Unfold(self.model)
        if self.cuda:
            self._folder.cuda()

    def apply(self, *args):
        """Call after folding entire tactic state to force computation"""
        return self._folder.apply(self.model, args)

    def add(self, op, *args):
        return self._folder.add(op, *args)

    def __str__(self):
        return str(self._folder)

# Fold over tactic state

class TacStFolder(object):
    def __init__(self, model, tactr, folder):
        self.model = model    # Only used to access embeddings
        self.tactr = tactr    # Corresponding tactic tree

        self.folder = folder
        self.folded = {}

    def reset(self):
        self.folded = {}
    # -------------------------------------------
    # Tactic state folding

    def fold_tacst(self, tacst):
        """Top-level fold function"""
        gid, ctx, concl_idx, tac = tacst
        env, foldeds = self.fold_ctx(gid, ctx)
        folded = self.fold_concl(gid, env, concl_idx)
        return self.model.pred(self.folder, folded, *foldeds)

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

        fold = self.model.ast_emb_func(self.folder, args) #self.folder.add('coq_exp', *args)
        self.folded[key] = fold
        return fold

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
    def lookup(self, lt):
        return self.folder.add('embed_lookup_f', autograd.Variable(t.LongTensor([lt])))

    def fold_evar_name(self, exk):
        """Override Me"""
        id = self.model.fix_id('evar', self.model.evar_to_idx[exk])
        return self.lookup(id)

    def fold_const_name(self, const):
        """Override Me"""
        id = self.model.fix_id('const', self.model.const_to_idx[const])
        return self.lookup(id)

    def fold_sort_name(self, sort):
        """Override Me"""
        id = self.model.fix_id('sort', self.model.sort_to_idx[sort])
        return self.lookup(id)

    def fold_ind_name(self, ind):
        """Override Me"""
        id = self.model.fix_id('ind', self.model.ind_to_idx[ind.mutind])
        return self.lookup(id)

    def fold_conid_name(self, ind_and_conid):
        """Override Me"""
        ind, conid = ind_and_conid
        id = self.model.fix_id('conid', self.model.conid_to_idx[(ind.mutind, conid)])
        return self.lookup(id)

    def fold_fix_name(self, name):
        """Override Me"""
        id = self.model.fix_id('fix', self.model.fix_to_idx[name])
        return self.lookup(id)

    # -------------------------------------------
    # Local variable folding

    def fold_local_var(self, ty):
        """Override Me"""
        return self.folder.add('var_identity', autograd.Variable(randn(1,self.model.D), requires_grad=False))


def randn(*shape):
    return t.FloatTensor(torch.randn(*shape))

def ones(*shape):
    return t.FloatTensor(torch.ones(*shape))

def zeros(*shape):
    return t.FloatTensor(torch.zeros(*shape))
# -------------------------------------------------
# Model

class PosEvalModel(nn.Module):
    def __init__(self, sort_to_idx, const_to_idx, ind_to_idx,
                 conid_to_idx, evar_to_idx, fix_to_idx,
                 D=128, state=128, outsize=3, eps=1e-6, ln = False):
        super().__init__()

        # Dimensions
        self.D = D            # Dimension of embeddings
        self.state = state    # Dimension of GRU state

        table_names = ['sort', 'const', 'ind', 'conid', 'evar', 'fix', 'fixbody']
        tables = [sort_to_idx, const_to_idx, ind_to_idx, conid_to_idx, evar_to_idx, fix_to_idx, fix_to_idx]
        shift = 0
        self.shifts = {}
        for table_name, table in zip(table_names, tables):
            self.shifts[table_name] = shift
            shift += len(table)
        print(self.shifts, shift)
        self.embed_table = nn.Embedding(shift, D)

        # Embeddings for constants
        self.sort_to_idx = sort_to_idx
        # self.sort_embed = nn.Embedding(len(sort_to_idx), D)
        self.const_to_idx = const_to_idx
        # self.const_embed = nn.Embedding(len(const_to_idx), D)
        self.ind_to_idx = ind_to_idx
        # self.ind_embed = nn.Embedding(len(ind_to_idx), D)
        self.conid_to_idx = conid_to_idx
        # self.conid_embed = nn.Embedding(len(conid_to_idx), D)
        self.evar_to_idx = evar_to_idx
        # self.evar_embed = nn.Embedding(len(evar_to_idx), D)
        self.fix_to_idx = fix_to_idx
        # self.fix_embed = nn.Embedding(len(fix_to_idx), D)
        # self.fixbody_embed = nn.Embedding(len(fix_to_idx), D)

        # Embeddings for Gallina AST
        self.ast_cell_init_state = nn.Parameter(torch.randn(1, self.state)) #TODO(prafulla): Change this?
        self.ast_cell = nn.GRUCell(state, state)
        self.ast_emb_func = lambda folder, xs: ast_embed(folder, xs, self.ast_cell_init_state, ln)
        for attr in ["rel", "var", "evar", "sort", "cast", "prod",
                     "lam", "letin", "app", "const", "ind", "construct",
                     "case", "fix", "cofix", "proj1"]:
            self.__setattr__(attr, nn.Parameter(torch.randn(1, self.state)))

        # Embeddings for Tactic State (ctx, goal)
        self.ctx_cell_init_state = nn.Parameter(torch.randn(1, self.state)) #TODO(prafulla): Change this?
        self.ctx_cell = nn.GRUCell(state, state)
        self.proj = nn.Linear(state + 1, state)
        self.final = nn.Linear(state, outsize)
        self.ctx_emb_func = lambda folder, xs: ctx_embed(folder, xs, self.ctx_cell_init_state)
        self.loss_fn = nn.CrossEntropyLoss()

        # Layer Norm
        self.gamma = nn.Parameter(ones(state))
        self.beta = nn.Parameter(zeros(state))
        self.eps = eps

    def var_identity(self, x):
        return x

    def ctx_identity(self, x):
        return x

    def fix_id(self, table_name, id):
        # print(table_name, id, )
        # print(self.embed_table(autograd.Variable(torch.LongTensor([self.shifts[table_name] + id]))))
        return self.shifts[table_name] + id

    def embed_lookup_f(self, id):
        return self.embed_table(id)

    def ast_cell_f(self, x, hidden):
        hidden = self.ast_cell(x, hidden)
        return hidden

    def ctx_cell_f(self, x, hidden):
        hidden = self.ctx_cell(x, hidden)
        return hidden

    def coq_exp(self, *args):
        return self.emb_func(args)

    def final_f(self, x):
        return self.final(x)

    def proj_f(self, x):
        return self.proj(x)

    def cat_f(self, *xs):
        return torch.cat(xs, dim = -1)

    def ln_f(self, x):
        mean = x.mean(-1, keepdim=True)
        std = x.std(-1, keepdim=True)
        return self.gamma * (x - mean) / (std + self.eps) + self.beta
    # def loss_f(self, logits, target):
    #     return self.loss_fn(logits, target)
    #
    # def loss_func(self, folder, logits, targets):
    #     return folder.add('loss', logits, targets)

    def final_func(self, folder, x):
        return folder.add('final_f', x)

    def proj_func(self, folder, x):
        return folder.add('proj_f', x)

    def cat_func(self, folder, xs):
        return folder.add('cat_f', *xs)

    def mask(self, folder, xs):
        # First element is conclu, rest is state
        concl_id = autograd.Variable(ones([1,1]))
        state_id = autograd.Variable(zeros([1,1]))
        projs = []

        for i,x in enumerate(xs):
            if i == 0:
                id = concl_id
            else:
                id = state_id
            projs.append(self.proj_func(folder, self.cat_func(folder, [x, id])))
        return projs

        # ctx_mask = torch.zeros(len(xs), 1, 1)
        # ctx_mask[0][0][0] = 1.0
        # x = self.cat_func(xs, 0)
        # x = self.proj(x)
        # x = torch.cat([x, autograd.Variable(ctx_mask, requires_grad=False)], dim=-1)
        # xs = torch.split(x, 1)

    def pred(self, folder, *tacst_evs):
        xs = self.mask(folder, tacst_evs)
        x = self.ctx_emb_func(folder, xs)
        # Final layer for logits
        x = self.final_func(folder, x)
        return x

    def pred_attention(self, folder, *tacst_evs):
        self.attn_proj_func(folder, *tacst_evs)
    # def loss(self, folder, tactst_folder, tactst, target):
    #     logits = tactst_folder.fold_tacst(tactst)
    #     loss = self.loss_func(folder, logits, target)
    #     return loss

    # def logits(self, *tacst_evs):
    #     # Adding 1 to conclusion and 0 to expressions
        # ctx_mask = torch.zeros(len(tacst_evs), 1, 1)
        # ctx_mask[0][0][0] = 1.0
        # x = torch.cat(list(tacst_evs), 0)
        # x = self.proj(x)
        # x = torch.cat([x, autograd.Variable(ctx_mask, requires_grad=False)], dim=-1)
        # xs = torch.split(x, 1)
    #     xs = tacst_evs
    #     # Run GRU on tacst
    #     x = self.ctx_emb_func(xs)
    #
    #     # Final layer for logits
    #     x = self.final(x)
    #     print("Output shape", x.shape)
    #     return x.view(1, -1)
