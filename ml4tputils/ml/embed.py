import numpy as np
import torch
import torch.autograd as autograd
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
torch.manual_seed(0)

from coq.ast import *
from coq.decode import DecodeCoqExp
from lib.myenv import MyEnv
from lib.myutil import NotFound

from coq.util import SizeCoqExp
from time import time

from ml.utils import ResultLogger

logger = ResultLogger('mllogs/embedv0.5.jsonl')

"""
[Note]

Create embedding of Coq Tactic Trees into R^D vectors.
Where to put model and training code?

NOTE(deh):
We are still missing some idents. 
[FIXED] 1. Why is this happening?? Because we aren't alpha-converting the rest of the
context. Fixing this with new version of proof format.
[FIXED] 2. Rel is because Prod is Dependent Product so its a binding form.
"""

def gru_embed(xs, cell, init):
    hidden = init
    for i,x in enumerate(xs):
        #print("GRU Embed ",i, x.shape)
        out, hidden = cell(x.view(1, 1, -1), hidden)
    return hidden

# -------------------------------------------------
# Embed Expressions

class EmbedCoqExp(object):
    def __init__(self,
                 model,
                 decoded):
        # assert isinstance(decoded, DecodeCoqExp)

        # Shared representation
        self.decoded = decoded

        # Model
        self.model = model

        # Keep track of shared embeddings
        self.embeddings = {}

        # Internal debugging
        self.bad_idents = set()
        self.GID = 0
        self.ctx_idents = []

    def embed_ast(self, env, c):
        return self._embed_ast(env, Kind.TERM, c)

    def _embedcon(self, key, embed_vec):
        self.embeddings[key] = embed_vec
        return embed_vec

    def _embed_ast(self, env, kind, c):
        key = c.tag
        if key in self.embeddings:
            return self.embeddings[key]

        if isinstance(c, RelExp):
            # NOTE(deh): DeBruinj indicides start at 1 ...
            try:
                ev_idx = env.lookup_rel(c.idx - 1)
            except NotFound:
                ev_idx = self.embed_local_var(None)
                self.bad_idents.add(c.idx)
                print("FAILED TO LOOKUP REL {} in gid {} in ctx {}".format(c.idx, self.GID, self.ctx_idents))
            return self._embedcon(key, self.embed_rel(ev_idx))
        elif isinstance(c, VarExp):
            try:
                ev_x = env.lookup_id(Name(c.x))
            except NotFound:
                ev_x = self.embed_local_var(None)
                self.bad_idents.add(c.x)
                print("FAILED TO LOOKUP VAR {} in gid {} in ctx {}".format(c.x, self.GID, self.ctx_idents))
            return self._embedcon(key, self.embed_var(ev_x))
        elif isinstance(c, MetaExp):
            assert False, "NOTE(deh): MetaExp should never be in dataset"
        elif isinstance(c, EvarExp):
            ev_exk = self.embed_evar_name(c.exk)
            ev_cs = self._embed_asts(env, Kind.TYPE, c.cs)
            return self._embedcon(key, self.embed_evar(ev_exk, ev_cs))
        elif isinstance(c, SortExp):
            ev_sort = self.embed_sort_name(c.sort)
            return self._embedcon(key, self.embed_sort(ev_sort))
        elif isinstance(c, CastExp):
            ev_c = self._embed_ast(env, Kind.TERM, c.c)
            ev_ty = self._embed_ast(env, Kind.TYPE, c.ty)
            return self._embedcon(key, self.embed_cast(ev_c, c.ck, ev_ty))
        elif isinstance(c, ProdExp):
            ev_x = self.embed_local_var(c.ty1)
            ev_ty1 = self._embed_ast(env, Kind.TYPE, c.ty1)
            ev_ty2 = self._embed_ast(env.extend(c.name, ev_x),
                                     Kind.TYPE, c.ty2)
            return self._embedcon(key, self.embed_prod(c.name, ev_ty1, ev_ty2))
        elif isinstance(c, LambdaExp):
            ev_x = self.embed_local_var(c.ty)
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
            ev_cs = self._embed_asts(env, Kind.TERM, c.cs)
            return self._embedcon(key, self.embed_app(ev_c, ev_cs))
        elif isinstance(c, ConstExp):
            ev_const = self.embed_const_name(c.const)
            ev_ui = self.embed_ui(c.ui)
            return self._embedcon(key, self.embed_const(ev_const, ev_ui))
        elif isinstance(c, IndExp):
            ev_ind = self.embed_ind_name(c.ind)
            ev_ui = self.embed_ui(c.ui)
            return self._embedcon(key, self.embed_ind(ev_ind, ev_ui))
        elif isinstance(c, ConstructExp):
            ev_ind = self.embed_ind_name(c.ind)
            ev_conid = self.embed_conid_name((c.ind, c.conid))
            ev_ui = self.embed_ui(c.ui)
            return self._embedcon(key, self.embed_construct(ev_ind, ev_conid,
                                                            ev_ui))
        elif isinstance(c, CaseExp):
            ev_ret = self._embed_ast(env, Kind.TERM, c.ret)
            ev_match = self._embed_ast(env, Kind.TERM, c.match)
            ev_cases = self._embed_asts(env, Kind.TERM, c.cases)
            return self._embedcon(key, self.embed_case(c.ci, ev_ret, ev_match,
                                                       ev_cases))
        elif isinstance(c, FixExp):
            # 1. Create initial embeddings
            for name in c.names:
                ev = self.embed_fix_name(name)
                # self.fixbody_embed[name] = ev
                env = env.extend(name, ev)

            # 2. Use initial embeddings
            ev_tys = []
            ev_cs = []
            for ty, body in zip(c.tys, c.cs):
                ev_tys += [self._embed_ast(env, Kind.TYPE, ty)]
                ev_c = self._embed_ast(env, Kind.TERM, body)
                # TODO(deh): wtf?
                # Tie the knot appropriately
                # self.fix_embed[name] = ev_c
                ev_cs += [ev_c]
            return self._embedcon(key, self.embed_fix(c.iarr, c.idx, c.names,
                                                      ev_tys, ev_cs))
        elif isinstance(c, CoFixExp):
            # NOTE(deh): CoFixExp not in dataset
            raise NameError("NOTE(deh): CoFixExp not in dataset")
        elif isinstance(c, ProjExp):
            # NOTE(deh): ProjExp not in dataset
            ev = self._embed_ast(env, Kind.TERM, c.c)
            return self._embedcon(key, self.combine_proj(c.proj, ev))
        else:
            raise NameError("Kind {} not supported".format(c))

    def _embed_asts(self, env, kind, cs):
        return [self._embed_ast(env, kind, c) for c in cs]

    # -------------------------------------------
    # Global embedding initialization

    def embed_evar_name(self, exk):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.model.evar_to_idx[exk]])
        return self.model.evar_embed(autograd.Variable(lookup_tensor))

    def embed_const_name(self, const):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.model.const_to_idx[const]])
        return self.model.const_embed(autograd.Variable(lookup_tensor))

    def embed_sort_name(self, sort):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.model.sort_to_idx[sort]])
        return self.model.sort_embed(autograd.Variable(lookup_tensor))

    def embed_ind_name(self, ind):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.model.ind_to_idx[ind.mutind]])
        return self.model.ind_embed(autograd.Variable(lookup_tensor))

    def embed_conid_name(self, ind_and_conid):
        """Override Me"""
        ind, conid = ind_and_conid
        lookup_tensor = torch.LongTensor([self.model.conid_to_idx[(ind.mutind, conid)]])
        return self.model.conid_embed(autograd.Variable(lookup_tensor))

    def embed_fix_name(self, name):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.model.fix_to_idx[name]])
        return self.model.fix_embed(autograd.Variable(lookup_tensor))

    # -------------------------------------------
    # Local embedding initialization

    def embed_local_var(self, ty):
        """Override Me"""
        return autograd.Variable(torch.randn(self.model.D), requires_grad=False)

    # -------------------------------------------
    # Combining embeddings

    def embed_rel(self, ev_idx):
        """Override Me"""
        return self.model.emb_func([self.model.rel, ev_idx])

    def embed_var(self, ev_x):
        """Override Me"""
        return self.model.emb_func([self.model.var, ev_x])

    def embed_evar(self, ev_evar, ev_cs):
        """Override Me"""
        return self.model.emb_func([self.model.evar, ev_evar])

    def embed_sort(self, ev_sort):
        """Override Me"""
        return self.model.emb_func([self.model.sort, ev_sort])

    def embed_cast(self, ev_c, ck, ev_ty):
        """Override Me"""
        return self.model.emb_func([self.model.cast, ev_c, ev_ty])

    def embed_prod(self, name, ev_ty1, ev_ty2):
        """Override Me"""
        return self.model.emb_func([self.model.prod, ev_ty1, ev_ty2])

    def embed_lambda(self, name, ev_ty, ev_body):
        """Override Me"""
        return self.model.emb_func([self.model.lamb, ev_ty, ev_body])

    def embed_letin(self, name, ev_c1, ev_ty, ev_c2):
        """Override Me"""
        return self.model.emb_func([self.model.letin, ev_c1, ev_ty, ev_c2])

    def embed_app(self, ev_c, ev_cs):
        """Override Me"""
        return self.model.emb_func([self.model.app, ev_c] + ev_cs)

    def embed_const(self, ev_const, ev_ui):
        """Override Me"""
        return self.model.emb_func([self.model.const, ev_const])

    def embed_ind(self, ev_ind, ev_ui):
        """Override Me"""
        return self.model.emb_func([self.model.ind, ev_ind])

    def embed_construct(self, ev_ind, ev_conid, ev_ui):
        """Override Me"""
        return self.model.emb_func([self.model.construct, ev_ind, ev_conid])

    def embed_case(self, ci, ev_ret, ev_match, ev_cases):
        """Override Me"""
        return self.model.emb_func([self.model.case, ev_ret, ev_match] + ev_cases)

    def embed_fix(self, iarr, idx, names, ev_tys, ev_cs):
        """Override Me"""
        return self.model.emb_func([self.model.fix] + ev_cs)

    def embed_cofix(self, idx, names, ev_tys, ev_cs):
        """Override Me"""
        raise NameError("TODO(prafulla, deh): No cofix in feit-thompson")
        # return self.model.emb_func([self.model.cofix] + ev_cs)

    def embed_proj(self, proj, ev_c):
        """Override Me"""
        raise NameError("TODO(prafulla, deh): No proj in feit-thompson")
        # return self.model.emb_func([self.model.proj1, ev_c])

    # -------------------------------------------
    # Embed universes

    def embed_ui(self, ui):
        """Override Me"""
        # NOTE(deh): Punting on this for now
        # how many universe instances are there?
        return None

    def embed_uis(self, uis):
        return [self.embed_ui(ui) for ui in uis]


# -------------------------------------------------
# Embed Tactic Tree

class EmbedCoqTacTr(object):
    def __init__(self, model, tactr):
        self.model = model
        self.tactr = tactr
        self.ece = EmbedCoqExp(model, tactr.decoder.decoded)

        # Sharing
        self.ctxid_embeds = {}
        self.concl_embeds = {}

    def embed(self):
        bfs = self.tactr.bfs_traverse()
        acc = []
        for node in bfs:
            if node[0] == 'OPEN':
                _, gid, _, _, ctx, concl_idx, _ = node
                env, evs = self.embed_ctx(gid, ctx)
                ev = self.embed_concl(gid, env, concl_idx)
                acc += [(evs, ev)]
            else:
                # TODO(deh): what to do on terminal nodes?
                _, gid, edge = node
        return acc

    def embed_tacst(self, tacst):
        self.ece = EmbedCoqExp(self.model, self.tactr.decoder.decoded)
        gid, ctx, concl_idx, tac = tacst
        env, evs = self.embed_ctx(gid, ctx)
        ev = self.embed_concl(gid, env, concl_idx)
        return [ev] + evs

    def embed_ctx(self, gid, ctx):
        evs = []
        env = MyEnv()
        for ident, typ_idx in ctx:
            ev = self.embed_ctx_ident(gid, env, typ_idx)
            self.ece.ctx = ctx
            env = env.extend(Name(ident), ev)
            evs += [ev]
        return env, evs

    def embed_ctx_ident(self, gid, env, typ_idx):
        # if typ_idx in self.ctxid_embeds:
        #     return self.ctxid_embeds[typ_idx]
        # else:
        c = self.tactr.decoder.decode_exp_by_key(typ_idx)
        self.ece.GID = gid
        ev = self.ece.embed_ast(env, c)
        self.ctxid_embeds[typ_idx] = ev
        return ev

    def embed_concl(self, gid, env, concl_idx):
        # if concl_idx in self.concl_embeds:
        #     return self.concl_embeds[concl_idx]
        # else:
        c = self.tactr.decoder.decode_exp_by_key(concl_idx)
        self.ece.GID = gid
        ev = self.ece.embed_ast(env, c)
        self.concl_embeds[concl_idx] = ev
        return ev


# -------------------------------------------------
# Model

class MyModel(nn.Module):
    def __init__(self, sort_to_idx, const_to_idx, ind_to_idx,
                 conid_to_idx, evar_to_idx, fix_to_idx,
                 D=128, state=128, outsize = 3):
        super().__init__()

        # Dimension
        self.D = D
        self.state = state

        # Embeddings
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

        # Embed AST
        self.cell_init_state = autograd.Variable(torch.randn((1, 1, self.state))) #TODO: Change this
        self.cell = nn.GRU(state, state)
        self.emb_func = lambda xs: gru_embed(xs, self.cell, self.cell_init_state)
        for attr in ["rel", "var", "evar", "sort", "cast", "prod",
                     "lamb", "letin", "app", "const", "ind", "construct",
                     "case", "fix", "cofix", "proj1"]:
            self.__setattr__(attr, autograd.Variable(torch.randn(self.state)))

        # Embed Ctx / TacticState
        self.ctx_cell_init_state = autograd.Variable(torch.randn((1, 1,self.state)))
        self.ctx_cell = nn.GRU(state, state)
        self.proj = nn.Linear(state, state - 1)
        self.final = nn.Linear(state, outsize)
        self.ctx_emb_func = lambda xs: gru_embed(xs, self.ctx_cell, self.ctx_cell_init_state)

    def forward(self, embedder, tacst):
        evs = embedder.embed_tacst(tacst)

        # Adding 1 to conclusion and 0 to expressions
        ctx_mask = torch.zeros(len(evs), 1, 1)
        ctx_mask[0][0][0] = 1.0
        x = torch.cat(evs, 0)
        x = self.proj(x)
        x = torch.cat([x, autograd.Variable(ctx_mask, requires_grad = False)], dim=-1)
        xs = torch.split(x, 1)

        # Run GRU on tacst
        x = self.ctx_emb_func(xs)

        # Final layer for logits
        x = self.final(x)
        print("Output shape", x.shape)
        return x.view(1, -1)
        # raise NotImplementedError


# -------------------------------------------------
# Training

class PosEvalTrainer(object):
    def __init__(self, model, tactrs, poseval_dataset):
        self.model = model       # PyTorch model
        self.tactrs = tactrs
        self.poseval_dataset = poseval_dataset  

        self.tactr_embedder = {}
        for tactr_id, tactr in enumerate(self.tactrs):
            self.tactr_embedder[tactr_id] = EmbedCoqTacTr(model, tactr)

    def train(self, epochs=20):
        losses = []
        loss_function = nn.CrossEntropyLoss()
        optimizer = optim.Adam(self.model.parameters(), lr = 0.001) #optim.SGD(self.model.parameters(), lr=0.001)
        for epoch in range(epochs):
            testart = time()
            total_loss = torch.Tensor([0])
            for idx, (tactr_id, poseval_pt) in enumerate(self.poseval_dataset):
                tstart = time()
                print("TRAINING ({}/{}) TacSt={}, AstSize={}".format(tactr_id, len(self.tactrs), idx, poseval_pt.tacst_size))
                self.model.zero_grad()
                log_probs = self.model(self.tactr_embedder[tactr_id], poseval_pt.tacst)
                target = autograd.Variable(torch.LongTensor([poseval_pt.subtr_bin]))
                loss = loss_function(log_probs, target)
                loss.backward()
                optimizer.step()
                total_loss += loss.data
                tend = time()
                print("Loss %.4f %.4f" % (loss.data, tend - tstart))
                logger.log(n_epochs = epoch, niters = idx, loss = "%0.4f" % loss.data)
            print("Epoch Time %.4f Loss %.4f" % (time() - testart, total_loss))
            losses.append(total_loss)
        logger.close()
        print("Losses", losses)
