import numpy as np
import torch
import torch.autograd as autograd
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim

from coq.ast import *
from coq.decode import DecodeCoqExp
from lib.myenv import MyEnv
from lib.myutil import NotFound

"""
[Note]

Create embedding of Coq Tactic Trees into R^D vectors.
Where to put model and training code?
"""


# -------------------------------------------------
# Embed Expressions

class EmbedCoqExp(object):
    def __init__(self,
                 sort_to_idx, sort_embed,
                 const_to_idx, const_embed,
                 ind_to_idx, ind_embed,
                 conid_to_idx, conid_embed,
                 evar_to_idx, evar_embed,
                 fix_to_idx, fix_embed, fixbody_embed,
                 decoded, D=5):
        # assert isinstance(decoded, DecodeCoqExp)
        # Dimension of embedding
        self.D = D

        # Shared representation
        self.decoded = decoded

        # Global embeddings
        self.sort_to_idx = sort_to_idx
        self.sort_embed = sort_embed

        self.const_to_idx = const_to_idx
        self.const_embed = const_embed

        self.ind_to_idx = ind_to_idx
        self.ind_embed = ind_embed

        self.conid_to_idx = conid_to_idx
        self.conid_embed = conid_embed

        self.evar_to_idx = evar_to_idx
        self.evar_embed = evar_embed

        self.fix_to_idx = fix_to_idx
        self.fix_embed = fix_embed           # For use everywhere else
        self.fixbody_embed = fixbody_embed   # For use in the body

        # Keep track of shared embeddings
        self.embeddings = {}

        # Internal debugging
        self.bad_idents = set()
        self.GID = 0

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
                # TODO(deh): some weird shit going on in Coq printing
                ev_idx = self.embed_local_var(None)
                self.bad_idents.add(c.idx)
                print("FAILED TO LOOKUP {} in gid {}".format(c.idx, self.GID))
            return self._embedcon(key, self.embed_rel(ev_idx))
        elif isinstance(c, VarExp):
            ev_x = env.lookup_id(Name(c.x))
            """
            try:
                ev_x = env.lookup_id(Name(c.x))
            except NotFound:
                # TODO(deh): some weird shit going on in Coq printing
                ev_x = self.embed_local_var(None)
                self.bad_idents.add(c.x)
                print("FAILED TO LOOKUP {} in gid {}".format(c.x, self.GID))
            """
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
            ev_ty1 = self._embed_ast(env, Kind.TYPE, c.ty1)
            ev_ty2 = self._embed_ast(env, Kind.TYPE, c.ty2)
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
                self.fixbody_embed[name] = ev
                env = env.extend(name, ev)

            # 2. Use initial embeddings
            ev_tys = []
            ev_cs = []
            for ty, body in zip(c.tys, c.cs):
                ev_tys += [self._embed_ast(env, Kind.TYPE, ty)]
                ev_c = self._embed_ast(env, Kind.TERM, body)
                # Tie the knot appropriately
                self.fix_embed[name] = ev_c
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
        lookup_tensor = torch.LongTensor([self.evar_to_idx[exk]])
        return self.evar_embed(autograd.Variable(lookup_tensor))

    def embed_const_name(self, const):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.const_to_idx[const]])
        return self.const_embed(autograd.Variable(lookup_tensor))

    def embed_sort_name(self, sort):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.sort_to_idx[sort]])
        return self.sort_embed(autograd.Variable(lookup_tensor))

    def embed_ind_name(self, ind):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.ind_to_idx[ind.mutind]])
        return self.ind_embed(autograd.Variable(lookup_tensor))

    def embed_conid_name(self, ind_and_conid):
        """Override Me"""
        ind, conid = ind_and_conid
        lookup_tensor = torch.LongTensor([self.conid_to_idx[(ind.mutind, conid)]])
        return self.conid_embed(autograd.Variable(lookup_tensor))

    def embed_fix_name(self, name):
        """Override Me"""
        lookup_tensor = torch.LongTensor([self.fix_to_idx[exk]])
        return self.fix_embed(autograd.Variable(lookup_tensor))

    # -------------------------------------------
    # Local embedding initialization

    def embed_local_var(self, ty):
        """Override Me"""
        return autograd.Variable(torch.randn(self.D), requires_grad=False)
        # return np.random.multivariate_normal(np.zeros(self.D), np.eye(self.D))

    # -------------------------------------------
    # Combining embeddings

    def embed_rel(self, ev_idx):
        """Override Me"""
        return ev_idx

    def embed_var(self, ev_x):
        """Override Me"""
        return ev_x

    def embed_evar(self, ev_evar, ev_cs):
        """Override Me"""
        return ev_evar

    def embed_sort(self, ev_sort):
        """Override Me"""
        return ev_sort

    def embed_cast(self, ev_c, ck, ev_ty):
        """Override Me"""
        return ev_c

    def embed_prod(self, name, ev_ty1, ev_ty2):
        """Override Me"""
        return ev_ty1

    def embed_lambda(self, name, ev_ty, ev_body):
        """Override Me"""
        return ev_body

    def embed_letin(self, name, ev_c1, ev_ty, ev_c2):
        """Override Me"""
        return ev_c2

    def embed_app(self, ev_c, ev_cs):
        """Override Me"""
        return ev_c

    def embed_const(self, ev_const, ev_ui):
        """Override Me"""
        return ev_const

    def embed_ind(self, ev_ind, ev_ui):
        """Override Me"""
        return ev_ind

    def embed_construct(self, ev_ind, ev_conid, ev_ui):
        """Override Me"""
        return ev_conid

    def embed_case(self, ci, ev_ret, ev_match, ev_cases):
        """Override Me"""
        return ev_ret

    def embed_fix(self, iarr, idx, names, ev_tys, ev_cs):
        """Override Me"""
        return ev_cs[0]

    def embed_cofix(self, idx, names, ev_tys, ev_cs):
        """Override Me"""
        return ev_cs[0]

    def embed_proj(self, proj, ev_c):
        """Override Me"""
        return ev_c

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
    def __init__(self, sort_to_idx, sort_embed,
                 const_to_idx, const_embed,
                 ind_to_idx, ind_embed,
                 conid_to_idx, conid_embed,
                 evar_to_idx, evar_embed,
                 fix_to_idx, fix_embed, fixbody_embed,
                 tactr):
        self.tactr = tactr
        self.ece = EmbedCoqExp(sort_to_idx, sort_embed,
                               const_to_idx, const_embed,
                               ind_to_idx, ind_embed,
                               conid_to_idx, conid_embed,
                               evar_to_idx, evar_embed,
                               fix_to_idx, fix_embed, fixbody_embed,
                               tactr.decoder.decoded)

        # Sharing
        self.ctxid_embeds = {}
        self.goal_embeds = {}

    def embed(self):
        bfs = self.tactr.bfs_traverse()
        acc = []
        for node in bfs:
            if node[0] == 'OPEN':
                _, gid, _, _, ctx_ids, goal_idx, edge = node
                env, evs = self.embed_ctx(gid, ctx_ids)
                ev = self.embed_goal(gid, env, goal_idx)
                acc += [(evs, ev)]
            else:
                # TODO(deh): what to do on terminal nodes?
                _, gid, edge = node
        return acc

    def embed_ctx(self, gid, ctx_idents):
        evs = []
        env = MyEnv()
        for ident in ctx_idents:
            ev = self.embed_ctx_ident(gid, env, ident)
            env = env.extend(Name(ident), ev)
            evs += [ev]
        return env, evs

    def embed_ctx_ident(self, gid, env, ident):
        if ident in self.ctxid_embeds:
            return self.ctxid_embeds[ident]
        else:
            c = self.tactr.decoder.decode_exp_by_ctxid(ident)
            self.ece.GID = gid
            ev = self.ece.embed_ast(env, c)
            self.ctxid_embeds[ident] = ev
            return ev

    def embed_goal(self, gid, env, goal_idx):
        if goal_idx in self.goal_embeds:
            return self.goal_embeds[goal_idx]
        else:
            c = self.tactr.decoder.decode_exp_by_key(goal_idx)
            self.ece.GID = gid
            ev = self.ece.embed_ast(env, c)
            self.goal_embeds[goal_idx] = ev
            return ev


# -------------------------------------------------
# Model

class MyModel(nn.Module):
    def __init__(self, sort_to_idx, const_to_idx, ind_to_idx,
                 conid_to_idx, evar_to_idx, fix_to_idx,
                 D=5):
        super().__init__()

        # Dimension
        self.D = D

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

        # TODO(prafulla): put LSTM variables here

    def forward(self, tactr):
        embedder = EmbedCoqTacTr(self.sort_to_idx, self.sort_embed,
                                 self.const_to_idx, self.const_embed,
                                 self.ind_to_idx, self.ind_embed,
                                 self.conid_to_idx, self.conid_embed,
                                 self.evar_to_idx, self.evar_embed,
                                 self.fix_to_idx, self.fix_embed,
                                 self.fixbody_embed, tactr)
        evs = embedder.embed()
        print(evs)
        # TODO(prafulla): put LSTM model here
        # raise NotImplementedError


# -------------------------------------------------
# Training

class MyTrainer(object):
    def __init__(self, model, tactrs):
        self.model = model       # PyTorch model
        self.tactrs = tactrs     # Tactic trees

    def train(self, epochs=100):
        losses = []
        loss_function = nn.NLLLoss()
        optimizer = optim.SGD(self.model.parameters(), lr=0.001)
        for epoch in range(epochs):
            total_loss = torch.Tensor([0])
            for e_input in self.tactrs:
                self.model.zero_grad()
                log_probs = self.model(e_input)

                # TODO(prafulla): loss here?
                # output = autograd.Variable(torch.LongTensor([foobar(const_to_idx, e_output)]))
                # loss = loss_function(log_probs, output)
                # loss.backward()
                # optimizer.step()
                # total_loss += loss.data
            losses.append(total_loss)
        print("Losses", losses)
