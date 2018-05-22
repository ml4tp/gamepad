import torch
import torch.autograd as autograd
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim


"""
[Note]:

Goal is to test out pytorch dynamic graphs for ASTs (STLC).
"""


# ---------------------------------------------------------
# Types

class Typ(object):
    pass


class BoolTyp(Typ):
    def __init__(self):
        pass


class ArrTyp(Typ):
    def __init__(self, ty1, ty2):
        assert isinstance(ty1, Typ)
        assert isinstance(ty2, Typ)
        self.ty1 = ty1
        self.ty2 = ty2


# ---------------------------------------------------------
# Expressions

class Exp(object):
    pass


class TrueExp(Exp):
    def __init__(self):
        pass


class FalseExp(Exp):
    def __init__(self):
        pass


class IfExp(Exp):
    def __init__(self, e1, e2, e3):
        assert isinstance(e1, Exp)
        assert isinstance(e2, Exp)
        assert isinstance(e3, Exp)
        self.e1 = e1
        self.e2 = e2
        self.e3 = e3


class VarExp(Exp):
    def __init__(self, x):
        self.x = x


class LamExp(Exp):
    def __init__(self, x, ty, e):
        assert isinstance(ty, Typ)
        assert isinstance(e, Exp)
        self.x = x
        self.ty = ty
        self.e = e

        self.tag = None


class AppExp(Exp):
    def __init__(self, e1, e2):
        assert isinstance(e1, Exp)
        assert isinstance(e2, Exp)
        self.e1 = e1
        self.e2 = e2


# ---------------------------------------------------------
# Enumerate expressions

class EnumExp(object):
    def __init__(self):
        pass

    def enum(self):
        pass


# ---------------------------------------------------------
# Embed expressions

class Env(object):
    def __init__(self, env={}):
        self.env = env

    def lookup(self, x):
        return self.env[x]

    def extend(self, key, val):
        env_p = {}
        for k, v in self.env.items():
            env_p[k] = v
        env_p[key] = val
        return Env(env_p)


class GenSym(object):
    def __init__(self):
        self.cnt = 1

    def gensym(self, prefix):
        idx = self.cnt
        self.cnt += 1
        return "{}-{}".format(prefix, idx)


class EmbedExp(object):
    def __init__(self, const_to_idx, embed_const, gs, embed_local, D=5):
        # Dimension of embedding
        self.D = D

        # Embedding for STLC + Bool constants
        self.const_to_idx = const_to_idx
        self.embed_const = embed_const

        # Local variable embeddings
        self.gs = gs
        self.embed_local = embed_local

    def embed_exp(self, env, e):
        if isinstance(e, TrueExp):
            lookup_tensor = torch.LongTensor([self.const_to_idx['T']])
            ev_tt = self.embed_const(autograd.Variable(lookup_tensor))
            return self.embed_true(ev_tt)
        elif isinstance(e, FalseExp):
            lookup_tensor = torch.LongTensor([self.const_to_idx['F']])
            ev_ff = self.embed_const(autograd.Variable(lookup_tensor))
            return self.embed_false(ev_ff)
        elif isinstance(e, IfExp):
            ev_e1 = self.embed_exp(env, e.e1)
            ev_e2 = self.embed_exp(env, e.e2)
            ev_e3 = self.embed_exp(env, e.e3)

            return self.embed_if(ev_e1, ev_e2, ev_e3)
        elif isinstance(e, VarExp):
            ev_x = env.lookup(e.x)

            return self.embed_var(ev_x)
        elif isinstance(e, LamExp):
            if not e.tag:
                ev_x = self.rand_embed()
                x_ident = self.gs.gensym(e.x)
                self.embed_local[x_ident] = ev_x
                e.tag = x_ident
            else:
                ev_x = self.embed_local[e.tag]

            ev_ty = self.embed_typ(e.ty)
            ev_e = self.embed_exp(env.extend(e.x, ev_x), e.e)

            return self.embed_lam(ev_x, ev_ty, ev_e)
        elif isinstance(e, AppExp):
            ev_e1 = self.embed_exp(env, e.e1)
            ev_e2 = self.embed_exp(env, e.e2)

            return self.embed_app(ev_e1, ev_e2)
        else:
            raise NameError("Expression not supported")

    def rand_embed(self):
        return autograd.Variable(torch.randn(self.D), requires_grad=True)

    def embed_typ(self, ty):
        if isinstance(ty, BoolTyp):
            lookup_tensor = torch.LongTensor([self.const_to_idx['B']])
            ev_bool = self.embed_const(autograd.Variable(lookup_tensor))
            return self.embed_bool(ev_bool)
        elif isinstance(ty, ArrTyp):
            ev_ty1 = self.embed_typ(ty.ty1)
            ev_ty2 = self.embed_typ(ty.ty1)
            return self.embed_arr(ev_ty1, ev_ty2)
        else:
            raise NameError("Type not supported")

    def embed_bool(self, ev_bool):
        return ev_bool

    def embed_true(self, ev_true):
        return ev_true

    def embed_false(self, ev_false):
        return ev_false

    def embed_var(self, ev_x):
        return ev_x

    def embed_if(self, ev_e1, ev_e2, ev_e3):
        # TODO(deh): think about
        return ev_e1

    def embed_lam(self, ev_x, ev_ty, ev_e):
        # TODO(deh): think about
        return ev_e

    def embed_app(self, ev_e1, ev_e2):
        # TODO(deh): think about
        return ev_e1


class MyModel(nn.Module):
    def __init__(self, const_to_idx, embedding_dim):
        super().__init__()
        self.const_evs = nn.Embedding(3, embedding_dim)
        self.linear1 = nn.Linear(embedding_dim, 64)
        self.linear2 = nn.Linear(64, 3)

        self.local_evs = {}
        self.embedder = EmbedExp(const_to_idx, self.const_evs, GenSym(), self.local_evs)

    def forward(self, e):
        ev = self.embedder.embed_exp(Env(), e)
        out = F.relu(self.linear1(ev))
        out = self.linear2(out)
        log_probs2 = F.log_softmax(out)
        return log_probs2.view(1, 3)


# ---------------------------------------------------------
# Test

def foobar(const_to_idx, e):
    if isinstance(e, TrueExp):
        return const_to_idx['T']
    elif isinstance(e, FalseExp):
        return const_to_idx['F']
    else:
        raise NameError("What the heck")


if __name__ == "__main__":
    e_tt = TrueExp()
    e_ff = FalseExp()
    e_swap = IfExp(VarExp("x"), e_ff, e_tt)
    e1 = LamExp("x", BoolTyp(), e_swap)
    e2 = AppExp(e1, e_tt)

    es = [(e_tt, e_tt), (e_ff, e_ff), (e2, e_ff)]

    losses = []
    loss_function = nn.NLLLoss()
    const_to_idx = {}
    const_to_idx['T'] = 0
    const_to_idx['F'] = 1
    const_to_idx['B'] = 2
    model = MyModel(const_to_idx, 5)
    optimizer = optim.SGD(model.parameters(), lr=0.001)

    for epoch in range(100):
        total_loss = torch.Tensor([0])
        for e_input, e_output in es:
            # Step 1. Prepare the inputs to be passed to the model (i.e, turn the words
            # into integer indices and wrap them in variables)
            # context_idxs = [word_to_ix[w] for w in context]
            # context_var = autograd.Variable(torch.LongTensor(context_idxs))

            # Step 2. Recall that torch *accumulates* gradients. Before passing in a
            # new instance, you need to zero out the gradients from the old instance
            model.zero_grad()

            # Step 3. Run the forward pass, getting log probabilities over next words
            log_probs = model(e_input)

            # Step 4. Compute your loss function. (Again, Torch wants the target
            # word wrapped in a variable)
            output = autograd.Variable(torch.LongTensor([foobar(const_to_idx, e_output)]))

            loss = loss_function(log_probs, output)

            # Step 5. Do the backward pass and update the gradient
            loss.backward()
            optimizer.step()

            total_loss += loss.data
            print("LOCALS", model.local_evs.keys())
        losses.append(total_loss)
        #print(total_loss)
    print("Losses", losses)  # The loss decreased every iteration over the training data!
