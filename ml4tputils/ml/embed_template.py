from abc import override

from ml.embed import EmbedCoqExp


"""
[Note]

Create embedding of Coq Tactic Trees into R^D vectors.

The class EmbedCoqExp takes care of traversing the AST. All that is required
is to implement:
1. What to do on global values (e.g., learned parameter vector)
2. What to do with local variables (e.g., learned parameter vector)
3. How to embed compound expressions, given the embeddings of their children.

ENJOY!
"""


class EmbedCoqExpTemplate(EmbedCoqExp):
    # -------------------------------------------
    # Global embedding initialization

    @override
    def embed_evar_name(self, exk):
        raise NotImplementedError

    @override
    def embed_const_name(self, const):
        raise NotImplementedError

    @override
    def embed_sort_name(self, sort):
        raise NotImplementedError

    @override
    def embed_ind_name(self, ind):
        raise NotImplementedError

    @override
    def embed_conid_name(self, ind_and_conid):
        ind, conid = ind_and_conid
        raise NotImplementedError

    @override
    def embed_rec_name(self, name):
        raise NotImplementedError

    # -------------------------------------------
    # Global embedding initialization

    @override
    def embed_local_var(self, ty):
        raise NotImplementedError

    # -------------------------------------------
    # Combining embeddings

    @override
    def embed_rel(self, ev_idx):
        raise NotImplementedError

    @override
    def embed_var(self, ev_x):
        raise NotImplementedError

    @override
    def embed_evar(self, ev_evar, ev_cs):
        raise NotImplementedError

    @override
    def embed_sort(self, ev_sort):
        raise NotImplementedError

    @override
    def embed_cast(self, ev_c, ck, ev_ty):
        raise NotImplementedError

    @override
    def embed_prod(self, name, ev_ty1, ev_ty2):
        raise NotImplementedError

    @override
    def embed_lambda(self, name, ev_ty, ev_body):
        raise NotImplementedError

    @override
    def embed_letin(self, name, ev_c1, ev_ty, ev_c2):
        raise NotImplementedError

    @override
    def embed_app(self, ev_c, ev_cs):
        raise NotImplementedError

    @override
    def embed_const(self, ev_const, ev_ui):
        raise NotImplementedError

    @override
    def embed_ind(self, ev_ind, ev_ui):
        raise NotImplementedError

    @override
    def embed_construct(self, ev_ind, ev_conid, ev_ui):
        raise NotImplementedError

    @override
    def embed_case(self, ci, ev_ret, ev_match, ev_cases):
        raise NotImplementedError

    @override
    def embed_fix(self, iarr, idx, names, ev_tys, ev_cs):
        raise NotImplementedError

    @override
    def embed_cofix(self, idx, names, ev_tys, ev_cs):
        raise NotImplementedError

    @override
    def embed_proj(self, proj, ev_c):
        raise NotImplementedError

    # -------------------------------------------
    # Embed universes

    @override
    def embed_ui(self, ui):
        # NOTE(deh): Punting on this for now
        raise NotImplementedError
