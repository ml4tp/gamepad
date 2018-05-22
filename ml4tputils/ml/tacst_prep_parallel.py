import argparse
import numpy as np
import pickle

from coq.tactics import TACTICS_EQUIV
from coq.constr_util import SizeConstr
from coq.glob_constr_util import SizeGlobConstr
from lib.myedit import *

from multiprocessing import Pool

"""
[Note]

Prepare data for:
1. Position evaluation
2. Tactic prediction (can just truncate)
"""


# -------------------------------------------------
# Seeding

np.random.seed(7)


def _tac_bin(tac, tactics_equiv=TACTICS_EQUIV):
    for idx, eq_tacs in enumerate(tactics_equiv):
        for tac_p in eq_tacs:
            if tac[-1].name.startswith(tac_p):
                return idx
    raise NameError("Not assigned to bin", tac[-1].name)


def mk_tactr(tactr_id):
    print("Working on {}".format(tactr_id))
    with open("tactrs/%s.pickle" % tactr_id, 'rb') as f:
        tactr = pickle.load(f)
    data = []
    tactics = set()
    subtr_size = {}
    size_subtr = SizeSubTr(tactr)
    for node in tactr.graph.nodes():
        subtr_size[node.gid] = size_subtr.size(node)
        if node in tactr.gid_tactic:
            for edge in tactr.gid_tactic[node]:
                tactics.add(edge.name)

    # Compute string edit distances
    dict_kern_str_dists = {}
    dict_mid_str_dists = {}
    dict_kern_str = {}
    dict_mid_str = {}
    for _, gid, _, _, ctx, (concl_kdx, concl_mdx), tac in tactr.bfs_traverse():
        kern_concl_str = dict_kern_str.setdefault(concl_kdx, kern2str(tactr, concl_kdx))
        mid_concl_str = dict_mid_str.setdefault(concl_mdx, mid2str(tactr, concl_mdx))

        for _, ty_kdx, ty_mdx in ctx:
            if (concl_kdx, ty_kdx) not in dict_kern_str_dists:
                kern_ty_str = dict_kern_str.setdefault(ty_kdx, kern2str(tactr, ty_kdx))
                dict_kern_str_dists[(concl_kdx, ty_kdx)] = string_edit_dist(kern_concl_str, kern_ty_str)

            if (concl_mdx, ty_mdx) not in dict_mid_str_dists:
                mid_ty_str = dict_mid_str.setdefault(ty_mdx, mid2str(tactr, ty_mdx))
                dict_mid_str_dists[(concl_mdx, ty_mdx)] = string_edit_dist(mid_concl_str, mid_ty_str)

    for _, gid, _, _, ctx, (concl_kdx, concl_mdx), tac in tactr.bfs_traverse():
        tacst = gid, ctx, (concl_kdx, concl_mdx), tac
        tac_bin = _tac_bin(tac)

        pt = TacStPt(tactr, tacst, subtr_size[gid], tac_bin, dict_kern_str_dists, dict_mid_str_dists)

        data.append(pt)

    result = (data, tactics)
    with open('tactr_pts/%s.pickle' % tactr_id, 'wb') as f:
        pickle.dump(result, f)
    print("Done {}".format(tactr_id))


# -------------------------------------------------
# Tactic States Dataset

class TacStPt(object):
    def __init__(self, tactr, tacst, subtr_size, tac_bin, dict_kern_str_dists, dict_mid_str_dists, f_feature=True):
        self.tactr = tactr
        self.tacst = tacst
        self.subtr_size = subtr_size
        self.tac_bin = tac_bin
        self._subtr_bin()

        # Features
        self._kern_size()
        self._mid_size()
        self._mid_noimp_size()
        self._ctx_len()
        if f_feature:
            # NOTE(deh): very slow
            # self._tree_edit_dist()
            self._string_edit_dist(dict_kern_str_dists, dict_mid_str_dists)

    # Prepares
    def _subtr_bin(self):
        if self.subtr_size < 5:
            self.subtr_bin = 0
        elif self.subtr_size < 20:
            self.subtr_bin = 1
        else:
            self.subtr_bin = 2

    def _kern_size(self):
        _, ctx, (concl_kdx, _), _ = self.tacst
        sc = SizeConstr(self.tactr.decoder.decoded)
        concl_size = sc.decode_size(concl_kdx)
        ctx_size = 0
        for _, kdx, _ in ctx:
            ctx_size += sc.decode_size(kdx)

        self.kern_concl_size = concl_size
        self.kern_ctx_size = ctx_size
        self.kern_size = concl_size + ctx_size

    def _mid_size(self):
        _, ctx, (_, concl_mdx), _ = self.tacst
        sgc = SizeGlobConstr(self.tactr.mid_decoder.decoded, f_cntiarg=True)
        concl_size = sgc.decode_size(concl_mdx)
        ctx_size = 0
        for _, _, mdx in ctx:
            ctx_size += sgc.decode_size(mdx)

        self.mid_concl_size = concl_size
        self.mid_ctx_size = ctx_size
        self.mid_size = concl_size + ctx_size

    def _mid_noimp_size(self):
        _, ctx, (_, concl_mdx), _ = self.tacst
        sgc = SizeGlobConstr(self.tactr.mid_decoder.decoded, f_cntiarg=False)
        concl_size = sgc.decode_size(concl_mdx)
        ctx_size = 0
        for _, _, mdx in ctx:
            ctx_size += sgc.decode_size(mdx)

        self.mid_noimp_concl_size = concl_size
        self.mid_noimp_ctx_size = ctx_size
        self.mid_noimp_size = concl_size + ctx_size

    def _ctx_len(self):
        _, ctx, (_, _), _ = self.tacst
        self.len_ctx = len(ctx)

    def _tree_edit_dist(self):
        _, ctx, (concl_kdx, concl_mdx), _ = self.tacst

        kern_concl_tr = kern2tr(self.tactr, concl_kdx)
        mid_concl_tr = mid2tr(self.tactr, concl_mdx)
        kern_dists = []
        mid_dists = []
        for _, ty_kdx, ty_mdx in ctx:
            kern_ty_tr = kern2tr(self.tactr, ty_kdx)
            kern_dists += [tree_edit_dist(kern_concl_tr, kern_ty_tr)]

            mid_ty_tr = mid2tr(self.tactr, ty_mdx)
            mid_dists += [tree_edit_dist(mid_concl_tr, mid_ty_tr)]

        # Set largest distances first
        sorted(kern_dists)
        sorted(mid_dists)

        # All distances, smallest first
        self.kern_tr_dists = kern_dists
        self.mid_tr_dists = mid_dists
        self.mid_noimp_tr_dists = mid_dists

    def _string_edit_dist(self, dict_kern_str_dists, dict_mid_str_dists):
        _, ctx, (concl_kdx, concl_mdx), _ = self.tacst

        kern_concl_str = kern2str(self.tactr, concl_kdx)
        mid_concl_str = mid2str(self.tactr, concl_mdx)

        kern_dists = [len(kern_concl_str)]
        mid_dists = [len(mid_concl_str)]
        for _, ty_kdx, ty_mdx in ctx:
            kern_dists += [dict_kern_str_dists[(concl_kdx, ty_kdx)]]
            mid_dists += [dict_mid_str_dists[(concl_mdx, ty_mdx)]]

        # All distance, smallest first
        kern_dists = sorted(kern_dists)
        mid_dists = sorted(mid_dists)
        self.kern_str_dists = kern_dists
        self.mid_str_dists = mid_dists
        self.mid_noimp_str_dists = mid_dists

        # Top-1
        self.kern_str_dist = self.kern_str_dists[0]
        self.mid_str_dist = self.mid_str_dists[0]
        self.mid_noimp_str_dist = self.mid_noimp_str_dists[0]

    # Getter's
    def kern_tacst(self):
        gid, ctx, (concl_kdx, _), tac = self.tacst
        return gid, [(ty, kdx) for ty, kdx, _ in ctx], concl_kdx, tac

    def mid_tacst(self):
        gid, ctx, (_, concl_mdx), tac = self.tacst
        return gid, [(ty, mdx) for ty, _, mdx in ctx], concl_mdx, tac


class SizeSubTr(object):
    def __init__(self, tactr):
        self.tactr = tactr

    def size(self, node):
        children = list(self.tactr.graph.successors(node))
        size = 1
        for child in children:
            # TODO(deh): ignore self-edges
            if child != node:
                size += self.size(child)
        return size


if __name__ == "__main__":
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-l", "--load", default="tactr.pickle",
                           type=str, help="Pickle file to load")
    argparser.add_argument("-p", "--tacst", default="tacst.pickle",
                           type=str, help="Pickle file to save to")
    argparser.add_argument("-v", "--verbose", action="store_true")
    argparser.add_argument("--simprw", action="store_true")
    args = argparser.parse_args()

    # with open(args.load, 'rb') as f:
    #     print("Loading {}...".format(args.load))
    #     tactrs = pickle.load(f)
    #
    # for tactr_id, tactr in enumerate(tactrs):
    #     with open("tactrs/%s.pickle" % tactr_id, 'wb') as f:
    #         pickle.dump(tactr, f)
    #
    # exit()
    print("Creating dataset {}...".format(args.load))

    with Pool() as p:
        p.map(mk_tactr, list(range(1602)))

    # if args.simprw:
    #     tactics_equiv = [["intros"], ["surgery"], ["<coretactics::reflexivity@0>"]]
    #     tacst = TacStDataset(tactics_equiv, tactrs)
    # else:
    #     tacst = TacStDataset(TACTICS_EQUIV, tactrs)
    # if args.simprw:
    #     tacst_dataset = tacst.split_by_lemma(f_balance=False, num_train=400, num_test=50)
    # else:
    #     tacst_dataset = tacst.split_by_lemma()
    #
    # kern_embed_tokens = EmbedTokens(f_mid=False)
    # kern_embed_tokens.tokenize_tactrs(tactrs)
    # kern_tokens_to_idx = kern_embed_tokens.tokens_to_idx()
    #
    # mid_embed_tokens = EmbedTokens(f_mid=True)
    # mid_embed_tokens.tokenize_tactrs(tactrs)
    # mid_tokens_to_idx = mid_embed_tokens.tokens_to_idx()
    #
    # with open(args.tacst, 'wb') as f:
    #     pickle.dump((tacst_dataset, kern_tokens_to_idx, mid_tokens_to_idx), f)
    #
    # if args.verbose:
    #     with open(args.tacst, 'rb') as f:
    #         dataset, _ = pickle.load(f)
    #         for tactr_id, pt in dataset:
    #             print(tactr_id, pt)

# class TacPredPt(object):
#     def __init__(self, tacst):
#         # (gid, ctx, concl_idx, tac)
#         self.tacst = tacst
#
#
# def tacst_to_tacpred(dataset):
#     acc = []
#     for tactrid, pt in dataset:
#         acc += [(tactrid, TacPredPt(pt.tacst))]
#     return acc


# def one_hot_lid(ctx, lids):
#     vec = [0 for _ in ctx]
#     for idx, (ident, _) in enumerate(ctx):
#         if ident in lids:
#             vec[idx] = 1
#             break
#     return vec
#
#
# def one_hot_gid(tokens_to_idx, gids):
#     vec = [0 for _ in tokens_to_idx]
#     for idx, (k, v) in enumerate(tokens_to_idx.items()):
#         if k in gids:
#             vec[idx] = 1
#             break
#     return vec
