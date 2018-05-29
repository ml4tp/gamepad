import argparse
import numpy as np
import pickle

from coq.tactics import TACTICS_EQUIV
from coq.constr_util import SizeConstr
from coq.glob_constr_util import SizeGlobConstr
from lib.myedit import *
from recon.embed_tokens import EmbedTokens


"""
[Note]

Prepare data for:
1. Position evaluation
2. Tactic prediction (can just truncate)
"""


# -------------------------------------------------
# Seeding

np.random.seed(7)


# -------------------------------------------------
# Tactic States Dataset
class TacStPt(object):
    def __init__(self, tactr, tacst, subtr_size, tac_bin, dict_kern_str_dists, dict_mid_str_dists,
                 f_feature=True, f_edit_feature=True):
        self.tactr = tactr
        self.tacst = tacst
        self.subtr_size = subtr_size
        self.tac_bin = tac_bin
        self._subtr_bin()

        # Features
        if f_feature:
            import sys
            sys.setrecursionlimit(1500)
            self._kern_size()
            self._mid_size()
            self._mid_noimp_size()
            self._ctx_len()
            if f_edit_feature:
                # TOO SLOW
                # self._tree_edit_dist()
                self._string_edit_dist(dict_kern_str_dists, dict_mid_str_dists)

        else:
            # Use for creating artificial tacst points for testing
            self.kern_concl_size = 0
            self.kern_ctx_size = 0
            self.kern_size = 0
            self.mid_concl_size = 0
            self.mid_ctx_size = 0
            self.mid_size = 0
            self.mid_noimp_concl_size = 0
            self.mid_noimp_ctx_size = 0
            self.mid_noimp_size = 0
            self.len_ctx = 0

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
        kern_dists = sorted(kern_dists)
        mid_dists = sorted(mid_dists)

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
            # NOTE(deh): ignore self-edges
            if child != node:
                size += self.size(child)
        return size


class Dataset(object):
    def __init__(self, train, val, test):
        self.train = train
        self.val = val
        self.test = test


class TacStDataset(object):
    def __init__(self, tactics_equiv, tactrs, args):
        self.tactrs = tactrs
        self.tactics = set()
        self.tactics_equiv = tactics_equiv
        self.tac_hist = [0 for _ in tactics_equiv]
        self.args = args

        self.data = {}
        self.sum_tacst_size = 0
        self.sum_tacst_mid_size = 0
        self.sum_tacst_mid_noimp_size = 0
        self.num_tacst = 0

    def mk_tactrs(self):
        self.data = {}
        self.sum_tacst_size = 0
        self.sum_tacst_mid_size = 0
        self.sum_tacst_mid_noimp_size = 0
        self.num_tacst = 0
        for tactr_id, tactr in enumerate(self.tactrs):
            self.mk_tactr(tactr_id, tactr)
        print("tacsts {} avg_size {} avg_mid_size {} avg_mid_noimp_size {}".format(self.num_tacst, self.sum_tacst_size / self.num_tacst, self.sum_tacst_mid_size / self.num_tacst, self.sum_tacst_mid_noimp_size / self.num_tacst))
        print("TACTICS", self.tactics)
        print("TACHIST")
        for idx, eq_tacs in enumerate(self.tactics_equiv):
            print("TAC", eq_tacs[0], self.tac_hist[idx])

    def tac_bin(self, tac):
        for idx, eq_tacs in enumerate(self.tactics_equiv):
            for tac_p in eq_tacs:
                if tac[-1].name.startswith(tac_p):
                    return idx
        raise NameError("Not assigned to bin", tac[-1].name)

    def mk_tactr(self, tactr_id, tactr):
        print("Working on ({}/{}) {}".format(tactr_id, len(self.tactrs), tactr.name))
        self.data[tactr_id] = []
        subtr_size = {}
        size_subtr = SizeSubTr(tactr)
        for node in tactr.graph.nodes():
            subtr_size[node.gid] = size_subtr.size(node)
            if node in tactr.gid_tactic:
                for edge in tactr.gid_tactic[node]:
                    self.tactics.add(edge.name)

        # Compute string edit distances
        dict_kern_str_dists = {}
        dict_mid_str_dists = {}
        dict_kern_str = {}
        dict_mid_str = {}
        if self.args.edit_features:
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
            tac_bin = self.tac_bin(tac)

            pt = TacStPt(tactr, tacst, subtr_size[gid], tac_bin, dict_kern_str_dists, dict_mid_str_dists, f_edit_feature=args.edit_features)

            self.data[tactr_id].append(pt)
            self.tac_hist[pt.tac_bin] += 1
            self.num_tacst += 1
            self.sum_tacst_size += pt.kern_size
            self.sum_tacst_mid_size += pt.mid_size
            self.sum_tacst_mid_noimp_size += pt.mid_noimp_size

    def split_by_lemma(self, f_balance=True, num_train=None, num_test=None):
        if self.data == {}:
            self.mk_tactrs()

        tlen = len(self.tactrs)
        perm = np.random.permutation(tlen)
        if num_train is None and num_test is None:
            strain, sval, stest = 0.8, 0.1, 0.1
            s1 = int(tlen * strain) + 1
            s2 = s1 + int(tlen * sval)
            train, val, test = perm[:s1], perm[s1:s2], perm[s2:]
        else:
            s1 = num_train
            s2 = num_train + num_test
            train, val, test = perm[:s1], perm[s1:s2], perm[s2:]
        if len(train) + len(val) + len(test) != tlen:
            raise NameError("Train={}, Valid={}, Test={} must sum to {}".format(len(train), len(val), len(test), tlen))

        def f(ids):
            pts = []
            for tactr_id in ids:
                for pt in self.data[tactr_id]:
                    pts.append((tactr_id, pt))
            return pts

        data_train, data_val, data_test = f(train), f(val), f(test)
        print("Split Train={} Valid={} Test={}".format(len(train), len(val), len(test)))
        print("Split Tactrs Train={} Valid={} Test={}".format(len(data_train), len(data_val), len(data_test)))
        ps = [len(data_train) / len(train), len(data_val) / len(val), len(data_test) / len(test)]
        print("ps ", ps)
        if f_balance:
            # Balance to make sure that splits are roughly equal in numebr of tacsts too
            mean = sum(ps) / len(ps)
            threshold = 1.5**2
            for p in ps:
                if (p - mean)**2 > threshold:
                    return self.split_by_lemma(f_balance, num_train, num_test)
        return Dataset(data_train, data_val, data_test)


if __name__ == "__main__":
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-l", "--load", default="tactr.pickle",
                           type=str, help="Pickle file to load")
    argparser.add_argument("-p", "--tacst", default="tacst.pickle",
                           type=str, help="Pickle file to save to")
    argparser.add_argument("-v", "--verbose", action="store_true")
    argparser.add_argument("--simprw", action="store_true")
    argparser.add_argument("--edit_features", action="store_true", help="Compute edit distance features")

    args = argparser.parse_args()

    with open(args.load, 'rb') as f:
        print("Loading {}...".format(args.load))
        tactrs = pickle.load(f)

    print("Creating dataset {}...".format(args.load))

    if args.simprw:
        tactics_equiv = [["intros"], ["surgery"], ["<coretactics::reflexivity@0>"]]
        tacst = TacStDataset(tactics_equiv, tactrs, args)
    else:
        tacst = TacStDataset(TACTICS_EQUIV, tactrs, args)
    if args.simprw:
        tacst_dataset = tacst.split_by_lemma(f_balance=False, num_train=400, num_test=50)
    else:
        tacst_dataset = tacst.split_by_lemma()

    kern_embed_tokens = EmbedTokens(f_mid=False)
    kern_embed_tokens.tokenize_tactrs(tactrs)
    kern_tokens_to_idx = kern_embed_tokens.tokens_to_idx()

    mid_embed_tokens = EmbedTokens(f_mid=True)
    mid_embed_tokens.tokenize_tactrs(tactrs)
    mid_tokens_to_idx = mid_embed_tokens.tokens_to_idx()

    with open(args.tacst, 'wb') as f:
        pickle.dump((tacst_dataset, kern_tokens_to_idx, mid_tokens_to_idx), f)

    if args.verbose:
        with open(args.tacst, 'rb') as f:
            dataset, _ = pickle.load(f)
            for tactr_id, pt in dataset:
                print(tactr_id, pt)
