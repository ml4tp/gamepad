import argparse
import numpy as np
import pickle

from coq.tactics import TACTICS_EQUIV
from coq.constr_util import SizeConstr
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
# Position Evaluation Dataset

class PosEvalPt(object):
    def __init__(self, gid, ctx, concl_idx, tac, tacst_size, subtr_size, tac_bin):
        self.tacst = (gid, ctx, concl_idx, tac)
        self.tacst_size = tacst_size
        self.subtr_size = subtr_size
        if subtr_size < 5:
            self.subtr_bin = 0
        elif subtr_size < 20:
            self.subtr_bin = 1
        else:
            self.subtr_bin = 2
        self.tac_bin = tac_bin
        # for idx, (tac_p, _) in enumerate(TACTIC_INFO):
        #     if tac[-1].name.startswith(tac_p):
        #         self.tac_bin = idx


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


class Dataset(object):
    def __init__(self, train, val, test):
        self.train = train
        self.val = val
        self.test = test


class PosEvalDataset(object):
    def __init__(self, tactics_equiv, tactrs):
        self.tactrs = tactrs
        self.data = {}
        self.tactics = set()
        self.tactics_equiv = tactics_equiv
        self.tac_hist = [0 for _ in tactics_equiv]

    def mk_tactrs(self):
        self.data = {}
        for tactr_id, tactr in enumerate(self.tactrs):
            self.mk_tactr(tactr_id, tactr)
        print("TACTICS", self.tactics)
        print("TACHIST")
        for idx, eq_tacs in enumerate(self.tactics_equiv):
            print("TAC", eq_tacs[0], self.tac_hist[idx])
        # assert False

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
            # for k, v in tactr.gid_tactic.items():
            #     print("HERE", k, v)
            if node in tactr.gid_tactic:
                for edge in tactr.gid_tactic[node]:
                    self.tactics.add(edge.name)
        # print("TACTICS", self.tactics)
        sce = SizeConstr(tactr.decoder.decoded)
        tacst_size = 0
        for _, gid, _, _, ctx, concl_idx, tac in tactr.bfs_traverse():
            tacst_size += sce.decode_size(concl_idx)
            for ident, idx in ctx:
                tacst_size += sce.decode_size(idx)

            tac_bin = self.tac_bin(tac)
            pt = PosEvalPt(gid, ctx, concl_idx, tac, tacst_size, subtr_size[gid], tac_bin)
            self.data[tactr_id].append(pt)
            self.tac_hist[pt.tac_bin] += 1

    def split_by_lemma(self, f_rec=True, num_train=None, num_test=None):
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
        if f_rec:
            for p in ps:
                if (p - 64.5)**2 > (66 - 64.5)**2:
                    return self.split_by_lemma()
        return Dataset(data_train, data_val, data_test)


if __name__ == "__main__":
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-l", "--load", default="tactr.pickle",
                           type=str, help="Pickle file to load")
    argparser.add_argument("-p", "--poseval", default="poseval.pickle",
                           type=str, help="Pickle file to save to")
    argparser.add_argument("-t", "--tacpred", default="tacpred.pickle",
                           type=str, help="Pickle file to save to")
    argparser.add_argument("-v", "--verbose", action="store_true")
    argparser.add_argument("--simprw", action="store_true")
    args = argparser.parse_args()

    with open(args.load, 'rb') as f:
        print("Loading {}...".format(args.load))
        tactrs = pickle.load(f)

    print("Creating dataset {}...".format(args.load))

    if args.simprw:
        tactics_equiv = [["intros"], ["surgery"], ["<coretactics::reflexivity@0>"]]
        poseval = PosEvalDataset(tactics_equiv, tactrs)
    else:
        poseval = PosEvalDataset(TACTICS_EQUIV, tactrs)
    if args.simprw:
        poseval_dataset = poseval.split_by_lemma(f_rec=False, num_train=400, num_test=50)
    else:
        poseval_dataset = poseval.split_by_lemma()

    embed_tokens = EmbedTokens()
    embed_tokens.tokenize_tactrs(tactrs)
    tokens_to_idx = embed_tokens.tokens_to_idx()

    with open(args.poseval, 'wb') as f:
        pickle.dump((poseval_dataset, tokens_to_idx), f)

    if args.verbose:
        with open(args.poseval, 'rb') as f:
            dataset, _ = pickle.load(f)
            for tactr_id, pt in dataset:
                print(tactr_id, pt)

        with open(args.tacpred, 'rb') as f:
            dataset, _ = pickle.load(f)
            for tactr_id, pt in dataset:
                print(tactr_id, pt)


# class TacPredPt(object):
#     def __init__(self, tacst):
#         # (gid, ctx, concl_idx, tac)
#         self.tacst = tacst
#
#
# def poseval_to_tacpred(dataset):
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
