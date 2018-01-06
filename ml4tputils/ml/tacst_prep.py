import argparse
import os.path as op
import pickle

from recon.embed_tokens import EmbedTokens

"""
[Note]

Prepare data for:
1. Position evaluation
2. Tactic prediction (can just truncate)
"""


# -------------------------------------------------
# Position Evaluation Dataset

class PosEvalPt(object):
    def __init__(self, gid, ctx, concl_idx, tac, subtr_size):
        self.tacst = (gid, ctx, concl_idx, tac)
        self.subtr_size = subtr_size
        if subtr_size < 5:
            self.subtr_bin = 0
        elif subtr_size < 20:
            self.subtr_bin = 1
        else:
            self.subtr_bin = 2


class SizeSubTr(object):
    def __init__(self, tactr):
        self.tactr = tactr

    def size(self, node):
        children = list(self.tactr.graph.successors(node))
        if children:
            size = 0
            for child in children:
                # TODO(deh): ignore self-edges
                if child != node:
                    size += self.size(child)
            return size
        else:
            return 1


class PosEvalDataset(object):
    def __init__(self, tactrs):
        self.tactrs = tactrs
        self.data = []

    def mk_tactrs(self):
        for tactr_id, tactr in enumerate(self.tactrs):
            self.mk_tactr(tactr_id, tactr)
        return self.data

    def mk_tactr(self, tactr_id, tactr):
        print("Working on ({}/{}) {}".format(tactr_id, len(self.tactrs), tactr.name))
        subtr_size = {}
        size_subtr = SizeSubTr(tactr)
        for node in tactr.graph.nodes():
            subtr_size[node.gid] = size_subtr.size(node)
        for _, gid, _, _, ctx, concl_idx, tac in tactr.bfs_traverse():
            self.data += [(tactr_id, PosEvalPt(gid, ctx, concl_idx, tac, subtr_size[gid]))]
        return self.data

    def split_by_lemma(self, train=80, valid=10, test=10):
        # TODO(deh): Add functionality for Test/Train/Split
        if train + valid + test != 100:
            raise NameError("Train={}, Valid={}, Test={} must sum to 100".format(train, valid, test))


# -------------------------------------------------
# Tactic Prediction

class TacPredPt(object):
    def __init__(self, tacst):
        # (gid, ctx, concl_idx, tac)
        self.tacst = tacst


def poseval_to_tacpred(dataset):
    acc = []
    for tactrid, pt in dataset:
        acc += [(tactrid, TacPredPt(pt.tacst))]
    return acc


if __name__ == "__main__":
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-l", "--load", default="tactr.pickle",
                           type=str, help="Pickle file to load")
    argparser.add_argument("-p", "--poseval", default="poseval.pickle",
                           type=str, help="Pickle file to save to")
    argparser.add_argument("-t", "--tacpred", default="tacpred.pickle",
                           type=str, help="Pickle file to save to")
    argparser.add_argument("-v", "--verbose", action="store_true")
    args = argparser.parse_args()

    with open(args.load, 'rb') as f:
        print("Loading {}...".format(args.load))
        tactrs = pickle.load(f)

    print("Creating dataset {}...".format(args.load))
    poseval = PosEvalDataset(tactrs)
    poseval_dataset = poseval.mk_tactrs()

    embed_tokens = EmbedTokens()
    embed_tokens.tokenize_tactrs(tactrs)
    tokens_to_idx = embed_tokens.tokens_to_idx()

    with open(args.poseval, 'wb') as f:
        pickle.dump((poseval_dataset, tokens_to_idx), f)

    tacpred_dataset = poseval_to_tacpred(poseval_dataset)
    with open(args.tacpred, 'wb') as f:
        pickle.dump(tacpred_dataset, f)

    if args.verbose:
        with open(args.poseval, 'rb') as f:
            dataset, _ = pickle.load(f)
            for tactr_id, pt in dataset:
                print(tactr_id, pt)

        with open(args.tacpred, 'rb') as f:
            dataset, _ = pickle.load(f)
            for tactr_id, pt in dataset:
                print(tactr_id, pt)
