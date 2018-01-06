import argparse
import os.path as op
import pickle

"""
[Note]

Create data of the form

LemId -> (TacSt, Int)
"""


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


class TacStInfo(object):
    def __init__(self, gid, ctx, concl_idx, tac, subtr_size):
        self.gid = gid
        self.ctx = ctx
        self.concl_idx = concl_idx
        self.tac = tac
        self.subtr_size = subtr_size


class TacStDistDataset(object):
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
            self.data += [(tactr_id, TacStInfo(gid, ctx, concl_idx, tac, subtr_size[gid]))]
        return self.data

    def split_by_lemma(self, train=80, valid=10, test=10):
        # TODO(deh): Add functionality for Test/Train/Split
        if train + valid + test != 100:
            raise NameError("Train={}, Valid={}, Test={} must sum to 100".format(train, valid, test))


if __name__ == "__main__":
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-l", "--load", default="tactr.pickle",
                           type=str, help="Pickle file to load")
    argparser.add_argument("-o", "--out", default="tacstdist.pickle",
                           type=str, help="Pickle file to save to")
    argparser.add_argument("-v", "--verbose", action="store_true")
    args = argparser.parse_args()

    with open(args.load, 'rb') as f:
        print("Loading {}...".format(args.load))
        tactrs = pickle.load(f)

    print("Creating dataset {}...".format(args.load))
    foobar = TacStDistDataset(tactrs)
    dataset = foobar.mk_tactrs()

    with open(args.out, 'wb') as f:
        pickle.dump(dataset, f)

    if args.verbose:
        with open(args.out, 'rb') as f:
            dataset = pickle.load(f)
            for tactr_id, info in dataset:
                print(tactr_id, info)
