import argparse
import networkx as nx
import numpy as np

from lex_raw import *
from parse_tacst2 import *
from build_tactr2 import *


class Visualize(object):
    def __init__(self):
        self.stats = {}

    def log_stats(self):
        for k, v in self.stats.items():
            print("{:16s}; {:2d}; {:2d}; {:2d}; {:8d}".format(k[0], k[1], k[2], k[3], v))

    def _log_weird_tac(self, lemma, tac):
        kind, nbf, nbod, naf = tac.base_stats()

        if nbf == naf and nbf == nbod:
            pass
        elif nbf == naf and nbod == 0:
            pass
        elif naf % nbf == 0 and nbf == nbod:
            pass
        elif naf == 1 and nbf == nbod:
            pass

        elif nbf == nbod and naf == 1:
            print("WEIRD1({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac))
        elif nbf > 1 and nbod == 1 and naf == 1:
            print("WEIRD2({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac))
        elif nbf == nbod and naf == 0:
            print("WEIRD3({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac))
        elif nbf == nbod and naf > nbf:
            print("WEIRD4({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac))
        elif nbf == nbod and nbf > naf:
            print("WEIRD5({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac))
        elif nbf == naf and nbod == 1:
            print("WEIRD6({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac))
        elif nbf != naf and nbod == 1:
            print("WEIRD7({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac))

    def visualize_lemma(self, lemma):
        # Internal
        print("------------------------------------------------")
        print("Visualizing lemma: {}".format(lemma.name))
        
        # [TacStDecl] tokens to [RawTac]
        tr_parser = TacTreeParser(lemma, f_log=False)
        tacs = tr_parser.parse_tactree()
        print(">>>>>>>>>>>>>>>>>>>>")
        for tac in tacs:
            print(tac.pp())
        print("<<<<<<<<<<<<<<<<<<<<")

        # Compute some stats on RawTacs
        for tac in tacs:
            stats = tac.rec_stats()
            merge_hist(self.stats, stats)

            # Check for "weird" RawTacs
            for tac_p in tac.postorder():
                self._log_weird_tac(lemma, tac_p)

        # tp_builder = TacPathBuilder(tacs, f_log=True)
        # tacs_p = tp_builder.build_tacpath()
        # for tac in tacs_p:
        #     print(tac.pp())

        # tr_builder = TacTreeBuilder(tacs, False)
        # tr_builder.build_tactree()
        # tr_builder.show()
    
    def visualize_file(self, file):
        print("==================================================")
        print("Visualizing file: {}".format(file))

        ts_parser = TacStParser(file, f_log=False)
        while not ts_parser.exhausted:
            lemma = ts_parser.parse_lemma()
            self.visualize_lemma(lemma)


if __name__ == "__main__":
    # Set up command line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("file",
                           help="Enter the file you want to visualize.")
    args = argparser.parse_args()

    files = ["../data/odd-order/BGsection1.v.dump",
             "../data/odd-order/BGsection2.v.dump",
             "../data/odd-order/BGsection3.v.dump",
             "../data/odd-order/BGsection4.v.dump",
             "../data/odd-order/BGsection5.v.dump",
             "../data/odd-order/BGsection6.v.dump",
             "../data/odd-order/BGsection7.v.dump",
             "../data/odd-order/BGsection8.v.dump",
             "../data/odd-order/BGsection9.v.dump",
             "../data/odd-order/BGsection10.v.dump",
             "../data/odd-order/BGsection11.v.dump",
             "../data/odd-order/BGsection12.v.dump",
             "../data/odd-order/BGsection13.v.dump",
             "../data/odd-order/BGsection14.v.dump",
             "../data/odd-order/BGsection15.v.dump",
             "../data/odd-order/BGsection16.v.dump",
             "../data/odd-order/BGappendixAB.v.dump",
             "../data/odd-order/BGappendixC.v.dump",
             "../data/odd-order/PFsection1.v.dump",
             "../data/odd-order/PFsection2.v.dump",
             "../data/odd-order/PFsection3.v.dump",
             "../data/odd-order/PFsection4.v.dump",
             "../data/odd-order/PFsection5.v.dump",
             "../data/odd-order/PFsection6.v.dump",
             "../data/odd-order/PFsection7.v.dump",
             "../data/odd-order/PFsection8.v.dump",
             "../data/odd-order/PFsection9.v.dump",
             "../data/odd-order/PFsection10.v.dump",
             "../data/odd-order/PFsection11.v.dump",
             "../data/odd-order/PFsection12.v.dump",
             "../data/odd-order/PFsection13.v.dump",
             "../data/odd-order/PFsection14.v.dump"]
    
    if args.file == "all":
        vis = Visualize()
        for file in files:
            vis.visualize_file(file)
            vis.log_stats()
    else:
        vis = Visualize()
        vis.visualize_file(args.file)
        vis.log_stats()


# -------------------------------------------------
# Compute statistics

"""
class TacStStats(object):
    def __init__(self, root, tree):
        self.root = root
        self.tree = tree

    def cnt_tac_sts(self):
        return len(self.tree.nodes)

    def cnt_have(self):
        cnt = 0
        for decl in self.tree.nodes:
            if decl.hdr.tac == "<ssreflect_plugin::ssrhave@0> $fwd":
                cnt += 1
            else:
                print("Skipping", decl)
        return cnt

    def cnt_term_tac_sts(self):
        # TODO(deh): broken
        term = []
        for node in self.tree.nodes:
            if len(self.tree.adj[node]) == 0:
                term += [node]
        return term

    def foobar(self):
        return nx.algorithms.simple_paths.all_simple_paths(self.tree, root=self.root)


def basic_have_stats(lemmas):
    total = 0
    haves = 0
    pfsizes = []
    for lemma in lemmas:
        size = 0
        for decl in lemma.decls:
            if decl.hdr.mode == TOK_BEFORE:
                if decl.hdr.tac == "<ssreflect_plugin::ssrhave@0> $fwd":
                    haves += 1
                total += 1
                size += 1
        pfsizes += [size]
    return (len(lemmas), haves, total, 1.0 * haves / (total + 1),
            np.mean(pfsizes))
"""

"""
def hist_after_notation(tacs):
    it = MyIter(tacs)
    hist = {TacKind.NAME: 0,
            TacKind.ATOMIC: 0,
            TacKind.NOTATION: 0,
            TacKind.ML: 0,
            "NO_BODY": 0}
    sizes = {}
    notation_body = 0
    total = 0
    while it.has_next():
        tac = next(it)
        size = len(tac.bods)
        if len(tac.bods) in sizes:
            sizes[size] += 1
        else:
            sizes[size] = 1

        if tac.kind == TacKind.NOTATION:
            if len(tac.bods) > 0:
                notation_body += 1
                if len(tac.bods[0]) > 0:
                    cnt[tac.bods[0][0].kind] += 1
                else:
                    cnt["EMPTY"] += 1
            else:
                total += 1
                hist["NO_BODY"] += 1

    #print("CNT:", cnt)
    if cnt[TacKind.NAME] > 0 or \
       cnt[TacKind.ATOMIC] > 0 or \
       cnt[TacKind.NOTATION] > 0:
        return True
    else:
        return False
"""