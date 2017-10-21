import argparse
import networkx as nx
import numpy as np

from build_tactr import *
from lib.myiter import MyIter
from parse_raw import *
from parse_tacst import *


# -------------------------------------------------
# Compute statistics

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


def visualize(file):
    ts_parser = TacStParser(file, f_log=False)
    lemmas = ts_parser.parse_file()
    # cleanup_lemmas(lemmas)

    cnt = 0
    for lemma in lemmas:
        cnt += 1
        # lemma_p = cleanup_lemma(lemma)

        it = MyIter(lemma.decls)
        tr_parser = TacTreeParser(lemma)
        tacs = tr_parser.parse_tactree()
        for tac in tacs:
            print(tac)
            # print("HERE", before, after)
        tr_builder = TacTreeBuilder(tacs, False)
        print("")
        print("")
        print("")
        tr_builder.build_tactree()
        tr_builder.show()

        """
        root, tree = recon_tac_tree(lemma_p, f_draw=True)
        ts_stats = TacStStats(root, tree)
        print("# tactic states: {}".format(ts_stats.cnt_tac_sts()))
        print("# have: {}".format(ts_stats.cnt_have()))
        print("chains: {}".format(ts_stats.cnt_term_tac_sts()))
        """


if __name__ == "__main__":
    # Set up command line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("file",
                           help="Enter the file you want to visualize.")
    args = argparser.parse_args()

    visualize(args.file)
