import argparse
import networkx as nx
import numpy as np
import pickle

from lex_raw import *
from parse_tacst2 import *
from build_tactr3 import *
from raw_stats import *


class Visualize(object):
    def __init__(self):
        self.stats = {}
        self.rawstats = RawStats(False)
        self.num_lemmas = 0
        self.failed = []

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
            # NOTE(deh): only seems to come from top-level tac
            print("WEIRD1({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac.pp()))
        elif nbf > 1 and nbod == 1 and naf == 1:
            # WEIRD2(2, 1, 1)@rank_eigenspaces_quasi_homocyclic
            # [[[by (ssrhintarg)(640; B(3003,by (ssrhintarg),
            # (./BGsection2.v,26756,26819),576))]]]
            print("WEIRD2({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac.pp()))
        elif nbf == nbod and naf == 0:
            # NOTE(deh): only seems to come from top-level tac
            print("WEIRD3({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac.pp()))
        elif nbf == nbod and naf > nbf:
            # WEIRD4(TacKind.NOTATION, 2, 2, 3)
            # @cyclic_Sylow_tiVsub_der1 
            # [[[rewrite (ssrrwargs) (ssrclauses)(24; 
            # B(783,rewrite (ssrrwargs) (ssrclauses),(./BGsection1.v,44505,44534),22),
            # B(784,rewrite (ssrrwargs) (ssrclauses),(./BGsection1.v,44505,44534),22))]]]
            #
            # apply; rewrite
            # seems that you can use contiguous goal id to reconstruct
            print("WEIRD4({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac.pp()))
        elif nbf == nbod and nbf > naf:
            # WEIRD5(3, 3, 2)@rank_abs_irr_dvd_solvable
            # [[[by (ssrhintarg)(550; B(2298,by (ssrhintarg)
            # (./BGsection2.v,9702,9741),429))]]]
            print("WEIRD5({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac.pp()))
        elif nbf == naf and nbod == 1:
            # WEIRD6(2, 1, 2)@sigma_decomposition_dichotomy
            # [[[have (ssrhavefwdwbinders)(181; B(1660,have (ssrhavefwdwbinders),
            # (./BGsection14.v,62084,62144),150))]]]
            print("WEIRD6({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac.pp()))
        elif nbf != naf and nbod == 1:
            # WEIRD7(TacKind.ML, 2, 1, 4)@logn_quotient_cent_abelem
            print("WEIRD7({}, {}, {}, {})@{} [[[{}]]]".format(
                kind, nbf, nbod, naf, lemma.name, tac.pp()))

    def visualize_lemma(self, file, lemma):
        # Internal
        print("------------------------------------------------")
        print("Visualizing lemma: {}".format(lemma.name))
        self.num_lemmas += 1

        # [TacStDecl] tokens to [RawTac]
        tr_parser = TacTreeParser(lemma, f_log=False)
        tacs = tr_parser.parse_tactree()

        """
        print(">>>>>>>>>>>>>>>>>>>>")
        for tac in tacs:
            print(tac.pp())
        print("<<<<<<<<<<<<<<<<<<<<")
        """

        # Compute statistics
        # self.rawstats.stats_tacs(lemma, tacs)

        """
        # Compute some stats on RawTacs
        for tac in tacs:
            stats = tac.rec_stats()
            merge_hist(self.stats, stats)

            # Check for "weird" RawTacs
            for tac_p in tac.postorder():
                self._log_weird_tac(lemma, tac_p)
        """

        tr_builder = TacTreeBuilder(tacs, False)
        tr_builder.build_tacs()
        if not tr_builder.check_success():
            self.failed += [(file, lemma.name)]
        # tr_builder.show()
    
    def visualize_file(self, file):
        print("==================================================")
        print("Visualizing file: {}".format(file))

        ts_parser = TacStParser(file, f_log=False)
        while not ts_parser.exhausted:
            lemma = ts_parser.parse_lemma()
            self.visualize_lemma(file, lemma)
        # self.pickle_save(file)


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
            #vis.log_stats()
        vis.rawstats.log_notok()
        vis.rawstats.log_mlstats()
        print("Total lemmas: {}".format(vis.num_lemmas))
        print("Failed lemmas: {}".format(len(vis.failed)))
        print("FAILED", vis.failed)
    else:
        vis = Visualize()
        vis.visualize_file(args.file)
        #vis.log_stats()
        vis.rawstats.log_notok()
        vis.rawstats.log_mlstats()
        print("Total lemmas: {}".format(vis.num_lemmas))
        print("Failed lemmas: {}".format(len(vis.failed)))
        print("FAILED", vis.failed)
