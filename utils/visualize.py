import argparse
import networkx as nx
import numpy as np
import pickle

from lex_raw import *
from parse_tacst2 import *
from build_tactr3 import *
from raw_stats import *


class Visualize(object):
    def __init__(self, f_display=False, rawtac_file=None, tgtlem=None):
        assert isinstance(f_display, bool)
        assert (not rawtac_file or isinstance(rawtac_file, str))
        assert (not tgtlem or isinstance(tgtlem, str))

        # Internal book-keeping
        self.num_lemmas = 0
        self.failed = []

        # Display result?
        self.f_display = f_display

        # Target lemma?
        self.tgtlem = tgtlem
        self.abort = False

        # Compute stats?
        if rawtac_file:
            self.f_stats = True
        else:
            self.f_stats = False
        self.rawstats = RawStats(rawtac_file, False)

    def visualize_lemma(self, file, lemma):
        if self.tgtlem and self.tgtlem != lemma.name:
            return

        # Internal
        print("------------------------------------------------")
        print("Visualizing lemma: {}".format(lemma.name))
        self.num_lemmas += 1

        # [TacStDecl] tokens to [RawTac]
        tr_parser = TacTreeParser(lemma, f_log=False)
        tacs = tr_parser.parse_tactree()

        if self.tgtlem:
            print(">>>>>>>>>>>>>>>>>>>>")
            for tac in tacs:
                print(tac.pp())
            print("<<<<<<<<<<<<<<<<<<<<")

        # Compute statistics
        self.rawstats.stats_tacs(lemma, tacs)

        tr_builder = TacTreeBuilder(tacs, False)
        tr_builder.build_tacs()
        succ, ncc = tr_builder.check_success()
        if not succ:
            self.failed += [(file, lemma.name, ncc)]

        if self.f_display:
            tr_builder.show()

        if self.tgtlem:
            self.abort = True
    
    def visualize_file(self, file):
        print("==================================================")
        print("Visualizing file: {}".format(file))

        ts_parser = TacStParser(file, f_log=False)
        while not ts_parser.exhausted:
            lemma = ts_parser.parse_lemma()
            self.visualize_lemma(file, lemma)
            if self.abort:
                break


def record(file, vis):
    print("Total lemmas: {}".format(vis.num_lemmas))
    print("Failed lemmas: {}".format(len(vis.failed)))
    print("FAILED", vis.failed)
    with open(file, "w") as f:
        f.write("Total lemmas: {}\n".format(vis.num_lemmas))
        f.write("Failed lemmas: {}\n".format(len(vis.failed)))
        f.write("FAILED\n")
        for file, lemma, ncc in vis.failed:
            f.write("{}, {}, {}\n".format(file, lemma, ncc))


if __name__ == "__main__":
    # Set up command line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("file",
                           help="Enter the file you want to visualize.")
    argparser.add_argument("-d", "--display", action="store_true",
                           help="Display the tactic tree.")
    argparser.add_argument("-l", "--lemma", type=str,
                           help="Visualize a specific lemma by name.")
    argparser.add_argument("-o", "--output", default="recon.log", type=str,
                           help="Output file for reconstructing stats.")
    argparser.add_argument("-s", "--stats", default="rawtac.log", type=str,
                           help="Compute raw tactic statistics")
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
    
    # Create visualizer
    if args.lemma:
        vis = Visualize(f_display=args.display, rawtac_file=args.stats, tgtlem=args.lemma)
    else:
        vis = Visualize(f_display=args.display, rawtac_file=args.stats)

    # Visualize
    if args.file == "all":
        for file in files:
            vis.visualize_file(file)
    else:
        vis.visualize_file(args.file)

    # Record info    
    vis.rawstats.log_notok()
    vis.rawstats.log_mlstats()
    vis.rawstats.log_namestats()
    record(args.output, vis)
