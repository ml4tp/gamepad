import argparse
import networkx as nx
import numpy as np
import os.path as op
import pickle

from lex_raw import *
from parse_tacst import *
from build_tactr import *
from raw_stats import *
from tactr_stats import *


class Visualize(object):
    def __init__(self, f_display=False, f_jupyter=False, f_verbose=True,
                 rawtac_file=None, tactr_file="tactr.log", tgtlem=None):
        assert isinstance(f_display, bool)
        assert (not rawtac_file or isinstance(rawtac_file, str))
        assert (not tgtlem or isinstance(tgtlem, str))

        # Internal book-keeping
        self.num_lemmas = 0
        self.failed = []

        # Flags
        self.f_display = f_display
        self.f_jupyter = f_jupyter
        self.f_verbose = f_verbose

        # Target lemma?
        self.tgtlem = tgtlem
        self.abort = False

        # Compute stats?
        if rawtac_file:
            self.f_stats = True
        else:
            self.f_stats = False
        self.rawstats = RawStats(rawtac_file, False)
        self.tactrstats = TacTreeStats(tactr_file)

    def visualize_lemma(self, file, lemma):
        if self.tgtlem and self.tgtlem != lemma.name:
            return

        # Internal
        if self.f_verbose:
            print("------------------------------------------------")
            print("Visualizing lemma: {}".format(lemma.name))
        self.num_lemmas += 1

        # [TacStDecl] tokens to [RawTac]
        tr_parser = TacTreeParser(lemma, f_log=False)
        tacs = tr_parser.parse_tactree()

        if self.f_verbose and self.tgtlem:
            print(">>>>>>>>>>>>>>>>>>>>")
            for tac in tacs:
                print(tac.pp())
            print("<<<<<<<<<<<<<<<<<<<<")

        # Compute statistics
        if self.f_stats:
            self.rawstats.stats_tacs(lemma, tacs)

        tr_builder = TacTreeBuilder(lemma.name, tacs, tr_parser.gid2info, False)
        tr_builder.build_tacs()
        succ, ncc = tr_builder.check_success()
        if not succ:
            self.failed += [(file, lemma.name, ncc)]

        tactr = tr_builder.get_tactree(self.f_verbose)
        tachist = self.tactrstats.tactic_hist(tactr)
        if self.f_verbose:
            tachist = sorted(tachist, key=lambda k: (k[1], k[0]), reverse=True)
            print("HIST", tachist)

        if self.f_display:
            if self.f_jupyter:
                tr_builder.show_jupyter()
            else:
                tr_builder.show()

        if self.tgtlem:
            self.abort = True

        return tactr
    
    def visualize_file(self, file):
        if self.f_verbose:
            print("==================================================")
            print("Visualizing file: {}".format(file))

        tactrs = []
        ts_parser = TacStParser(file, f_log=False)
        while not ts_parser.exhausted:
            lemma = ts_parser.parse_lemma()
            tactrs += [self.visualize_lemma(file, lemma)]
            if self.abort:
                return tactrs
        return tactrs


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
    argparser.add_argument("-p", "--path", default="data/odd-order",
                           type=str, help="Path to files")
    argparser.add_argument("-s", "--stats", default="rawtac.log", type=str,
                           help="Compute raw tactic statistics")
    argparser.add_argument("-to", "--tactrout", default="tactr.log", type=str,
                           help="Compute tactic tree statistics")
    argparser.add_argument("-v", "--verbose", action="store_true",
                           help="Verbose")
    args = argparser.parse_args()

    files = ["BGsection1.v.dump",
             "BGsection2.v.dump",
             "BGsection3.v.dump",
             "BGsection4.v.dump",
             "BGsection5.v.dump",
             "BGsection6.v.dump",
             "BGsection7.v.dump",
             "BGsection8.v.dump",
             "BGsection9.v.dump",
             "BGsection10.v.dump",
             "BGsection11.v.dump",
             "BGsection12.v.dump",
             "BGsection13.v.dump",
             "BGsection14.v.dump",
             "BGsection15.v.dump",
             "BGsection16.v.dump",
             "BGappendixAB.v.dump",
             "BGappendixC.v.dump",
             "PFsection1.v.dump",
             "PFsection2.v.dump",
             "PFsection3.v.dump",
             "PFsection4.v.dump",
             "PFsection5.v.dump",
             "PFsection6.v.dump",
             "PFsection7.v.dump",
             "PFsection8.v.dump",
             "PFsection9.v.dump",
             "PFsection10.v.dump",
             "PFsection11.v.dump",
             "PFsection12.v.dump",
             "PFsection13.v.dump",
             "PFsection14.v.dump",
             "stripped_odd_order_theorem.v.dump",
             "wielandt_fixpoint.v.dump"]
    
    files = [ op.join(args.path, file) for file in files ]

    # Create visualizer
    if args.lemma:
        vis = Visualize(f_display=args.display, f_verbose=args.verbose,
                        rawtac_file=args.stats, tactr_file=args.tactrout,
                        tgtlem=args.lemma)
    else:
        vis = Visualize(f_display=args.display, f_verbose=args.verbose,
                        rawtac_file=args.stats, tactr_file=args.tactrout)

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
    vis.tactrstats.log_tactic_hist()
    record(args.output, vis)
