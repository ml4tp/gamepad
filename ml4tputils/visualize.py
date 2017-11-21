import argparse
import networkx as nx
import numpy as np
import os.path as op
import pickle

from lex_raw import TacStParser
from parse_tacst import TacTreeParser
from build_tactr import TacTreeBuilder


class Visualize(object):
    def __init__(self, f_display=False, f_jupyter=False, f_verbose=True,
                 tactr_file="tactr.log", tgtlem=None):
        assert isinstance(f_display, bool)
        assert (not tgtlem or isinstance(tgtlem, str))

        # Internal book-keeping
        self.num_lemmas = 0
        self.failed = []

        # Flags
        self.f_display = f_display     # Draw graph?
        self.f_jupyter = f_jupyter     # Using jupyter?
        self.f_verbose = f_verbose

        # Target lemma?
        self.tgtlem = tgtlem           

        # Tactic tree statistics
        self.tactr_file = tactr_file
        self.h_tactr_file = open(tactr_file, 'w')
        self.h_tactr_file.write("LEMMA INFO\n")

        # Tactic Trees
        self.tactrs = []

    def finalize(self):
        self.h_tactr_file.write("TOTAL {}: WERID: {}\n".format(
                                self.num_lemmas, len(self.failed)))
        self.h_tactr_file.close()

    def visualize_lemma(self, file, lemma):
        if self.tgtlem and self.tgtlem != lemma.name:
            return

        # Internal
        if not self.f_jupyter:
            print("------------------------------------------------")
            print("Visualizing lemma: {}".format(lemma.name))
        if self.f_verbose:
            for decl in lemma.decls:
                print(decl)
            print("--------------------")
        self.num_lemmas += 1

        # [TacStDecl] tokens to [RawTac]
        tr_parser = TacTreeParser(lemma, f_log=False)
        tacs = tr_parser.parse_tactree()
        if self.f_verbose and self.tgtlem:
            print(">>>>>>>>>>>>>>>>>>>>")
            for tac in tacs:
                print(tac.pp())
            print("<<<<<<<<<<<<<<<<<<<<")

        # [RawTac] to tactic tree
        tr_builder = TacTreeBuilder(lemma.name, tacs, lemma.get_tacst_info(),
                                    lemma.decoder, False)
        tr_builder.build_tacs()
        succ, ncc = tr_builder.check_success()
        if not succ:
            self.failed += [(file, lemma.name, ncc, len(tr_builder.notok))]

        # Compute tactic tree statistics
        tactr = tr_builder.get_tactree(self.f_verbose)
        info = tactr.log_stats(self.h_tactr_file)

        if self.f_display:
            if self.f_jupyter:
                tr_builder.show_jupyter()
            else:
                tr_builder.show()

        return tactr
    
    def _visualize_lemma(self, ts_parser):
        lemma = ts_parser.parse_lemma()
        if self.f_verbose:
            print(">>>>>>>>>>>>>>>>>>>>>")
            print(lemma.pp())
            print("<<<<<<<<<<<<<<<<<<<<<")
        tactr = self.visualize_lemma(ts_parser.filename, lemma)
        self.tactrs += [tactr]

    def visualize_file(self, file):
        if not self.f_jupyter:
            print("==================================================")
            print("Visualizing file: {}".format(file))

        ts_parser = TacStParser(file, f_log=False)
        if self.tgtlem:
            while not ts_parser.exhausted:
                ts_parser.seek_lemma(self.tgtlem)
                self._visualize_lemma(ts_parser)
                break
        else:
            while not ts_parser.exhausted:
                self._visualize_lemma(ts_parser)


if __name__ == "__main__":
    # Set up command line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("file",
                           help="Enter the file you want to visualize.")
    argparser.add_argument("-d", "--display", action="store_true",
                           help="Display the tactic tree.")
    argparser.add_argument("-l", "--lemma", type=str,
                           help="Visualize a specific lemma by name.")
    argparser.add_argument("-p", "--path", default="data/odd-order",
                           type=str, help="Path to files")
    argparser.add_argument("-to", "--tactrout", default="tactr.log", type=str,
                           help="Compute tactic tree statistics")
    argparser.add_argument("-v", "--verbose", action="store_true",
                           help="Verbose")
    args = argparser.parse_args()

    files = ["BGsection1.v.dump",
             "BGsection2.v.dump",
             "BGappendixAB.v.dump",
             "BGappendixC.v.dump",
             "wielandt_fixpoint.v.dump",
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
             "stripped_odd_order_theorem.v.dump"]

    bgfiles = [file for file in files if file.startswith("BG")]
    pffiles = [file for file in files if file.startswith("PF")]
    
    files = [ op.join(args.path, file) for file in files ]

    # Visualize
    vis = Visualize(f_display=args.display, f_verbose=args.verbose,
                    tactr_file=args.tactrout, tgtlem=args.lemma)
    if args.file == "all":
        for file in files:
            vis.visualize_file(file)
    elif args.file == "bg":
        for file in bgfiles:
            vis.visualize_file(file)
    elif args.file == "pf":
        for file in pffiles:
            vis.visualize_file(file)
    else:
        vis.visualize_file(args.file)
    vis.finalize()
