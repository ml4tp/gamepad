import argparse
import os.path as op

from recon.build_tactr import TacTreeBuilder
from recon.parse_raw import TacStParser
from recon.parse_rawtac import RawTacParser
from recon.recon import FILES, Recon


class Visualize(object):
    def __init__(self, f_display=False, f_jupyter=False, f_verbose=True,
                 tactr_file="tactr.log"):
        # Internal book-keeping
        self.num_lemmas = 0
        self.failed = []

        self.recon = Recon()

        # Flags
        self.f_display = f_display     # Draw graph?
        self.f_jupyter = f_jupyter     # Using jupyter?
        self.f_verbose = f_verbose

        # Tactic tree statistics
        self.tactr_file = tactr_file
        self.h_tactr_file = open(tactr_file, 'w')
        self.h_tactr_file.write("LEMMA INFO\n")

        # Global statistics
        self.unique_const = set()
        self.unique_ind = set()
        self.unique_conid = set()

        # Tactic Trees
        self.tactrs = []

    def finalize(self):
        self.h_tactr_file.write("TOTAL: {} WERID: {}\n".format(
                                self.num_lemmas, len(self.failed)))
        self.h_tactr_file.write("UNIQUECONST: {}\n".format(
                                len(self.unique_const)))
        self.h_tactr_file.write("UNIQUEIND: {}\n".format(
                                len(self.unique_ind)))
        self.h_tactr_file.write("UNIQUECONID: {}\n".format(
                                len(self.unique_conid)))
        self.h_tactr_file.close()

    """
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
        tr_parser = RawTacParser(lemma, f_log=False)
        tacs = tr_parser.parse_rawtacs()
        if self.f_verbose and self.tgtlem:
            print(">>>>>>>>>>>>>>>>>>>>")
            for tac in tacs:
                print(tac.pp())
            print("<<<<<<<<<<<<<<<<<<<<")

        # [RawTac] to tactic tree
        tr_builder = TacTreeBuilder(lemma.name, tacs, lemma.get_tacst_info(),
                                    {}, lemma.decoder,  False)
        tr_builder.build_tacs()
        succ, ncc = tr_builder.check_success()
        if not succ:
            self.failed += [(file, lemma.name, ncc, len(tr_builder.notok))]

        # Compute tactic tree statistics
        tactr = tr_builder.get_tactree(self.f_verbose)
        tactr.log_stats(self.h_tactr_file)

        # Compute global statistics
        self.unique_const = self.unique_const.union(tactr.unique_const())
        self.unique_ind = self.unique_ind.union(tactr.unique_ind())
        self.unique_conid = self.unique_conid.union(tactr.unique_conid())

        if self.f_display:
            if self.f_jupyter:
                tactr.show_jupyter()
            else:
                tactr.show()

        return tactr

    def _visualize_lemma(self, ts_parser):
        lemma = ts_parser.parse_lemma()
        if self.f_verbose:
            print(">>>>>>>>>>>>>>>>>>>>>")
            print(lemma.pp())
            print("<<<<<<<<<<<<<<<<<<<<<")
        tactr = self.visualize_lemma(ts_parser.filename, lemma)
        self.tactrs += [tactr]
    """

    """
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
    """
    def visualize_file(self, file):
        self.tactrs += self.recon.recon_file(file, not(self.f_jupyter))

    def visualize_lemma(self, file, lemma):
        tactr = self.recon.recon_lemma(file, lemma, not(self.f_jupyter))
        self.tactrs += [tactr]

        if self.f_display:
            if self.f_jupyter:
                tactr.show_jupyter()
            else:
                tactr.show()


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

    files = [op.join(args.path, file) for file in FILES]
    bgfiles = [op.join(args.path, file) for file in
               FILES if file.startswith("BG")]
    pffiles = [op.join(args.path, file) for file in
               FILES if file.startswith("PF")]

    # Visualize
    vis = Visualize(f_display=args.display, f_verbose=args.verbose,
                    tactr_file=args.tactrout)
    if args.lemma:
        vis.visualize_lemma(args.file, args.lemma)
    else:
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
