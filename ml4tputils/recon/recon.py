import os.path as op

from recon.lex_raw import TacStParser
from recon.parse_rawtac import RawTacParser
from recon.build_tactr2 import TacTreeBuilder


# -------------------------------------------------
# Model

FILES = ["BGsection1.v.dump",
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


# -------------------------------------------------
# Reconstructing

class Recon(object):
    def __init__(self):
        self.unique_sort = set()
        self.unique_const = set()
        self.unique_ind = set()
        self.unique_conid = set()
        self.unique_evar = set()
        self.unique_fix = set()

        self.tactrs = []

    def recon_file(self, file, f_verbose=False):
        if f_verbose:
            print("==================================================")
            print("Reconstructing file {}".format(file))
        
        ts_parser = TacStParser(file, f_log=False)
        tactrs = []
        while not ts_parser.exhausted:
            lemma = ts_parser.parse_lemma()
            tactr = self._recon_lemma(lemma)
            tactrs += [tactr]

        self.tactrs += tactrs
        return tactrs

    def recon_lemma(self, file, lemma, f_verbose=False):
        if f_verbose:
            print("==================================================")
            print("Reconstructing lemma {} in file {}".format(lemma, file))

        ts_parser = TacStParser(file, f_log=False)
        ts_parser.seek_lemma(lemma)
        tactr = self._recon_lemma(ts_parser.filename, lemma)
        self.tactrs += [tactr]

    def _recon_lemma(self, lemma):
        # [TacStDecl] tokens to [RawTac]
        tr_parser = RawTacParser(lemma, f_log=False)
        tacs = tr_parser.parse_rawtacs()

        # [RawTac] to tactic tree
        tr_builder = TacTreeBuilder(lemma.name, tacs, lemma.get_tacst_info(),
                                    {}, lemma.decoder,  False)
        tr_builder.build_tacs()
        tactr = tr_builder.get_tactree()

        # Get unique "tokens"
        tactr.hist_coqexp()
        self.unique_sort = self.unique_sort.union(tactr.unique_sort())
        self.unique_const = self.unique_const.union(tactr.unique_const())
        self.unique_ind = self.unique_ind.union(tactr.unique_ind())
        self.unique_conid = self.unique_conid.union(tactr.unique_conid())
        self.unique_evar = self.unique_evar.union(tactr.unique_evar())
        self.unique_fix = self.unique_fix.union(tactr.unique_fix())

        return tactr
