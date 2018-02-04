import os.path as op

from recon.build_tactr import TacTreeBuilder
from recon.embed_tokens import EmbedTokens
from recon.parse_raw import TacStParser
from recon.parse_rawtac import RawTacParser


"""
[Note]

Reconstruct tactic trees from tcoq dump files.

parse_raw     : Dump -> [TacStDecl]
parse_rawtac  : [TacStDecl] -> [RawTac]
build_tactr   : [RawTac] -> TacTree
"""


# -------------------------------------------------
# Files in dataset

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
    def __init__(self, f_token=True):
        self.f_token = f_token
        self.embed_tokens = EmbedTokens()
        self.tactrs = []

    def recon_file(self, file, f_verbose=False):
        if f_verbose:
            print("==================================================")
            print("Reconstructing file {}".format(file))
        
        ts_parser = TacStParser(file, f_log=False)
        tactrs = []
        while not ts_parser.exhausted:
            # Coq output file to [TacStDecl] tokens
            lemma = ts_parser.parse_lemma()
            tactr = self._recon_lemma(file, lemma)
            tactrs += [tactr]

        self.tactrs += tactrs
        return tactrs

    def recon_lemma(self, file, lemma, f_verbose=False):
        if f_verbose:
            print("==================================================")
            print("Reconstructing lemma {} in file {}".format(lemma, file))

        ts_parser = TacStParser(file, f_log=False)
        ts_parser.seek_lemma(lemma)
        # Coq output file to [TacStDecl] tokens
        lemma = ts_parser.parse_lemma()
        if f_verbose:
            print(">>>>>>>>>>>>>>>>>>>>>")
            # TODO(deh): some bug with pretty printing ...
            # print(lemma.pp())
            print("<<<<<<<<<<<<<<<<<<<<<")

        tactr = self._recon_lemma(file, lemma)
        self.tactrs += [tactr]
        return tactr

    def _recon_lemma(self, file, lemma):
        # [TacStDecl] tokens to [RawTac]
        tr_parser = RawTacParser(lemma, f_log=False)
        tacs, _ = tr_parser.parse_rawtacs()

        # [RawTac] to tactic tree
        tr_builder = TacTreeBuilder(lemma.name, tacs, lemma.get_tacst_info(),
                                    {}, lemma.decoder,  False)
        tr_builder.build_tacs()
        tactr = tr_builder.get_tactree()

        # Get unique "tokens"
        if self.f_token:
            self.embed_tokens.tokenize_tactr(tactr)

        return tactr
