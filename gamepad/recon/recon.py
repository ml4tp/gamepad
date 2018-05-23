from recon.tactr_builder import TacTreeBuilder
from recon.embed_tokens import EmbedTokens
from recon.tacst_parser import TacStParser
from recon.rawtac_builder import RawTacParser


"""
[Note]

Reconstruct tactic trees from tcoq dump files.
"""


# -------------------------------------------------
# Reconstructing

class Recon(object):
    """
    [Note]

    Reconstruct tactic trees from tcoq dump files.
    It proceeds in 3 steps:
    1. Convert raw dump into list of declarations.
        parse_raw     : Dump -> [TacStDecl]
    2. Group declarations into the tactics that produce the declarations.
        parse_rawtac  : [TacStDecl] -> [RawTac]
    3. Build the tactic tree.
        build_tactr   : [RawTac] -> TacTree
    """
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
        # Coq output file to [TacStDecl] tokens
        lemma = ts_parser.parse_lemma()
        if f_verbose:
            print(">>>>>>>>>>>>>>>>>>>>>")
            # TODO(deh): some bug with pretty printing ...
            # print(lemma.pp())
            print("<<<<<<<<<<<<<<<<<<<<<")

        tactr = self._recon_lemma(lemma)
        self.tactrs += [tactr]
        return tactr

    def _recon_lemma(self, lemma):
        # [TacStDecl] tokens to [RawTac]
        tr_parser = RawTacParser(lemma, f_log=False)
        tacs, _ = tr_parser.parse_rawtacs()

        # [RawTac] to tactic tree
        tr_builder = TacTreeBuilder(lemma.name, tacs, lemma.get_tacst_info(), {}, {},
                                    lemma.decoder, lemma.mid_decoder, False)
        tr_builder.build_tacs()
        tactr = tr_builder.get_tactree()

        # Get unique "tokens"
        if self.f_token:
            self.embed_tokens.tokenize_tactr(tactr)

        return tactr
