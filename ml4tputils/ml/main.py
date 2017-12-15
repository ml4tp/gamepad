import argparse
import os.path as op
import pickle

from recon.embed_tokens import EmbedTokens
from recon.recon import Recon, FILES
from ml.embed import EmbedCoqTacTr, MyModel, MyTrainer

"""
[Note]

Top-level entry-point for machine learning.
"""


class Preprocess(object):
    def __init__(self, files):
        self.recon = Recon(f_token=False)
        self._preprocess_embed_all(files)

    def _preprocess_embed_all(self, files):
        for file in files:
            self._preprocess_embed_file(file)

    def _preprocess_embed_file(self, file):
        self.recon.recon_file(file, f_verbose=True)

    def get_tactrees(self):
        return self.recon.tactrs


if __name__ == "__main__":
    # Set up command line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-r", "--recon", default=None,
                           help="Enter the file you want to reconstruct.")
    argparser.add_argument("-p", "--path", default="data/odd-order",
                           type=str, help="Path to files")
    argparser.add_argument("-l", "--load", default="tactr.pickle",
                           type=str, help="Path to files")
    args = argparser.parse_args()

    bgfiles = [op.join(args.path, file) for file in
               FILES if file.startswith("BG")]
    pffiles = [op.join(args.path, file) for file in
               FILES if file.startswith("PF")]

    files = [op.join(args.path, file) for file in FILES]

    # Read in files
    if not args.recon:
        with open("tactr.pickle", 'rb') as f:
            print("Loading {}...".format(args.load))
            tactrs = pickle.load(f)
            print("Done loading...")
    else:
        if args.recon == "all":
            preprocess = Preprocess(files)
        elif args.recon == "bg":
            preprocess = Preprocess(bgfiles)
        elif args.recon == "pf":
            preprocess = Preprocess(pffiles)
        else:
            preprocess = Preprocess([args.recon])
        tactrs = preprocess.get_tactrees()

    # Tokenize embeddings
    embed_tokens = EmbedTokens()
    embed_tokens.tokenize_tactrs(tactrs)
    tokens_to_idx = embed_tokens.tokens_to_idx()

    # Run model
    model = MyModel(*tokens_to_idx)
    trainer = MyTrainer(model, tactrs)
    trainer.train()
