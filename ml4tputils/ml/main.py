import argparse
import os.path as op
import pickle
import torch
from recon.embed_tokens import EmbedTokens
from recon.recon import Recon, FILES
from ml.embed import EmbedCoqTacTr#, MyModel, PosEvalTrainer
import tacst_prep
from tacst_prep import PosEvalPt

from ml.poseval.fold_model import PosEvalModel
from ml.poseval.fold_train import PosEvalTrainer

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
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-l", "--load", default="tactr.pickle",
                           type=str, help="Pickle file to load")
    argparser.add_argument("-p", "--poseval", default="poseval.pickle",
                           type=str, help="Pickle file to save to")
    argparser.add_argument("-f", "--fold", action = 'store_true', help="To fold or not to fold")
    argparser.add_argument("--ln", action = 'store_true', help="To norm or not to norm")

    argparser.add_argument("--orig", action = 'store_true', help="Old is gold")
    argparser.add_argument('--no-cuda', action='store_true', default=False,
                        help='disables CUDA training')
    argparser.add_argument('--nbatch', type = int, default = 32, help = 'minibatch size')
    argparser.add_argument('--lr', type = float, default=0.001, help = 'learning rate')

    args = argparser.parse_args()
    args.cuda = not args.no_cuda and torch.cuda.is_available()

    torch.manual_seed(0)
    if args.cuda:
        torch.cuda.manual_seed(0)

    print(args)
    print("Loading tactrs ...")
    with open(args.load, 'rb') as f:
        tactrs = pickle.load(f)

    print("Loading poseval dataset ...")
    with open(args.poseval, 'rb') as f:
        poseval_dataset, tokens_to_idx = pickle.load(f)
    print("Points ", len(poseval_dataset))
    if not args.orig:
        model = PosEvalModel(*tokens_to_idx, ln=args.ln)
        trainer = PosEvalTrainer(model, tactrs, poseval_dataset, args.fold, args.cuda)
        trainer.train(args)
    else:
        from ml.embed import MyModel, PosEvalTrainer
        print("Original")
        model = MyModel(*tokens_to_idx)
        trainer = PosEvalTrainer(model, tactrs, poseval_dataset)
        trainer.train()

    # model = PosEvalModel(*tokens_to_idx)
    # trainer = PosEvalTrainer(model, tactrs, poseval_dataset)
    # trainer.train()

    """
    # Set up command line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-r", "--recon", default=None,
                           help="Enter the file you want to reconstruct.")
    argparser.add_argument("-p", "--path", default="data/odd-order",
                           type=str, help="Path to files")
    argparser.add_argument("-l", "--load", default="tactr.pickle",
                           type=str, help="Pickle file to load")
    args = argparser.parse_args()

    bgfiles = [op.join(args.path, file) for file in
               FILES if file.startswith("BG")]
    pffiles = [op.join(args.path, file) for file in
               FILES if file.startswith("PF")]

    files = [op.join(args.path, file) for file in FILES]

    # Read in files
    if not args.recon:
        with open(args.load, 'rb') as f:
        # with open("tactr.pickle", 'rb') as f:
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
    """
