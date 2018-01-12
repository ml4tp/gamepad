import argparse
import os.path as op
import pickle

from recon.embed_tokens import EmbedTokens
from recon.recon import Recon, FILES
from ml.embed import EmbedCoqTacTr#, MyModel, PosEvalTrainer
import tacst_prep
from tacst_prep import PosEvalPt

from ml.poseval.fold_model import PosEvalModel
from ml.poseval.fold_train import PosEvalTrainer, ChkPosEvalTrainer

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
    argparser.add_argument("-f", "--fold", action="store_true",
                           help="Set to use folding library for batching")
    args = argparser.parse_args()

    print("Loading tactrs ...")
    with open(args.load, 'rb') as f:
        tactrs = pickle.load(f)

    print("Loading poseval dataset ...")
    with open(args.poseval, 'rb') as f:
        poseval_dataset, tokens_to_idx = pickle.load(f)

    # model = PosEvalModel(*tokens_to_idx)
    # trainer = PosEvalTrainer(model, tactrs, poseval_dataset,
    #                          "mllogs/embedv1.0.jsonl", args.fold)
    # trainer.train()

    model = PosEvalModel(*tokens_to_idx)
    trainer1 = PosEvalTrainer(model, tactrs, poseval_dataset,
                              "mllogs/embedv1.0.jsonl", f_fold=False)
    trainer2 = PosEvalTrainer(model, tactrs, poseval_dataset,
                              "mllogs/embedv2.0.jsonl", f_fold=True)
    checker = ChkPosEvalTrainer(trainer1, trainer2)
    checker.check()
