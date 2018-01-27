import argparse
import os.path as op
import pickle
import torch
import numpy as np

from recon.recon import Recon
from ml.tacst_prep import Dataset, PosEvalPt

from ml.poseval.fold_model import PosEvalModel
from ml.poseval.fold_train import PosEvalTrainer #, PosEvalInfer
# from ipdb import launch_ipdb_on_exception

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

    # Model/Experiment args
    argparser.add_argument('--nbatch', type = int, default = 32, help = 'minibatch size')
    argparser.add_argument('--lr', type = float, default=0.001, help = 'learning rate')
    argparser.add_argument('--state', type = int, default = 128, help = 'state size')
    argparser.add_argument("--ln", action = 'store_true', help="To norm or not to norm")
    argparser.add_argument('--dropout', type= float, default = 0.0, help = 'dropout rate')
    argparser.add_argument('--weight_dropout', type= float, default = 0.0, help = 'weight dropout rate')
    argparser.add_argument('--variational', action='store_true', help = 'Variational dropout')
    argparser.add_argument("--attention", action = 'store_true', help="To attend or not to attend")
    argparser.add_argument("--heads", type = int, default = 1, help="Attention heads")
    argparser.add_argument("--treelstm", action = 'store_true', help="To tree or not to tree")
    argparser.add_argument("--lstm", action = 'store_true', help="To tree or not to tree")
    argparser.add_argument('--valbatch', type = int, default = 32, help = 'minibatch size for validation')
    argparser.add_argument('--name', type = str, default = "", help = 'name of experiment')
    argparser.add_argument("--debug", action = 'store_true', help="debug training")
    argparser.add_argument("--orig", action = 'store_true', help="Old is gold")

    argparser.add_argument("-f", "--fold", action = 'store_true', help="To fold or not to fold")
    argparser.add_argument('--no-cuda', action='store_true', default=False, help='disables CUDA training')
    argparser.add_argument('--mload', type = str, default = "", help = 'path to load saved model from')
    argparser.add_argument('--validate', action='store_true', default = False, help = 'only validate')


    args = argparser.parse_args()
    assert not (args.lstm and args.treelstm)

    args.cuda = not args.no_cuda and torch.cuda.is_available()
    if args.debug:
        args.name = "debug_" + args.name
    np.random.seed(0)
    torch.manual_seed(0)
    if args.cuda:
        torch.cuda.manual_seed(0)
        import sys
        sys.setrecursionlimit(5000)

    print(args)
    print("Loading tactrs ...")
    with open(args.load, 'rb') as f:
        tactrs = pickle.load(f)

    print("Loading poseval dataset ...")
    with open(args.poseval, 'rb') as f:
        poseval_dataset, tokens_to_idx = pickle.load(f)

    print("Points Train={} Val={} Test={}".format(len(poseval_dataset.train), len(poseval_dataset.val), len(poseval_dataset.test)))
    #with launch_ipdb_on_exception():
    if not args.orig:
        model = PosEvalModel(*tokens_to_idx, ln=args.ln, treelstm=args.treelstm, lstm=args.lstm, dropout=args.dropout, attention=args.attention, heads=args.heads, D = args.state, state = args.state, weight_dropout=args.weight_dropout, variational=args.variational)
        trainer = PosEvalTrainer(model, tactrs, poseval_dataset, args)
        if args.validate:
            trainer.validate()
        else:
            trainer.train()
        trainer.logger.close()
        trainer.vallogger.close()
    else:
        from ml.embed import MyModel, PosEvalTrainer
        print("Original")
        model = MyModel(*tokens_to_idx)
        trainer = PosEvalTrainer(model, tactrs, poseval_dataset.train)
        trainer.train()


        # # Inference
    # model_infer = PosEvalModel(*tokens_to_idx)
    # model_infer.load_state_dict(torch.load(filename))
    # infer = PosEvalInfer(tactrs, model_infer)
    # infer.infer(poseval_dataset)


    # TODO(deh): Uncomment me to test with checker
    # model = PosEvalModel(*tokens_to_idx)
    # trainer1 = PosEvalTrainer(model, tactrs, poseval_dataset,
    #                           "mllogs/embedv1.0.jsonl", f_fold=False)
    # trainer2 = PosEvalTrainer(model, tactrs, poseval_dataset,
    #                           "mllogs/embedv2.0.jsonl", f_fold=True)
    # checker = ChkPosEvalTrainer(trainer1, trainer2)
    # checker.check()
    # trainer1.finalize() 
    # trainer2.finalize()
