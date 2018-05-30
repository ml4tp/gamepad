import argparse
import pickle

import numpy as np
import torch

from coq.tactics import TACTICS_EQUIV
from ml.fold_model import LinearModel, TacStModel
from ml.fold_train import TacStTrainer
from ml.rewrite.dataset_prep import to_goalattn_dataset
from ml.rewrite.simprw import run_end2end
from ml.tacst_prep import Dataset, TacStPt      # NOTE(deh): Need this for loading pickle

"""
[Note]

Top-level entry-point for machine learning.
"""


if __name__ == "__main__":
    argparser = argparse.ArgumentParser()

    # Task arguments
    argparser.add_argument('--task', type=str, default='pose', choices=['pose', 'tac'], help='which task')
    argparser.add_argument('--simprw', action='store_true', help='train for simple rewrite')
    argparser.add_argument('--lids', action='store_true', help='predict tactic arguments. Only local ids')

    # Dataset args
    argparser.add_argument('--load', type=str, default='tactr.pickle', help='Pickle file to load')
    argparser.add_argument('--tacst', type=str, default='tacst.pickle', help='Pickle file to save to')
    argparser.add_argument('--midlvl', action='store_true', help='train on mid-level ast')
    argparser.add_argument('--noimp', action='store_true', help='remove implicit arguments')

    # Model args
    argparser.add_argument('--linear', action='store_true', help='use simple linear model')
    argparser.add_argument('--treelstm', action='store_true', help='use treelstm model')
    argparser.add_argument('--lstm', action='store_true', help='use lstm model')
    argparser.add_argument('--state', type=int, default=128, help='state size')
    argparser.add_argument('--ln', action='store_true', help='use simple layer norm')
    argparser.add_argument('--conclu_pos', type=int, choices=[0, -1], default=0, help='place conclusion at start or end (0 or -1)')
    argparser.add_argument('--dropout', type=float, default=0.0, help='dropout rate')
    argparser.add_argument('--weight_dropout', type=float, default=0.0, help='weight dropout rate')
    argparser.add_argument('--variational', action='store_true', help='use variational dropout')
    argparser.add_argument('--attention', action='store_true', help='use attention model')
    argparser.add_argument('--heads', type=int, default=1, help='attention heads')
    
    # Training args
    argparser.add_argument('--nbatch', type=int, default=32, help='minibatch size')
    argparser.add_argument('--lr', type=float, default=0.001, help='learning rate')
    argparser.add_argument('--valbatch', type=int, default=32, help='minibatch size for validation')
    
    # Speed args
    argparser.add_argument('--no_fold', action='store_true', help='disables folding ie dynamic batching')
    argparser.add_argument('--no_sharing', action='store_true', help='disables embedding sharing')
    argparser.add_argument('--no_cuda', action='store_true', help='disables CUDA training')
    
    # Other args
    argparser.add_argument('--name', type=str, default='', help='name of experiment')
    argparser.add_argument('--debug', action='store_true', help='debug training')
    argparser.add_argument('--mload', type=str, default='', help='path to load saved model from')
    argparser.add_argument('--validate', action='store_true', help='only validate')
    argparser.add_argument('--teste2e', action='store_true', help='test end2end')

    args = argparser.parse_args()

    assert not (args.lstm and args.treelstm)
    
    if args.task == 'tac':
        args.outsize = len(TACTICS_EQUIV)
    else:
        args.outsize = 3

    args.cuda = not args.linear and not args.no_cuda and torch.cuda.is_available()
    args.fold = not args.no_fold
    args.sharing = not args.no_sharing

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

    print("Loading tacst dataset ...")
    with open(args.tacst, 'rb') as f:
        tacst_dataset, kern_tokens_to_idx, mid_tokens_to_idx = pickle.load(f)
        if args.midlvl:
            tokens_to_idx = mid_tokens_to_idx
        else:
            tokens_to_idx = kern_tokens_to_idx

    print("Points Train={} Val={} Test={}".format(len(tacst_dataset.train), len(tacst_dataset.val),
                                                  len(tacst_dataset.test)))
    # with launch_ipdb_on_exception():
    if args.simprw:
        dataset, test_lemmas, val_lemmas = to_goalattn_dataset("theorems", tacst_dataset)
        model = TacStModel(*tokens_to_idx, ln=args.ln, treelstm=args.treelstm, lstm=args.lstm,
                           dropout=args.dropout, attention=args.attention, heads=args.heads, D=args.state,
                           state=args.state, weight_dropout=args.weight_dropout, variational=args.variational,
                           conclu_pos=args.conclu_pos, lids=args.lids, outsize=40, f_mid=args.midlvl, f_useiarg=not args.noimp)
        trainer = TacStTrainer(model, tactrs, dataset, args)
        if args.validate:
            trainer.validate()
        elif args.teste2e:
            run_end2end(trainer, test_lemmas, val_lemmas)
        else:
            trainer.train()
    else:
        if args.linear:
            model = LinearModel(outsize=args.outsize, f_mid=args.midlvl, f_useiarg=not args.noimp)
        else:
            model = TacStModel(*tokens_to_idx, ln=args.ln, treelstm=args.treelstm, lstm=args.lstm,
                               dropout=args.dropout, attention=args.attention, heads=args.heads, D=args.state,
                               state=args.state, weight_dropout=args.weight_dropout, variational=args.variational,
                               conclu_pos=args.conclu_pos, lids=args.lids, outsize=args.outsize, f_mid=args.midlvl, f_useiarg=not args.noimp)
        print("Made model")
        trainer = TacStTrainer(model, tactrs, tacst_dataset, args)
        print("Made trainer")
        if args.validate:
            trainer.validate()
        else:
            trainer.train()
    trainer.logger.close()
    trainer.vallogger.close()
