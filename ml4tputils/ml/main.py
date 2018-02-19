import argparse
import pickle
import torch
import numpy as np

from ml.poseval.fold_model import PosEvalModel
from ml.poseval.fold_train import PosEvalTrainer
# from ipdb import launch_ipdb_on_exception
from ml.rewrite.solver import to_goalattn_dataset, run

"""
[Note]

Top-level entry-point for machine learning.
"""


if __name__ == "__main__":
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-l", "--load", default="tactr.pickle",
                           type=str, help="Pickle file to load")
    argparser.add_argument("-p", "--poseval", default="poseval.pickle",
                           type=str, help="Pickle file to save to")

    # Model/Experiment args
    argparser.add_argument('--nbatch', type=int, default=32, help='minibatch size')
    argparser.add_argument('--lr', type=float, default=0.001, help='learning rate')
    argparser.add_argument('--state', type=int, default=128, help='state size')
    argparser.add_argument("--ln", action='store_true', help="To norm or not to norm")
    argparser.add_argument('--conclu_pos', type=int, choices=[0, -1], default=0, help='conclusion at start or end')
    argparser.add_argument('--dropout', type=float, default=0.0, help='dropout rate')
    argparser.add_argument('--weight_dropout', type=float, default=0.0, help='weight dropout rate')
    argparser.add_argument('--variational', action='store_true', help='Variational dropout')
    argparser.add_argument("--attention", action='store_true', help="To attend or not to attend")
    argparser.add_argument("--heads", type=int, default=1, help="Attention heads")
    argparser.add_argument("--treelstm", action='store_true', help="To tree or not to tree")
    argparser.add_argument("--lstm", action='store_true', help="To tree or not to tree")
    argparser.add_argument('--valbatch', type=int, default=32, help='minibatch size for validation')
    argparser.add_argument('--name', type=str, default="", help='name of experiment')
    argparser.add_argument("--debug", action='store_true', help="debug training")
    argparser.add_argument("--orig", action='store_true', help="Old is gold")
    argparser.add_argument("--end2end", action='store_true', help="run end-to-end model")

    argparser.add_argument("-f", "--fold", action='store_true', help="To fold or not to fold")
    argparser.add_argument('--no-cuda', action='store_true', default=False, help='disables CUDA training')
    argparser.add_argument('--mload', type=str, default="", help='path to load saved model from')
    argparser.add_argument('--validate', action='store_true', default=False, help='only validate')

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

    print("Points Train={} Val={} Test={}".format(len(poseval_dataset.train), len(poseval_dataset.val),
                                                  len(poseval_dataset.test)))
    # with launch_ipdb_on_exception():
    if not args.orig:
        if args.end2end:
            dataset, test_lemmas, val_lemmas = to_goalattn_dataset(poseval_dataset)
            # model = PosEvalModel(*tokens_to_idx, ln=args.ln, treelstm=args.treelstm, lstm=args.lstm, dropout=args.dropout, attention=args.attention, heads=args.heads, D = args.state, state = args.state, weight_dropout=args.weight_dropout, variational=args.variational, conclu_pos=args.conclu_pos, f_twoway=args.end2end, outsize=20)
            # trainer = PosEvalTrainer(model, tactrs, dataset, args, f_twoway=True)
            model = PosEvalModel(*tokens_to_idx, ln=args.ln, treelstm=args.treelstm, lstm=args.lstm,
                                 dropout=args.dropout, attention=args.attention, heads=args.heads, D=args.state,
                                 state=args.state, weight_dropout=args.weight_dropout, variational=args.variational,
                                 conclu_pos=args.conclu_pos, outsize=40)
            trainer = PosEvalTrainer(model, tactrs, dataset, args)
            if args.validate:
                # trainer.validate()
                run(trainer, test_lemmas, val_lemmas)
            else:
                trainer.train()
        else:
            model = PosEvalModel(*tokens_to_idx, ln=args.ln, treelstm=args.treelstm, lstm=args.lstm,
                                 dropout=args.dropout, attention=args.attention, heads=args.heads, D=args.state,
                                 state=args.state, weight_dropout=args.weight_dropout, variational=args.variational,
                                 conclu_pos=args.conclu_pos, f_twoway=args.end2end)
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
