import argparse
import os.path as op

from recon.recon import Recon, FILES
from ml.embed import EmbedCoqTacTr, MyModel, MyTrainer


class Preprocess(object):
    def __init__(self, files):
        self.recon = Recon()
        self._preprocess_embed_all(files)

    def tokens_to_idx(self):
        sort_to_idx = self._tokens_to_idx(self.recon.unique_sort)
        const_to_idx = self._tokens_to_idx(self.recon.unique_const)
        ind_to_idx = self._tokens_to_idx(self.recon.unique_ind)
        conid_to_idx = self._tokens_to_idx(self.recon.unique_conid)
        evar_to_idx = self._tokens_to_idx(self.recon.unique_evar)
        fix_to_idx = self._tokens_to_idx(self.recon.unique_fix)

        print("SORT", sort_to_idx)
        print("CONST", const_to_idx)

        return (sort_to_idx, const_to_idx, ind_to_idx,
                conid_to_idx, evar_to_idx, fix_to_idx)

    def _tokens_to_idx(self, unique):
        print("UNIQUE", unique)
        ls = list(unique)
        tok_to_idx = {}
        for idx, tok in enumerate(ls):
            tok_to_idx[tok] = idx
        return tok_to_idx

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
    argparser.add_argument("file",
                           help="Enter the file you want to visualize.")
    argparser.add_argument("-p", "--path", default="data/odd-order",
                           type=str, help="Path to files")
    args = argparser.parse_args()

    bgfiles = [op.join(args.path, file) for file in
               FILES if file.startswith("BG")]
    pffiles = [op.join(args.path, file) for file in
               FILES if file.startswith("PF")]

    files = [op.join(args.path, file) for file in FILES]

    print("WTF", args.file)

    # Read in files
    if args.file == "all":
        preprocess = Preprocess(files)
    elif args.file == "bg":
        preprocess = Preprocess(bgfiles)
    elif args.file == "pf":
        preprocess = Preprocess(pffiles)
    else:
        preprocess = Preprocess([args.file])

    # Run model
    tokens_to_idx = preprocess.tokens_to_idx()
    model = MyModel(*tokens_to_idx)
    trainer = MyTrainer(model, preprocess.get_tactrees())
    trainer.train()
