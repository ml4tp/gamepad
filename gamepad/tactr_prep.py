# Copyright 2018 The GamePad Authors. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# ==============================================================================

import argparse
import os.path as op
import pickle

from recon.tacst_parser import TacStParser
from recon.recon import Recon


"""
[Note]

1. Visualize all files
    python gamepad/tactr_prep.py files <file-list.txt>
2. Visualize a lemma in a specific file
    python gamepad/tactr_prep.py file <file.dump> -l <lemma>
"""


class Visualize(object):
    def __init__(self, f_display=False, f_jupyter=False, f_verbose=False, tactr_log=None, tactr_pkl=None):
        # Internal book-keeping
        self.recon = Recon()         # tactic tree reconstructor
        self.tactrs = []             # reconstructed tactic trees
        self.failed = []             # failed reconstructions

        # Flags
        self.f_display = f_display   # draw graph?
        self.f_jupyter = f_jupyter   # using jupyter?
        self.f_verbose = f_verbose   # verbose?

        # Tactic tree statistics
        self.tactr_log = tactr_log
        if self.tactr_log:
            self.h_tactr_log = open(self.tactr_log, 'w')
            self.h_tactr_log.write("LEMMA INFO\n")
            self.num_iargs = 0
            self.num_args = 0

        # Tactic tree pickling
        self.tactr_pkl = tactr_pkl

        import sys
        sys.setrecursionlimit(1500)

    def finalize(self):
        if self.tactr_log:
            self.h_tactr_log.write("TOTAL: {} WERID: {}\n".format(
                                    len(self.tactrs), len(self.failed)))
            self.h_tactr_log.write("UNIQUE-SORT: {}\n".format(
                                    len(self.recon.embed_tokens.unique_sort)))
            self.h_tactr_log.write("UNIQUE-CONST: {}\n".format(
                                    len(self.recon.embed_tokens.unique_const)))
            self.h_tactr_log.write("UNIQUE-IND: {}\n".format(
                                    len(self.recon.embed_tokens.unique_ind)))
            self.h_tactr_log.write("UNIQUE-CONID: {}\n".format(
                                    len(self.recon.embed_tokens.unique_conid)))
            self.h_tactr_log.write("UNIQUE-EVAR: {}\n".format(
                                    len(self.recon.embed_tokens.unique_evar)))
            self.h_tactr_log.write("UNIQUE-FIX: {}\n".format(
                                    len(self.recon.embed_tokens.unique_fix)))
            self.h_tactr_log.write("NUM_IARGS: {}\n".format(self.num_iargs))
            self.h_tactr_log.write("NUM_ARGS: {}\n".format(self.num_args))
            self.h_tactr_log.close()

    def save_tactrs(self):
        if self.tactr_pkl:
            with open(self.tactr_pkl, 'wb') as h_pickle:
                pickle.dump(self.tactrs, h_pickle)
        else:
            raise NameError("Cannot save pickle to", self.tactr_pkl)

    def load_tactrs(self):
        if self.tactr_pkl:
            with open(self.tactr_pkl, 'rb') as h_pickle:
                self.tactrs = pickle.load(h_pickle)
        else:
            raise NameError("Cannot load pickle from", self.tactr_pkl)

    def test_parse_tac(self, file):
        ts_parser = TacStParser(file)
        ts_parser.parse_file()

    def visualize_file(self, file):
        tactrs = self.recon.recon_file(file, not self.f_jupyter)
        self.tactrs += tactrs
        
        for tactr in tactrs:
            succ, ncc = tactr.check_success()
            if not succ:
                print("FAILED", tactr.name, ncc)
                self.failed += [(file, tactr.name, ncc, len(tactr.notok))]

            if self.tactr_log:
                info = tactr.log_stats(self.h_tactr_log)
                self.num_iargs += info['hist_gc'][1]
                self.num_args += info['hist_gc'][2]
                # print("iargs / args = {} / {}".format(self.num_iargs, self.num_args))

    def visualize_lemma(self, file, lemma):
        tactr = self.recon.recon_lemma(file, lemma, not self.f_jupyter)
        self.tactrs += [tactr]

        if self.f_display:
            if self.f_jupyter:
                tactr.show_jupyter()
            else:
                tactr.show()
        return tactr


if __name__ == "__main__":
    # Set up command line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("mode", choices=["file", "files"],
                           help="Enter the file you want to visualize.")
    argparser.add_argument("file",
                           help="Enter the dump or dump list you want to visualize.")
    argparser.add_argument("-f", "--files", type=str, help="Visualize a list of files", default=None)
    argparser.add_argument("-d", "--display", action="store_true",
                           help="Display the tactic tree.")
    argparser.add_argument("-l", "--lemma", type=str,
                           help="Visualize a specific lemma by name.")
    argparser.add_argument("-p", "--path", default="data/odd-order",
                           type=str, help="Path to files")
    argparser.add_argument("-log", "--log", default="tactr.log", type=str,
                           help="File to log tactic tree statistics to.")
    argparser.add_argument("-pkl", "--pickle", default="tactr.pickle", type=str,
                           help="File to save tactic tree pickle to.")
    argparser.add_argument("-v", "--verbose", action="store_true",
                           help="Verbose")
    args = argparser.parse_args()

    # Visualize
    vis = Visualize(f_display=args.display, f_verbose=args.verbose,
                    tactr_log=args.log, tactr_pkl=args.pickle)
    if args.mode == "file":
        file = op.join(args.path, args.file)
        if args.lemma:
            vis.visualize_lemma(file, args.lemma)
        else:
            vis.visualize_file(file)
            vis.finalize()
            vis.save_tactrs()
    else:
        with open(args.file, 'r') as h_files:
            files = []
            for file in h_files:
                files += [op.join(args.path, file.strip())]

            for file in files:
                vis.visualize_file(file)
            vis.finalize()
            vis.save_tactrs()
