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
import json
import numpy as np
import random

from ml.rewrite.pycoq_prover import PyCoqProver
from ml.rewrite.simprw_prover import PyCoqTrainedProver
from ml.rewrite.utils import SIMPRW_PRELUDE, SimpRWGen, SimpRWSolver
from ml.utils import curr_timestamp


"""
[Note]

Top-level for simple-rewrite problem. You can generate lemmas here, but run the model from ml/main.py
"""


# -------------------------------------------------
# Seeding

random.seed(0)


# -------------------------------------------------
# Some lemmas

# LEMMA = "Lemma rewrite_eq_0: forall b, ( e <+> ( ( ( ( b ) <+> m ) <+> m ) <+> m ) ) <+> m = b."
# LEMMA = "Lemma rewrite_eq_0: forall b: G, ((b <+> m) <+> (m <+> ((e <+> (m <+> m)) <+> (e <+> ((e <+> e) <+> m))))) = b."
# LEMMA = "Lemma rewrite_eq_0: forall b: G, ((e <+> (b <+> (e <+> m))) <+> m) = b."
# LEMMA = "Lemma rewrite_eq_49: forall b: G, (b <+> (((e <+> e) <+> (e <+> e)) <+> m)) <+> (e <+> m) = b."
# LEMMA = "Lemma rewrite_eq_0: forall b: G, (b <+> (m <+> (e <+> (e <+> ((e <+> e) <+> m))))) = b."
# LEMMA = "Lemma rewrite_eq_432: forall b: G, (((e <+> m) <+> ((e <+> m) <+> m)) <+> (((e <+> m) <+> b) <+> (e <+> m))) = b."
# LEMMA = "Lemma rewrite_eq_191: forall b: G, ((e <+> m) <+> ((e <+> (e <+> e)) <+> (e <+> ((e <+> m) <+> (b <+> m))))) = b."
# LEMMA = "Lemma rewrite_eq_259: forall b: G, ((((e <+> m) <+> e) <+> (e <+> e)) <+> ((e <+> m) <+> ((e <+> m) <+> b))) = b."
# LEMMA = "Lemma rewrite_eq_83: forall b: G, ((e <+> (b <+> m)) <+> (((e <+> m) <+> (e <+> m)) <+> (m <+> (m <+> m)))) = b."
LEMMA = "Lemma rewrite_eq_4: forall b: G, (((e <+> (e <+> (((e <+> m) <+> m) <+> (m <+> m)))) <+> m) <+> (e <+> b)) = b."


# -------------------------------------------------
# Helper functions

def gen_lemmas(module_name, num_theorems, sent_len):
    with open('{}.v'.format(module_name), 'w') as f:
        f.write(SIMPRW_PRELUDE)
        simprw_gen = SimpRWGen()
        seen = set()
        while True:
            if len(seen) == num_theorems:
                break
            lemma = simprw_gen.gen_lemma(sent_len)
            print("Generated", lemma)
            if lemma not in seen:
                seen.add(lemma)
                policy = SimpRWSolver()
                rewriter = PyCoqProver(policy, lemma, SIMPRW_PRELUDE)
                rewriter.attempt_proof()
                print(rewriter.extract_proof())
                f.write(rewriter.extract_proof())
                f.write('\n\n')


def run_end2end_one(trainer, lemma):
    prover = PyCoqTrainedProver(SimpRWSolver(), lemma, trainer)
    prover.attempt_proof()

    print("Lemma {}".format(lemma))
    print("# steps {}".format(prover.num_steps))
    print("# bad steps {}".format(prover.num_bad_infer))
    print("# bad ast {}".format(prover.num_bad_ast))


def run_end2end(trainer, test_lemmas, val_lemmas):
    mystats = {}
    for lem_id, lemma in val_lemmas.items():
        print("DOING", lemma)
        prover = PyCoqTrainedProver(SimpRWSolver(), lemma, trainer)
        prover.attempt_proof()
        assert prover.num_steps == 9
        mystats[lem_id] = {"lemma": lemma,
                           "num_steps": prover.num_steps,
                           "bad_steps": list(prover.bad_steps),
                           "bad_infer": prover.num_bad_infer,
                           "bad_ast": prover.num_bad_ast}
        print("Statistics", mystats[lem_id])

    with open('mllogs/simprw-{}.log'.format(curr_timestamp()), 'w') as f:
        f.write(json.dumps([v for k, v in mystats.items()]))


def stats(simprw_log):
    mystats = None
    with open(simprw_log, 'rb') as f:
        for line in f:
            mystats = json.loads(line)
    if mystats is None:
        raise NameError("Cannot load file: {}".format(simprw_log))

    num_fully_solved = 0
    good_bad_ratio = []
    bad_ratio = []
    for stat in mystats:
        if len(stat['bad_steps']) == 0:
            num_fully_solved += 1
            good_bad_ratio += [stat['bad'] / stat['num_steps']]
        bad_ratio += [len(stat['bad_steps']) / stat['num_steps']]

    print("# fully solved           :  {}/{}".format(num_fully_solved, len(mystats)))
    print("Ratio of bad steps       :  {}", bad_ratio)
    print("Avg. ratio of bad steps  :  {}".format(np.mean(bad_ratio)))
    # print(np.mean(good_bad_ratio))


if __name__ == "__main__":
    # Command-line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-m", "--module", default="theorems", type=str,
                           help="Coq module containing simple rewrite")
    argparser.add_argument("-n", "--numlems", default=500, type=int,
                           help="Number of lemmas to generate")
    argparser.add_argument("-l", "--exprlen", default=10, type=int,
                           help="Algebraic expression length")
    args = argparser.parse_args()

    # Generate lemmas
    gen_lemmas(args.module, args.numlems, args.exprlen)
