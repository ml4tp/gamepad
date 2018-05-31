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

from coq.glob_constr import *
from coq.glob_constr_parser import GlobConstrParser
from ml.tacst_prep import Dataset


class DiffGlobConstr(object):
    """Figures out the first position where two glob constrs differ for the simple-rewrite problem.
    """
    def __init__(self):
        # Differencing state
        self.pos = 0
        self.found = False

    def diff_ast(self, c1, c2):
        # Reset state
        self.pos = 0
        self.found = False

        # Compute difference
        self._diff_ast(c1, c2)
        if not self.found:
            raise NameError("Could not find difference between {} and {}".format(c1, c2))

        return self.pos

    def _diff_ast(self, c1, c2):
        if isinstance(c1, GRef) and isinstance(c2, GRef):
            if not self.found:
                self.pos += 1
        elif isinstance(c1, GVar) and isinstance(c2, GVar):
            if not self.found:
                self.pos += 1
        elif isinstance(c1, GApp) and isinstance(c2, GApp):
            if not self.found:
                self.pos += 1
                self._diff_ast(c1.g, c2.g)
                for c1_p, c2_p in zip(c1.gs, c2.gs):
                    if not self.found:
                        self._diff_ast(c1_p, c2_p)
        else:
            self.found = True
            return self.pos


def get_lemmas(module_name, lemma_ids):
    lemmas = {}
    with open("{}.v".format(module_name), 'r') as f:
        for line in f:
            line = line.strip()
            if "Lemma rewrite_eq" in line:
                idx = line.find(':')
                lemma2 = line[6:idx]
                for lemid in lemma_ids:
                    if "rewrite_eq_{}".format(lemid) == lemma2:
                        lemmas[lemid] = line
                        break
    print("LEMMAS", lemma_ids.difference(set(lemmas.keys())))
    return lemmas


def to_goalattn_dataset(module_name, poseval_dataset):
    def clean2(orig):
        dataset = []
        positions = [0 for _ in range(40)]
        for tactr_id, pt in orig:
            # Item 3 contains [TacEdge]
            tac = pt.tacst[3][-1]
            if tac.name.startswith("surgery"):
                args = tac.ftac.tac_args
                rw_dir = GlobConstrParser().parse_glob_constr(args[0])
                orig_ast = GlobConstrParser().parse_glob_constr(args[1])
                rw_ast = GlobConstrParser().parse_glob_constr(args[2])
                pos = DiffGlobConstr().diff_ast(orig_ast, rw_ast)
                # Put the tactic in tac_bin
                # Put the position of the ast in the subtr_bin
                if "{}.id_r".format(module_name) in tac.ftac.gids:
                    pt.tac_bin = 0
                    pt.subtr_bin = 2 * pos
                    positions[2 * pos] += 1
                    dataset += [(tactr_id, pt)]
                elif "{}.id_l".format(module_name) in tac.ftac.gids:
                    pt.tac_bin = 1
                    pt.subtr_bin = 2 * pos + 1
                    positions[2 * pos + 1] += 1
                    dataset += [(tactr_id, pt)]
                else:
                    assert False
        print(positions)
        return dataset

    train = clean2(poseval_dataset.train)
    test = clean2(poseval_dataset.test)
    seen = set()
    for tactr_id, pt in test:
        seen.add(tactr_id)
    print("TEST", len(seen), seen)
    test_lemmas = get_lemmas(module_name, seen)
    val = clean2(poseval_dataset.val)
    seen = set()
    for tactr_id, pt in val:
        seen.add(tactr_id)
    print("VALID", len(seen), seen)
    val_lemmas = get_lemmas(module_name, seen)
    print("LEN", len(val_lemmas))
    return Dataset(train, test, val), test_lemmas, val_lemmas
