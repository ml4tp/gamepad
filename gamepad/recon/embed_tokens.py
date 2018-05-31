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

"""
[Note]

Convert "tokens" in dataset into unique integers for embeddings.
"""


class EmbedTokens(object):
    """
    Collect all tokens in the data-set.
    """
    def __init__(self, f_mid=False):
        self.unique_sort = set()
        self.unique_const = set()
        self.unique_ind = set()
        self.unique_conid = set()
        self.unique_evar = set()
        self.unique_fix = set()

        self.f_mid = f_mid

    def _tokens_to_idx(self, unique):
        ls = list(unique)
        tok_to_idx = {}
        for idx, tok in enumerate(ls):
            tok_to_idx[tok] = idx
        return tok_to_idx

    def tokens_to_idx(self):
        sort_to_idx = self._tokens_to_idx(self.unique_sort)
        const_to_idx = self._tokens_to_idx(self.unique_const)
        ind_to_idx = self._tokens_to_idx(self.unique_ind)
        conid_to_idx = self._tokens_to_idx(self.unique_conid)
        evar_to_idx = self._tokens_to_idx(self.unique_evar)
        fix_to_idx = self._tokens_to_idx(self.unique_fix)

        return (sort_to_idx, const_to_idx, ind_to_idx,
                conid_to_idx, evar_to_idx, fix_to_idx)

    def tokenize_tactr(self, tactr):
        if self.f_mid:
            tokens = tactr.tokenize_mid()
        else:
            tokens = tactr.tokenize_kern()
        self.unique_sort = self.unique_sort.union(tokens[0])
        self.unique_const = self.unique_const.union(tokens[1])
        self.unique_ind = self.unique_ind.union(tokens[2])
        self.unique_conid = self.unique_conid.union(tokens[3])
        self.unique_evar = self.unique_evar.union(tokens[4])
        self.unique_fix = self.unique_fix.union(tokens[5])

    def tokenize_tactrs(self, tactrs):
        for tactr in tactrs:
            self.tokenize_tactr(tactr)
