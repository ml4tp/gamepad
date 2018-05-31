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

from apted import APTED
from apted.helpers import Tree
import editdistance


"""
[Note]

For edit-distance calculations. Tree edit distance is really slow.
"""


def kern2tr(tactr, kdx):
    return Tree("FOO").from_text(tactr.decoder.decode_exp_by_key(kdx).apted_tree())


def kern_tree_edit_dist(tactr, kdx1, kdx2):
    return APTED(kern2tr(tactr, kdx1), kern2tr(tactr, kdx2)).compute_edit_distance()


def mid2tr(tactr, mdx):
    return Tree("FOO").from_text(tactr.mid_decoder.decode_exp_by_key(mdx).apted_tree())


def mid_tree_edit_dist(tactr, kdx1, kdx2):
    return APTED(mid2tr(tactr, kdx1), mid2tr(tactr, kdx2)).compute_edit_distance()


def tree_edit_dist(tr1, tr2):
    return APTED(tr1, tr2).compute_edit_distance()


def kern2str(tactr, kdx):
    return tactr.decoder.decode_exp_by_key(kdx).apted_tree()


def mid2str(tactr, mdx):
    return tactr.mid_decoder.decode_exp_by_key(mdx).apted_tree()


def string_edit_dist(str1, str2):
    return editdistance.eval(str1, str2)
