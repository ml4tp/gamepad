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

Contains tokens for proof format.
"""


# -------------------------------------------------
# Tokens

TOK_BEFORE = "bf"
TOK_AFTER = "af"
TOK_DEAD = "dead"

TOK_ATOMIC = "Atom"
TOK_ML = "ML"
TOK_NAME = "Name"
TOK_NOTATION = "Not"

TOK_SEP = "{!}"
TOK_DIV = "============================"
TOK_BEG_TAC_ST = "bg(ts)"
TOK_END_TAC_ST = "en(ts)"
TOK_BEG_SUB_PF = "bg(spf)"
TOK_END_SUB_PF = "en(spf)"
TOK_BEG_PF = "bg(pf)"
TOK_END_PF = "en(pf)"
TOK_TYPS = "Typs"
TOK_BODS = "Bods"
TOK_CONSTRS = "Constrs"
TOK_PRTYPS = "PrTyps"
TOK_PRBODS = "PrBods"
TOK_PRGLS = "PrGls"
TOK_BEG_INC = "bg(inc)"
TOK_END_INC = "en(inc)"


def is_after(mode):
    return mode.startswith(TOK_AFTER) or mode.startswith(TOK_DEAD)


# -------------------------------------------------
# Random goal stuff

GID_SOLVED = -1
GID_FAILED = -2
