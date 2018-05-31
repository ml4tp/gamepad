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

import lib.sexpdata as sexpdata


"""
[Note]

Functionality for s-expression parsing.
"""


def sexpr_strify(sexpr):
    ty = type(sexpr)
    if ty is sexpdata.Symbol:
        return sexpr._val.replace("!@#", "'")
    elif ty is bool:
        return str(sexpr)
    else:
        raise NameError("Cannot strify {}::{}".format(sexpr, type(sexpr)))


def sexpr_unpack(sexpr):
    try:
        tag = sexpr[0]
        body = sexpr[1:]
        return tag._val, body
    except:
        return sexpr._val, None
