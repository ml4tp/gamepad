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

Utility functions.
"""


class NotFound(Exception):
    def __init__(self, msg):
        self.msg = msg


class ImplmentMe(Exception):
    def __init__(self, msg=""):
        self.msg = msg


def pp_tab(tab, s):
    return tab * " " + s


def inc_update(hist, key, value):
    if key in hist:
        hist[key] += value
    else:
        hist[key] = value


def dict_ls_app(dict_, k, v):
    if k in dict_:
        dict_[k] += [v]
    else:
        dict_[k] = [v]


def merge_hist(dict1, dict2):
    d = dict([(k, v) for k, v in dict1.items()])
    for k, v in dict2.items():
        if k in d:
            d[k] += v
        else:
            d[k] = v
    return d


def merge_hists(dicts):
    if len(dicts) <= 0:
        return {}
    elif len(dicts) == 1:
        return dict([(k, v) for k, v in dicts[0].items()])
    else:
        d = dicts[0]
        dicts = dicts[1:]
        for d2 in dicts:
            d = merge_hist(d, d2)
        return d
