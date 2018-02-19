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
