from enum import Enum
import json
import numpy as np

from tactr import *


def avg_hist(stats, f_sort=True):
    """Histogram of tactic vs count"""
    hist = [0 for _ in TACTIC_IDS]
    total = len(stats)
    for lemma, info in stats.items():
        for idx, cnt in enumerate(info['hist']):
            hist[idx] += cnt

    avg = [(ID_TACTIC_MAP[idx], float(cnt) / total) for idx, cnt in enumerate(hist)]
    if f_sort:
        return sorted(avg, key=lambda k: (k[1], k[0]), reverse=True)
    else:
        return avg

def avg_tacs(stats):
    """Average number of tactics used per lemma"""
    return np.mean([info['num_tacs'] for _, info in stats.items()])

def avg_goals(stats):
    """Average number of goals in each lemma"""
    return np.mean([info['num_goals'] for _, info in stats.items()])

def avg_term(stats):
    """Average number of terminal states in each lemma"""
    return np.mean([info['num_term'] for _, info in stats.items()])

def avg_err(stats):
    """Average number of error states in each lemma"""
    return np.mean([info['num_err'] for _, info in stats.items()])

def gather_term_path_lens(stats):
    """Histogram of terminal path-length vs count"""
    MAX_LEN = 100
    term_path_lens = []
    for lemma, info in stats.items():
        hist = [0 for _ in range(MAX_LEN)]
        for l in info['term_path_lens']:
            if l < MAX_LEN:
                hist[l] += 1
        term_path_lens += [hist]
    return term_path_lens

def gather_err_path_lens(stats):
    """Histogram of error path-length vs count"""
    MAX_LEN = 100
    err_path_lens = []
    for lemma, info in stats.items():
        hist = [0 for _ in range(MAX_LEN)]
        for l in info['err_path_lens']:
            if l < MAX_LEN:
                hist[l] += 1
        err_path_lens += [hist]
    return err_path_lens

def gather_have_info(stats):
    """Average tactic size and length of path per lemma"""
    acc_size_ftac = []
    acc_size_path = []
    for lemma, info in stats.items():
        hinfo = info['have_info']
        ftac = hinfo[0]
        size_ftac = hinfo[1]
        size_path = len(hinfo[2])
        acc_size_ftac += [size_ftac]
        acc_size_path += [size_path]

    return np.mean(acc_size_ftac), np.mean(acc_size_path)

class DepthMode(Enum):
    CONTEXT = 0
    GOAL = 1

def avg_depth_size(stats, mode):
    """Histogram of depth vs context/goal size"""
    if mode == DepthMode.CONTEXT:
        projfn = lambda info: info['avg_depth_ctx_size']
    elif mode == DepthMode.GOAL:
        projfn = lambda info: info['avg_depth_goal_size']
    else:
        raise NameError("Mode {} not supported".format(mode))

    MAX_DEPTH = max([max([depth for depth, _ in projfn(info)]) for _, info in stats.items()]) + 1
    hist = {}
    for depth in range(MAX_DEPTH):
        hist[depth] = 0

    for lemma, info in stats.items():
        for depth, size in projfn(info):
            hist[depth] += size
    total = len(stats)
    for depth in range(MAX_DEPTH):
        hist[depth] /= total
    del hist[0]
    return hist


def compute_all(stats):
    # Hist[tactic, cnt]
    print(avg_hist(stats, f_sort=True))

    # var, max, min, quartiles
    print("Average # of tactics (per lemma): {}".format(avg_tacs(stats)))
    # var, max, min, quartiles
    print("Average # of goals (per lemma): {}".format(avg_goals(stats)))
    # var, max, min, quartiles
    print("Average # of terminal states (per lemma): {}".format(avg_term(stats)))
    # var, max, min, quartiles
    print("Average # of error states (per lemma): {}".format(avg_err(stats)))
    # var, max, min, quartiles
    # print(gather_have_info(stats))

    # Matrix[lemma#, lens]
    print(gather_term_path_lens(stats))
    # Matrix[lemma#, lens]
    print(gather_err_path_lens(stats))
    # Hist[depth, avg]
    print(avg_depth_size(stats, DepthMode.CONTEXT))
    # Hist[depth, avg]
    print(avg_depth_size(stats, DepthMode.GOAL))

def load_tactr_stats(filename):
    stats = {}
    with open(filename, 'r') as f:
        for line in f:
            if line.startswith("LEMMA INFO"):
                pass
            elif line.startswith("TOTAL"):
                pass
            else:
                line = line.strip()
                x = json.loads(line)
                stats[x['lemma']] = x['info']
    return stats

if __name__ == "__main__":
    stats = load_tactr_stats("log/tactr-build-10.log")
    compute_all(stats)