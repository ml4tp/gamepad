from enum import Enum
import json
import numpy as np
import scipy.stats as sps

from tactr import *


# -------------------------------------------------
# Utility

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


class DepthMode(Enum):
    CONTEXT = 0
    GOAL = 1


# -------------------------------------------------
# Tactic Tree Statistics

class TacTrStats(object):
    def __init__(self, stats):
        self.stats = stats

    def _mylog(self, msg):
        print(msg)

    def _descrip_stats(self, ls):
        _min = min(ls)
        _max = max(ls)
        mean = np.mean(ls)
        sdev = np.sqrt(sps.moment(ls, moment=2))
        kurt = sps.kurtosis(ls)

        self._mylog("Min:       {}".format(_min))
        self._mylog("Max:       {}".format(_max))
        self._mylog("Mean:      {}".format(mean))
        self._mylog("Sdev:      {}".format(sdev))
        self._mylog("Kurtosis:  {}".format(kurt))

        return _min, _max, mean, sdev

    def avg_hist(self, f_sort=True):
        """Histogram of tactic vs count"""
        hist = [0 for _ in TACTIC_IDS]
        total = len(self.stats)
        for lemma, info in self.stats.items():
            for idx, cnt in enumerate(info['hist']):
                hist[idx] += cnt

        avg = [(ID_TACTIC_MAP[idx], float(cnt) / total) for idx, cnt in enumerate(hist)]
        if f_sort:
            return sorted(avg, key=lambda k: (k[1], k[0]), reverse=True)
        else:
            return avg

    def descrip_tacs(self):
        """Descriptive statistics on number of tactics used per lemma"""
        self._mylog("Statistics on number of tactics used (across lemmas)")
        ls = [info['num_tacs'] for _, info in self.stats.items()]
        return self._descrip_stats(ls)

    def descrip_tacsts(self):
        """Descriptive statistics on number of tactic states present in each lemma"""
        self._mylog("Statistics on number of tactic states present (across lemmas)")
        ls = [info['num_goals'] for _, info in self.stats.items()]
        return self._descrip_stats(ls)

    def descrip_term(self):
        """Descriptive statistics on number of terminal states in each lemma"""
        self._mylog("Statistics on number of terminal states (across lemmas)")
        ls = [info['num_term'] for _, info in self.stats.items()]
        return self._descrip_stats(ls)

    def descrip_deadend(self):
        """Descriptive number of deadend states in each lemma"""
        self._mylog("Statistics on number of deadend states (across lemmas)")
        ls = [info['num_err'] for _, info in self.stats.items()]
        return self._descrip_stats(ls)

    def gather_term_path_lens(self):
        """Histogram of terminal path-length vs count"""
        MAX_LEN = 100
        term_path_lens = []
        for lemma, info in self.stats.items():
            hist = [0 for _ in range(MAX_LEN)]
            for l in info['term_path_lens']:
                if l < MAX_LEN:
                    hist[l] += 1
            term_path_lens += [hist]
        return term_path_lens

    def gather_err_path_lens(self):
        """Histogram of error path-length vs count"""
        MAX_LEN = 100
        err_path_lens = []
        for lemma, info in self.stats.items():
            hist = [0 for _ in range(MAX_LEN)]
            for l in info['err_path_lens']:
                if l < MAX_LEN:
                    hist[l] += 1
            err_path_lens += [hist]
        return err_path_lens

    def gather_have_info(self):
        """Average tactic size and length of path per lemma"""
        acc_size_ftac = []
        acc_size_path = []
        for lemma, info in self.stats.items():
            hinfos = info['have_info']
            for hinfo in hinfos:
                ftac = hinfo[0]
                size_ftac = hinfo[1]
                size_path = len(hinfo[2])
                acc_size_ftac += [size_ftac]
                acc_size_path += [size_path]

        self._mylog("Statistics on size of haves (across lemmas)")
        self._descrip_stats(acc_size_ftac)
        self._mylog("Statistics on length of have paths (across lemmas)")
        self._descrip_stats(acc_size_path)
        return acc_size_ftac, acc_size_path

    def avg_depth_size(self, mode):
        """Histogram of depth vs context/goal size"""
        if mode == DepthMode.CONTEXT:
            projfn = lambda info: info['avg_depth_astctx_size']
        elif mode == DepthMode.GOAL:
            projfn = lambda info: info['avg_depth_astgoal_size']
        else:
            raise NameError("Mode {} not supported".format(mode))

        MAX_DEPTH = max([max([depth for depth, _ in projfn(info)]) for _, info in self.stats.items()]) + 1
        hist = {}
        for depth in range(MAX_DEPTH):
            hist[depth] = 0

        norm = [0 for _ in range(0, MAX_DEPTH)]
        print("Lemmas", len(self.stats.items()))
        for lemma, info in self.stats.items():
            print("HERE", lemma, info['avg_depth_astctx_size'])
        maxsize = 0
        for lemma, info in self.stats.items():
            for depth, dsize in projfn(info):
                maxsize = max(dsize, maxsize)
                if dsize > 1e99:
                    print(info)
                    print("Maxsize and size", lemma, maxsize, dsize)
                hist[depth] += dsize
                norm[depth] += 1
        # print("FUCK", hist)
        """
        for lemma, info in self.stats.items():
            max_depth = max([depth for depth, _ in projfn(info)]) + 1
            for depth in range(0, max_depth):
                norm[depth] += 1
        """
        # print("DEFINITELY FUCK", norm)

        for depth in range(1, MAX_DEPTH):
            hist[depth] /= norm[depth]
        # print("WTF", hist)
        del hist[0]
        return hist


if __name__ == "__main__":
    stats = load_tactr_stats("log/tactr-build-10.log")
    tactr_stats = TacTrStats(stats)
    # compute_all(stats)

"""
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
"""
