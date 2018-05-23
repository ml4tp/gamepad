from enum import Enum
import json
import numpy as np
import scipy.stats as sps

from lib.myutil import inc_update
from coq.tactics import TACTIC_HIST
from coq.constr_util import COQEXP_HIST


# -------------------------------------------------
# Utility

def load_tactr_stats(filename):
    my_stats = {}
    unique = {'const': 0, 'ind': 0, 'conid': 0}
    with open(filename, 'r') as f:
        for line in f:
            if line.startswith("LEMMA INFO"):
                pass
            elif line.startswith("TOTAL"):
                pass
            elif line.startswith("UNIQUE-SORT"):
                toks = line.split()
                unique['sort'] = int(toks[1].strip())
            elif line.startswith("UNIQUE-CONST"):
                toks = line.split()
                unique['const'] = int(toks[1].strip())
            elif line.startswith("UNIQUE-IND"):
                toks = line.split()
                unique['ind'] = int(toks[1].strip())
            elif line.startswith("UNIQUE-CONID"):
                toks = line.split()
                unique['conid'] = int(toks[1].strip())
            elif line.startswith("UNIQUE-EVAR"):
                toks = line.split()
                unique['evar'] = int(toks[1].strip())
            elif line.startswith("UNIQUE-FIX"):
                toks = line.split()
                unique['fix'] = int(toks[1].strip())
            elif line.startswith("NUM_IARG"):
                pass
            elif line.startswith("NUM_ARGS"):
                pass
            else:
                line = line.strip()
                x = json.loads(line)
                my_stats[x['lemma']] = x['info']
    return my_stats, unique


class DepthMode(Enum):
    CHAR_CTX = 0
    CHAR_GOAL = 1
    AST_CTX = 2
    AST_GOAL = 3


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
        hist = TACTIC_HIST.empty()
        for lemma, info in self.stats.items():
            hist = TACTIC_HIST.merge(hist, info['hist'])

        total = len(self.stats)
        avg = TACTIC_HIST.map(hist, lambda x: x / total)
        return TACTIC_HIST.view(avg, f_sort)

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
        max_len = 100
        term_path_lens = []
        for lemma, info in self.stats.items():
            hist = [0 for _ in range(max_len)]
            for l in info['term_path_lens']:
                if l < max_len:
                    hist[l] += 1
            term_path_lens += [hist]
        return term_path_lens

    def gather_err_path_lens(self):
        """Histogram of error path-length vs count"""
        max_len = 100
        err_path_lens = []
        for lemma, info in self.stats.items():
            hist = [0 for _ in range(max_len)]
            for l in info['err_path_lens']:
                if l < max_len:
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
                # ftac = hinfo[0]
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
        if mode == DepthMode.CHAR_CTX:
            projfn = lambda info: info['avg_depth_ctx_size']
        elif mode == DepthMode.CHAR_GOAL:
            projfn = lambda info: info['avg_depth_goal_size']
        elif mode == DepthMode.AST_CTX:
            projfn = lambda info: info['avg_depth_astctx_size']
        elif mode == DepthMode.AST_GOAL:
            projfn = lambda info: info['avg_depth_astgoal_size']
        else:
            raise NameError("Mode {} not supported".format(mode))

        max_depth = max([max([depth for depth, _ in projfn(info)]) for _, info in self.stats.items()]) + 1
        hist = {}
        for depth in range(max_depth):
            hist[depth] = 0

        norm = [0 for _ in range(0, max_depth)]
        for lemma, info in self.stats.items():
            for depth, dsize in projfn(info):
                hist[depth] += dsize
                norm[depth] += 1

        for depth in range(1, max_depth):
            if norm[depth] > 0:
                hist[depth] /= norm[depth]
        del hist[0]
        return hist

    def coqexp_hist(self, f_sort=True):
        hists = [info['hist_coqexp'] for lemma, info in self.stats.items()]
        hist = COQEXP_HIST.merges(hists)
        return COQEXP_HIST.view(hist, f_sort)

    def coqexp_comp_p(self, hist_key, f_avg=True, f_trunc=True):
        hist = {}
        for lemma, info in self.stats.items():
            for x in info[hist_key]:
                inc_update(hist, x, 1.0)

        maxsize = max([k for k, v in hist.items()])
        if f_trunc:
            hist_p = {}
            total = np.sum([v for k, v in hist.items()])
            acc = 0.0
            for k in range(maxsize + 1):
                if k in hist:
                    acc += hist[k]
                    hist_p[k] = hist[k]
                else:
                    hist_p[k] = 0.0
                if acc / total > 0.95:
                    break
        else:
            hist_p = hist

        if f_avg:
            num_lemmas = len(self.stats)
            for k, v in hist_p.items():
                hist_p[k] /= num_lemmas

        return hist_p, maxsize


if __name__ == "__main__":
    stats = load_tactr_stats("data/feit-tactr.log")
    tactr_stats = TacTrStats(stats)
