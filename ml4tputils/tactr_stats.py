import json

from build_tactr import *
from tactr import *

class TacTreeStats(object):
    def __init__(self, tactr_file):
        self.f_tactr = open(tactr_file, 'w')
        self.tacstats = {}
        self.edges = 0
        self.weird = 0

    def __exit__(self):
        self.f_tactr.close()

    def tactic_hist(self, tactr):
        """
        # Compute hist
        hist = [0 for _ in TACTICS]
        for k, tacs in tactr.tactics.items():
            tac = tacs[0]
            for idx, tactic in enumerate(TACTICS):
                if tac.name.startswith(tactic):
                    hist[idx] += 1
        hist_p = [(x, y) for x, y in zip(TACTICS, hist)]

        num_tacs = len(tactr.tactics)
        num_gs = len(tactr.goals)
        num_term = len(tactr.term_goals)
        num_err = len(tactr.err_goals)
        term_path_lens = [len(path) for path in tactr.view_term_paths()]
        err_path_lens = [len(path) for path in tactr.view_err_paths()]
        if len(tactr.notok) > 0:
            self.weird += 1
        info = {'hist': hist_p,
                'num_tacs': num_tacs,
                'num_goals': num_gs,
                'num_terminal': num_term,
                'num_error': num_err,
                'term_path_lens': term_path_lens,
                'err_path_lens': err_path_lens,
                'have_info': tactr.view_have_info(),
                'depth_hist': tactr.flatview,
                'notok': tactr.notok}
        self.tacstats[tactr.name] = info

        hist_pp = sorted(hist_p, key=lambda k: (k[1], k[0]), reverse=True)
        return hist_p
        """
        info = tactr.stats()
        self.tacstats[tactr.name] = info
        return tactr.view_tactic_hist()

    def _avg_tactic_hist(self, tachists):
        tachist = [(tactic, 0) for tactic in TACTICS]
        for hist_p in tachists:
            for i, (tactic, cnt) in enumerate(hist_p):
                tachist[i] = (tactic, tachist[i][1] + cnt)

        l = len(tachists)
        avg_tachist = [(tactic, float(cnt) / l) for tactic, cnt in tachist]
        avg_tachist = sorted(avg_tachist, key=lambda k: (k[1], k[0]), reverse=True)

        return avg_tachist

    def log_tactic_hist(self):
        self.f_tactr.write("LEMMA INFO\n")
        for k, info in self.tacstats.items():
            msg = json.dumps({"lemma": k, "info": info})
            print("INFO", info['avg_depth_ctx_items'])
            self.f_tactr.write(msg)
            self.f_tactr.write("\n")

        # self.f_tactr.write("AVERAGE TACTIC HIST")
        # tachists = [info['hist'] for _, info in self.tacstats.items()]
        # avg_tachist = self._avg_tactic_hist(tachists)
        # msg = json.dumps({"avg_tactic_hist": avg_tachist})
        # self.f_tactr.write(msg)
        # self.f_tactr.write("\n")

        self.f_tactr.write("TOTAL {}: WERID: {}\n".format(len(self.tacstats), self.weird))
