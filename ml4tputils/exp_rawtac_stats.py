from enum import Enum
import json

from lib.myiter import MyIter
from recon.lex_raw import *
from recon.parse_tacst import *

"""
Hypothesis:
- Notation
  1. [V] # before >= 1
  2. [V] # before = # bods (hence # bods >= 1)
  3. [TESTME] should be able to connect the dots, i.e., no discontiguous goal ids
     * Since # before = # bods, for each body in bods, check for tac = last(body) that tac.afters connects with the current afters
     * Record non-terminal goal ids that were not matched
- ML
  1. [V] # before >= 1
  2. # body = 1
  3. [TESTME] Depending on the tactic, can either connect the dots or have discontinguos goal ids
     * For each ML-tactic, record:
       * tactic
       * # before, # after, length of body = bods[0] (since #bods = 1)
       * matched before ids (index in body?)
       * matched after ids (index in body?)
       * non-terminal goal ids that were not matched
- Atomic:
  1. [V] direct match or branching
  2. [V] no body, i.e., bods = []
- Name
  1. [V] direct match
  2. [V] no body, i.e., bods = []
"""


class RawStats(object):
    def __init__(self, rawtac_file, f_print=False):
        self.file = open(rawtac_file, "w")
        self.f_print = f_print
        self.mltacs = {}
        self.mlstats = {}
        self.nametacs = {}
        self.namestats = {}
        self.notok = []
        self.total = 0

    def __exit__(self):
        self.file.close()

    def _mylog(self, msg):
        self.file.write(msg)
        self.file.write("\n")
        if self.f_print:
            print(msg)

    def log_namestats(self):
        self._mylog("NAMETACS")
        for k, v in self.nametacs.items():
            self._mylog("{}, {}".format(k, v))
        self._mylog("NAMESTATS")
        for k, v in self.namestats.items():
            self._mylog("{}, {}, {}, {}, {}".format(k[0], k[1], k[2], k[3], v))

    def log_mlstats(self):
        self._mylog("MLTACS")
        for k, v in self.mltacs.items():
            self._mylog("{}, {}".format(k, v))
        self._mylog("MLSTATS")
        for k, v in self.mlstats.items():
            self._mylog("{}, {}, {}, {}, {}".format(k[0], k[1], k[2], k[3], v))

    def log_notok(self):
        self._mylog("NOTOK: {}  TOTAL: {}".format(len(self.notok), self.total))
        self._mylog(", ".join([ str(x) for x in self.notok]))

    def fo_bfaf_match(self, bfaf_decls, body, projfn):
        """
        bfaf_decls : either bf_decls or af_decls
        body       : tactic body that we are searching in
        projfn     : either projects bf_decls or af_decls
        """
        # 1st order match befores/afters
        connected = {}
        for bfaf_decl in bfaf_decls:
            connected[bfaf_decl.hdr.gid] = []
        isolated = {}
        for i, tac_p in enumerate(body):
            for j, bfaf_decl_p in enumerate(projfn(tac_p)):
                if bfaf_decl_p.hdr.gid in connected:
                    connected[bfaf_decl_p.hdr.gid] += [(i, j)]
                else:
                    if bfaf_decl_p.hdr.gid in isolated:
                        isolated[bfaf_decl_p.hdr.gid] += [(i, j)]
                    else:
                        isolated[bfaf_decl_p.hdr.gid] = [(i, j)]
        return connected, isolated

    def stats_terminal(self, tac):
        # Non-terminal goal ids
        ending = {"open": 0, "error": 0, "solved": 0}
        for af_decl in tac.af_decls:
            if af_decl.hdr.gid == GID_SOLVED:
                ending["solved"] += 1
            elif af_decl.hdr.mode == "afterE":
                ending["error"] += 1
            else:
                ending["open"] += 1
        return ending

    def stats_ml_tac(self, tac):
        if tac.name.startswith("<"):
            end = tac.name.find(">") + 1
            name = tac.name[:end]
            if name in self.mltacs:
                self.mltacs[name] += 1
            else:
                self.mltacs[name] = 1

            nbf = len(tac.bf_decls)
            nbody = len(tac.bods[0])
            naf = len(tac.af_decls)
            key = (name, nbf, nbody, naf)
            if key in self.mlstats:
                self.mlstats[key] += 1
            else:
                self.mlstats[key] = 1

    def stats_notation(self, lemma, tac):
        # Basic stats
        nbf = len(tac.bf_decls)
        nbods = len(tac.bods)
        assert nbf == nbods
        naf = len(tac.af_decls)

        # First-order befores matching
        bf_conns = []
        bf_isos = []
        for i, (bf_decl, body) in enumerate(zip(tac.bf_decls, tac.bods)):
            bf_conn, bf_iso = self.fo_bfaf_match([bf_decl], body,
                                                 lambda tac: tac.bf_decls)
            connected = bf_conn[bf_decl.hdr.gid]
            if len(connected) == 1 and connected[0][0] == 0:
                pass
            else:
                bf_conns += [(i, bf_conn[bf_decl.hdr.gid])]

            if bf_iso:
                bf_isos += [(i, bf_iso)]

        # First-order afters matching
        af_conn = {}
        empty = []
        for af_decl in tac.af_decls:
            af_conn[af_decl.hdr.gid] = []
        for af_decl in tac.af_decls:
            for i, body in enumerate(tac.bods):
                if body:
                    for af_decl_p in body[-1].af_decls:
                        if af_decl.hdr.gid == af_decl_p.hdr.gid:
                            af_conn[af_decl.hdr.gid] += [(i, len(body) - 1)]
                else:
                    empty += [i]

        # Non-terminal goal ids
        ending = self.stats_terminal(tac)

        # Heuristic for "ok-looking" tactic
        isok = True
        if bf_conns or bf_isos:
            isok = False
        if len(tac.af_decls) == 1 and tac.af_decls[0].hdr.gid == GID_SOLVED:
            pass
        else:
            open_ = 0
            for k, v in af_conn.items():
                if k != GID_SOLVED:
                    open_ += len(v)
            if open_ != len(tac.af_decls):
                isok = False

        msg = json.dumps({"lemma": lemma.name, "isok": isok,
                          "uid": tac.uid, "tac": tac.name, "kind": "NOTATION",
                          "nbf": nbf, "nbods": nbods, "naf": naf,
                          "bf_conn": bf_conns, "bf_iso": bf_isos,
                          "af_conn": af_conn, "empty_body": empty,
                          "ending": ending})
        self._mylog(msg)

        # Recursively check body
        for body in tac.bods:
            self.stats_tacs(lemma, body)

        if not isok:
            self.notok += [(lemma.name, tac.uid, tac.name, tac.kind, naf, nbods, nbf)]
        return isok

    def stats_ml(self, lemma, tac):
        # Basic stats
        nbf = len(tac.bf_decls)
        assert len(tac.bods) == 1
        body = tac.bods[0]
        nbody = len(body)
        naf = len(tac.af_decls)

        self.stats_ml_tac(tac)

        # First-order connection stats
        bf_conn, bf_iso = self.fo_bfaf_match(tac.bf_decls, body, lambda tac: tac.bf_decls)
        af_conn, af_iso = self.fo_bfaf_match(tac.af_decls, body, lambda tac: tac.af_decls)

        # Non-terminal goal ids
        ending = self.stats_terminal(tac)

        # Heuristic for "ok-looking" tactic
        isok = True
        if af_iso:
            isok = False
        for k, v in bf_conn.items():
            if len(v) != 1:
                isok = False
        """
        total = 0
        for k, v in af_conn.items():
            total += len(v)
        if total != len(tac.af_decls):
            isok = False
        """

        msg = json.dumps({"lemma": lemma.name, "isok": isok,
                          "uid": tac.uid, "tac": tac.name, "kind": "ML",
                          "nbf": nbf, "nbody": nbody, "naf": naf,
                          "bf_conn": bf_conn, "bf_iso": bf_iso,
                          "af_conn": af_conn, "af_iso": af_iso,
                          "ending": ending})
        self._mylog(msg)

        # Recursively check body
        self.stats_tacs(lemma, body)

        if not isok:
            self.notok += [(lemma.name, tac.uid, tac.name, tac.kind, naf, nbody, nbf)]
        return isok

    def stats_name(self, lemma, tac):
        name = tac.name
        if name in self.nametacs:
            self.nametacs[name] += 1
        else:
            self.nametacs[name] = 1

        nbf = len(tac.bf_decls)
        nbods = len(tac.bods)
        naf = len(tac.af_decls)
        key = (name, nbf, nbods, naf)
        if key in self.namestats:
            self.namestats[key] += 1
        else:
            self.namestats[key] = 1

    def stats_tac(self, lemma, tac):
        self.total += 1
        if tac.kind == TacKind.ML:
            self.stats_ml(lemma, tac)
        elif tac.kind == TacKind.NOTATION:
            self.stats_notation(lemma, tac)
        elif tac.kind == TacKind.NAME:
            self.stats_name(lemma, tac)

    def stats_tacs(self, lemma, tacs):
        # Compute some stats on RawTacs
        for tac in tacs:
            self.stats_tac(lemma, tac)


# -------------------------------------------------
# TODO(deh): use?

def kind_hist():
    return {TacKind.NAME: 0, TacKind.ATOMIC: 0, TacKind.NOTATION: 0,
            TacKind.ML: 0, "EMPTY": 0}


def merge_kind_hist(hist1, hist2):
    for (k, v) in hist2.items():
        hist1[k] += v
    return hist1


def merge_hist(hist1, hist2):
    for (k, v) in hist2.items():
        inc_update(hist1, k, v)
    return hist1
