from enum import Enum

from lib.myiter import MyIter
from lex_raw import *

"""
[Note]

Goal: [TacStDecl] -> [Tac]

Works (L means long time):
BGappendix AB, C
BGsection 1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14[L], 15, 16
PFsection 1, 2, 3, 4, 6[L], 7, 8, 9[L], 10[L], 11[L], 12, 13[L], 14[L]

Pop from empty list:
BGsection 3, 4
PFsection 5

BGsection 4:
rank2_coprime_comm_cprod
"""


# -------------------------------------------------
# Data structures

class TacKind(Enum):
    NAME = 1
    ATOMIC = 2
    NOTATION = 3
    ML = 4


def kind_hist():
    return {TacKind.NAME: 0, TacKind.ATOMIC: 0, TacKind.NOTATION: 0,
            TacKind.ML: 0, "EMPTY": 0}


def merge_kind_hist(hist1, hist2):
    for (k, v) in hist2.items():
        hist1[k] += v
    return hist1


def inc_update(hist, key, value):
    if key in hist:
        hist[key] += value
    else:
        hist[key] = value


def merge_hist(hist1, hist2):
    for (k, v) in hist2.items():
        inc_update(hist1, k, v)
    return hist1


def pp_tab(tab, str):
    return tab * " " + str


class RawTac(object):
    def __init__(self, uid, name, kind, bf_decls, af_decls, bods):
        assert isinstance(uid, int)
        assert isinstance(name, str)
        assert isinstance(kind, TacKind)
        for bf_decl in bf_decls:
            assert isinstance(bf_decl, TacStDecl)
        for af_decl in af_decls:
            assert isinstance(af_decl, TacStDecl)
        for body in bods:
            for tac in body:
                assert isinstance(tac, RawTac)

        self.uid = uid
        self.name = name
        self.kind = kind
        self.bf_decls = bf_decls
        self.af_decls = af_decls
        self.bods = bods

    def postorder(self):
        acc = []
        for body in self.bods:
            for tac in body:
                acc += tac.postorder()
                acc += [tac]
        return acc

    def base_stats(self):
        return (self.kind, len(self.bf_decls),
                len(self.bods), len(self.af_decls))

    def rec_stats(self):
        stats = {}
        tacs = self.postorder()
        for tac in tacs:
            key = tac.base_stats()
            inc_update(stats, key, 1)
        return stats

    def pp(self, tab=0):
        epi = pp_tab(tab, "{}({}) {{\n".format(self.name, self.uid))
        bf = pp_tab(tab + 2, "before = [" + ", ".join([str(bf_decl) for bf_decl in self.bf_decls]) + "]\n")
        if self.bods:
            def foo(body):
                if body:
                    return "\n".join([tac.pp(tab + 4) for tac in body])
                else:
                    return pp_tab(tab + 4, "[]")
            s1 = pp_tab(tab + 2, "bods = {\n")
            s2 = ";\n".join([foo(body) for body in self.bods])
            s3 = "\n" + pp_tab(tab + 2, "}\n")
            bods = s1 + s2 + s3
        else:
            bods = pp_tab(tab + 2, "bods = EMP\n")
        af = pp_tab(tab + 2, "after = [" + ", ".join([str(af_decl) for af_decl in self.af_decls]) + "]\n")
        pro = pp_tab(tab, "}")
        return epi + bf + bods + af + pro

    """
    def stats(self):
        # Stats
        ns = {(self.kind, len(self.bf_decls), len(self.bods), len(self.af_decls)): 1}

        # Compute
        for body in self.bods:
            for tac in body:
                ns2 = tac.stats()
                ns = merge_hist(ns, ns2)

        return ns
    """

    def __hash__(self):
        return self.uid

    def __str__(self):
        bf_decl = ", ".join([str(bf_decl) for bf_decl in self.bf_decls])
        af_decls = ", ".join([str(af_decl) for af_decl in self.af_decls])
        bods = "\n".join([", ".join([str(tac) for tac in body]) for body in self.bods])
        return "{}({}; {})".format(self.name, self.uid, bf_decl, af_decls, bods)


# -------------------------------------------------
# Parsing

class TacTreeParser(object):
    def __init__(self, lemma, f_log=False):
        assert isinstance(lemma, LemTacSt)

        self.lemma = lemma
        self.it = MyIter(lemma.decls)
        self.log = []
        self.f_log = f_log
        self.uidcnt = 0
        self.depth = 0
        self.uidstk = []

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            # self.log.append(msg)
            print(" " * (2 * self.depth) + str(msg))

    def _log_acc(self, acc):
        self._mylog("Contents of accumulator")
        for tac in acc:
            self._mylog(tac)

    def _getuid(self):
        uid = self.uidcnt
        self.uidcnt += 1
        return uid

    def parse_atom_call(self):
        # Internal
        it = self.it
        self._mylog("@parse_atom_call:before<{}>".format(it.peek()))

        # Parse before
        befores = []
        start_decl = it.peek()
        while it.peek().hdr.mode == TOK_BEFORE and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            befores += [next(it)]

        # Parse after
        afters = []
        while it.peek().hdr.mode.startswith(TOK_AFTER) and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            afters += [next(it)]

        return RawTac(self._getuid(), befores[0].hdr.tac, TacKind.ATOMIC,
                       befores, afters, [])

    def parse_name_call(self):
        # Internal
        it = self.it
        self._mylog("@parse_name_call:before<{}>".format(it.peek()))

        # Parse before
        befores = []
        start_decl = it.peek()
        while it.peek().hdr.mode == TOK_BEFORE and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            befores += [next(it)]

        # Parse after
        afters = []
        while it.has_next() and \
              it.peek().hdr.mode.startswith(TOK_AFTER) and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            afters += [next(it)]

        return RawTac(self._getuid(), befores[0].hdr.tac, TacKind.NAME,
                       befores, afters, [])

    def parse_notation_call(self):
        # Internal
        it = self.it
        self._mylog("@parse_notation_call:before<{}>".format(it.peek()))

        # Parse before + body
        befores = []
        bods = []
        start_decl = it.peek()
        while it.peek().hdr.mode == TOK_BEFORE and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            befores += [next(it)]
            bods += [self.parse_tactree()]

        # Parse after
        afters = []
        while it.has_next() and \
              it.peek().hdr.mode.startswith(TOK_AFTER) and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            afters += [next(it)]

        return RawTac(self._getuid(), befores[0].hdr.tac, TacKind.NOTATION,
                       befores, afters, bods)

    def parse_ml_call(self):
        # Internal
        it = self.it
        self._mylog("@parse_ml_call:before<{}>".format(it.peek()))

        # Parse before
        befores = []
        start_decl = it.peek()
        while it.peek().hdr.mode == TOK_BEFORE and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            befores += [next(it)]

        # Parse body
        body = self.parse_tactree()
        
        # Parse after
        afters = []
        while it.has_next() and \
              it.peek().hdr.mode.startswith(TOK_AFTER) and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            afters += [next(it)]

        return RawTac(self._getuid(), befores[0].hdr.tac, TacKind.ML,
                       befores, afters, [body])

    def parse_tactree(self):
        """
        Top-level parsing function.
        """
        # Internal
        it = self.it
        self._mylog("@parse_tactree:before<{}>".format(it.peek()))

        # Reconstruct tactic tree
        acc = []
        while it.has_next():
            decl = it.peek()

            # Simple cases
            if decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.kind == "LtacAtomCall":
                acc += [self.parse_atom_call()]

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.kind == "LtacNameCall":
                acc += [self.parse_name_call()]

            # Nested cases
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.kind == "LtacNotationCall":
                if len(self.uidstk) > 0 and \
                   decl.hdr.uid == self.uidstk[-1]:
                    return acc
                else:
                    self.uidstk.append(decl.hdr.uid)
                    acc += [self.parse_notation_call()]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.kind == "LtacNotationCall":
                # TODO(deh): kludge wtf?
                # BGsection4: 1 apply missing
                # BGsection3: 1 apply missing, 1 case missing
                # PFsection5: 1 apply missing
                if len(self.uidstk) == 0:
                    if decl.hdr.loc == "(./BGsection4.v,56364,56374)" or \
                       decl.hdr.loc == "(./BGsection3.v,69788,69814)" or \
                       decl.hdr.loc == "(./BGsection3.v,95041,95066)" or \
                       decl.hdr.loc == "(./PFsection5.v,30836,30858)":
                        return acc
                    else:
                        raise NameError("Wtf {}".format(decl))
                else:
                    self.uidstk.pop()
                    return acc

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.kind == "LtacMLCall":
                acc += [self.parse_ml_call()]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.kind == "LtacMLCall":
                return acc

            else:
                self._log_acc(acc)
                raise NameError("Parsing alignment error {}".format(decl))
        return acc


"""
class Tac(object):
    def __init__(self, uid, terminal=False):
        self.uid = uid
        self.terminal = terminal

    def has_subtac(self):
        # type: Tac -> bool
        raise NotImplementedError

    def in_edge(self):
        # type: Tac -> GoalId
        raise NotImplementedError

    def out_edges(self):
        # type: Tac -> [GoalId]
        raise NotImplementedError

    def __hash__(self):
        return self.uid
"""
