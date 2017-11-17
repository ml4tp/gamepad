from enum import Enum

import coq_ast
from lib.gensym import GenSym
from lib.myiter import MyIter
from lib.myutil import pp_tab, inc_update
from lex_raw import *

"""
[Note]

Goal: [TacStDecl] -> [RawTac]
Group TacStDecls into a RawTac that contains the effects of a tactic call.

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


class RawTac(object):
    def __init__(self, uid, name, kind, ftac, bf_decls, af_decls, bods):
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

        self.uid = uid             # Unique identifier
        self.name = name           # Name of the tactic
        self.kind = kind           # Kind of the tactic
        self.ftac = ftac           # Full tactic
        self.bf_decls = bf_decls   # Before declarations
        self.af_decls = af_decls   # After declarations  
        self.bods = bods           # Raw tactics in the body

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

    def postorder(self):
        acc = []
        for body in self.bods:
            for tac in body:
                acc += tac.postorder()
                acc += [tac]
        acc += [self]
        return acc

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

    def __hash__(self):
        return self.uid

    def __str__(self):
        bf_decl = ", ".join([str(bf_decl) for bf_decl in self.bf_decls])
        af_decls = ", ".join([str(af_decl) for af_decl in self.af_decls])
        bods = "\n".join([", ".join([str(tac) for tac in body]) for body in self.bods])
        return "{}({}; {}; {}; {})".format(self.name, self.uid, bf_decl, af_decls, bods)


# -------------------------------------------------
# Parsing

class TacTreeParser(object):
    def __init__(self, lemma, f_log=False):
        assert isinstance(lemma, LemTacSt)

        # Internal state
        self.f_log = f_log
        self.lemma = lemma
        self.it = MyIter(lemma.decls)
        
        self.gensym = GenSym()          # RawTac uid gensym
        self.depth = 0                  # Nesting depth
        self.uidstk = []                # RawTac uid stack (for after)

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            print(" " * (2 * self.depth) + str(msg))

    def _log_acc(self, acc):
        self._mylog("Contents of accumulator")
        for tac in acc:
            self._mylog(tac)

    def _fresh_uid(self):
        return self.gensym.gensym()

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
        while it.has_next() and \
              is_after(it.peek().hdr.mode) and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            afters += [next(it)]

        return RawTac(self._fresh_uid(), befores[0].hdr.tac, TacKind.ATOMIC,
                      befores[0].hdr.ftac, befores, afters, [])

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
              is_after(it.peek().hdr.mode) and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            afters += [next(it)]

        return RawTac(self._fresh_uid(), befores[0].hdr.tac, TacKind.NAME,
                      befores[0].hdr.ftac, befores, afters, [])

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
              is_after(it.peek().hdr.mode) and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            afters += [next(it)]

        return RawTac(self._fresh_uid(), befores[0].hdr.tac, TacKind.NOTATION,
                      befores[0].hdr.ftac, befores, afters, bods)

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
              is_after(it.peek().hdr.mode) and \
              it.peek().hdr.uid == start_decl.hdr.uid:
            afters += [next(it)]

        return RawTac(self._fresh_uid(), befores[0].hdr.tac, TacKind.ML,
                      befores[0].hdr.ftac, befores, afters, [body])

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
                 decl.hdr.kind == TOK_ATOM:
                acc += [self.parse_atom_call()]

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.kind == TOK_NAME:
                acc += [self.parse_name_call()]

            # Nested cases
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.kind == TOK_NOTE:
                if len(self.uidstk) > 0 and \
                   decl.hdr.uid == self.uidstk[-1]:
                    return acc
                else:
                    self.uidstk.append(decl.hdr.uid)
                    acc += [self.parse_notation_call()]
            elif is_after(decl.hdr.mode) and \
                 decl.hdr.kind == TOK_NOTE:
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
                 decl.hdr.kind == TOK_ML:
                acc += [self.parse_ml_call()]
            elif is_after(decl.hdr.mode) and \
                 decl.hdr.kind == TOK_ML:
                return acc

            else:
                self._log_acc(acc)
                raise NameError("Parsing alignment error {}".format(decl))
        return acc
