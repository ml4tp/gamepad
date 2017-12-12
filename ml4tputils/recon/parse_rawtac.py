from enum import Enum

from coq.tactics import TacKind
from lib.gensym import GenSym
from lib.myiter import MyIter
from lib.myutil import pp_tab, inc_update
from recon.tokens import *
from recon.parse_raw import TacStDecl, LemTacSt

"""
[Note]

parse_rawtacs: [TacStDecl] -> [RawTac]

bf body af af
bf body af
"""


# -------------------------------------------------
# Data structures

class RawTac(object):
    def __init__(self, uid, name, tkind, ftac, bf_decl, af_decls, body):
        assert isinstance(uid, int)
        assert isinstance(name, str)
        assert isinstance(tkind, TacKind)
        assert isinstance(bf_decl, TacStDecl)
        for af_decl in af_decls:
            assert isinstance(af_decl, TacStDecl)
        for rawtac in body:
            assert isinstance(rawtac, RawTac)

        self.uid = uid             # UID for raw tactic
        self.name = name           # Name of the tactic
        self.tkind = tkind         # Kind of the tactic
        self.ftac = ftac           # Full tactic
        self.bf_decl = bf_decl     # Before declarations
        self.af_decls = af_decls   # After declarations
        self.body = body           # Raw tactics in the body

    def pp(self, tab=0):
        epi = pp_tab(tab, "{}({}) {{\n".format(self.name, self.uid))
        bf = pp_tab(tab + 2, "bf_decl = {}\n".format(str(self.bf_decl)))
        if self.body:
            s1 = pp_tab(tab + 2, "bods = {\n")
            s2 = ";\n".join([rawtac.pp(tab + 4) for rawtac in self.body])
            s3 = "\n" + pp_tab(tab + 2, "}\n")
            body = s1 + s2 + s3
        else:
            body = pp_tab(tab + 2, "body = EMP\n")
        af = pp_tab(tab + 2, "af_decls = [{}]\n".format(", ".join([str(af_decl) for af_decl in self.af_decls])))
        pro = pp_tab(tab, "}")
        return epi + bf + body + af + pro

    def __hash__(self):
        return self.uid


# -------------------------------------------------
# Parsing

class RawTacParser(object):
    def __init__(self, lemma, f_log=False):
        assert isinstance(lemma, LemTacSt)

        # Internal state
        self.f_log = f_log
        self.lemma = lemma
        self.it = MyIter(lemma.decls)

        self.gensym = GenSym()          # RawTac uid gensym
        self.depth = 0                  # Nesting depth

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            print(" " * (2 * self.depth) + str(msg))

    def _log_acc(self, acc):
        self._mylog("Contents of accumulator")
        for tac in acc:
            self._mylog(tac)

    def _fresh_uid(self):
        return self.gensym.gensym()

    def parse_name_call(self):
        # Internal
        it = self.it
        self._mylog("@parse_name_call:before<{}>".format(it.peek()))

        # Parse before
        befores = []
        start_decl = it.peek()
        while (it.peek().hdr.mode == TOK_BEFORE and
               it.peek().hdr.callid == start_decl.hdr.callid):
            befores += [next(it)]

        # Parse after
        afters = []
        while (it.has_next() and
               is_after(it.peek().hdr.mode) and
               it.peek().hdr.callid == start_decl.hdr.callid):
            afters += [next(it)]

        rawtacs = []
        for bf_decl, af_decl in zip(befores, afters):
            rawtacs += [RawTac(self._fresh_uid(), start_decl.hdr.tac,
                               TacKind.NAME, start_decl.hdr.ftac,
                               bf_decl, [af_decl], [])]
        return rawtacs

    def rec_parse_rawtac(self):
        self.depth += 1
        body = self.parse_rawtacs()
        self.depth -= 1
        return body

    def parse_nested(self, tackind):
        # Internal
        it = self.it
        self._mylog("@parse_nested:before<{},{}>".format(it.peek(), tackind))

        rawtacs = []
        start_decl = it.peek()
        while it.has_next() and it.peek().hdr.callid == start_decl.hdr.callid:
            bf_decl = next(it)
            body = self.rec_parse_rawtac()
            af_decls = []
            while (it.has_next() and
                   is_after(it.peek().hdr.mode) and
                   it.peek().hdr.callid == start_decl.hdr.callid):
                af_decls += [next(it)]
            rawtacs += [RawTac(self._fresh_uid(), start_decl.hdr.tac,
                               tackind, start_decl.hdr.ftac, bf_decl,
                               af_decls, body)]
        return rawtacs

    def parse_rawtacs(self):
        """
        Top-level parsing function.
        """
        # Internal
        it = self.it
        self._mylog("@parse_rawtac:before<{}>".format(it.peek()))

        # Reconstruct tactic tree
        acc = []
        while it.has_next():
            decl = it.peek()

            # Simple cases
            if decl.hdr.mode == TOK_BEFORE and decl.hdr.kind == TOK_NAME:
                acc += self.parse_name_call()

            # Nested cases
            elif decl.hdr.mode == TOK_BEFORE and decl.hdr.kind == TOK_NOTATION:
                acc += self.parse_nested(TacKind.NOTATION)
            elif is_after(decl.hdr.mode) and decl.hdr.kind == TOK_NOTATION:
                return acc

            elif decl.hdr.mode == TOK_BEFORE and decl.hdr.kind == TOK_ATOMIC:
                acc += self.parse_nested(TacKind.ATOMIC)
            elif is_after(decl.hdr.mode) and decl.hdr.kind == TOK_ATOMIC:
                return acc

            elif decl.hdr.mode == TOK_BEFORE and decl.hdr.kind == TOK_ML:
                acc += self.parse_nested(TacKind.ML)
            elif is_after(decl.hdr.mode) and decl.hdr.kind == TOK_ML:
                return acc

            else:
                self._log_acc(acc)
                raise NameError("Parsing alignment error {}".format(decl))
        return acc
