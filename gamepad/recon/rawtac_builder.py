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

import lib.sexpdata as sexpdata

from coq.tactics_util import FvsTactic
from coq.tactics import TacKind
from lib.gensym import GenSym
from lib.myiter import MyIter
from lib.myutil import pp_tab
from recon.tokens import *
from recon.tacst_parser import TacStDecl, LemTacSt


"""
[Note]

parse_rawtacs: [TacStDecl] -> [RawTac]

Collects a sequence of tactic state declarations into the effect of a single raw tactic.
bf body af af
bf body af
"""


# -------------------------------------------------
# Data structures

class RawTac(object):
    """
    A RawTac collects all "after" declarations belonging to a single "before" declaration.
    It is also appropriately nested in the sense that it captures the Ltac call stack.
    """
    def __init__(self, uid, name, tkind, ftac, bf_decl, af_decls, body, constrs):
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
        self.constrs = constrs     # Expressions in scope (for Ltac substitution)?

        # Need to change to substitued arguments instead of formal parameters
        if self.constrs:
            self.ftac.pp_tac = self.name
            self.ftac.lids = set()
            self.ftac.gids = set()
            self.ftac.tac_args = self.constrs
            for sexp_gc in self.constrs:
                fvs = FvsTactic()
                self.ftac.lids = self.ftac.lids.union(fvs.fvs_glob_constr(sexp_gc))
                self.ftac.gids = self.ftac.gids.union(fvs.globs)

    def pp(self, tab=0):
        epi = pp_tab(tab, "{}({}, {}) {{\n".format(self.name, self.ftac, self.uid))
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
    """
    Collects a sequence of tactic state declarations into the effect of a single raw tactic.
    """
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

    def parse_constr(self):
        # Internal
        it = self.it
        self._mylog("@parse_constr:before<{}>".format(it.peek()))

        constrs = []
        while it.has_next() and it.peek().hdr.kind.startswith("Constr("):
            decl = next(it)
            # Constr(stuff), the literal ' throws us off
            str_gc = decl.hdr.kind[7:-1].replace('\'', '!@#')
            sexp_gc = sexpdata.loads(str_gc)
            constrs += [sexp_gc]
        return constrs

    def rec_parse_rawtac(self):
        self.depth += 1
        body, constrs = self.parse_rawtacs()
        self.depth -= 1
        return body, constrs

    def parse_nested(self, tackind):
        # Internal
        it = self.it
        self._mylog("@parse_nested:before<{},{}>".format(it.peek(), tackind))

        rawtacs = []
        start_decl = it.peek()
        while it.has_next() and it.peek().hdr.callid == start_decl.hdr.callid:
            bf_decl = next(it)
            constrs1 = self.parse_constr()
            body, constrs2 = self.rec_parse_rawtac()
            af_decls = []
            while (it.has_next() and
                   is_after(it.peek().hdr.mode) and
                   it.peek().hdr.callid == start_decl.hdr.callid):
                af_decls += [next(it)]
            rawtacs += [RawTac(self._fresh_uid(), start_decl.hdr.tac,
                               tackind, start_decl.hdr.ftac, bf_decl,
                               af_decls, body, constrs1 + constrs2)]
        return rawtacs

    def parse_rawtacs(self):
        """
        Top-level parsing function.
        """
        # Internal
        it = self.it
        if not it.has_next():
            return [], []
        self._mylog("@parse_rawtac:before<{}>".format(it.peek()))

        # Reconstruct tactic tree
        acc = []
        constrs = []
        while it.has_next():
            decl = it.peek()

            if decl.hdr.mode == TOK_BEFORE and decl.hdr.kind == TOK_NAME:
                acc += self.parse_nested(TacKind.NAME)
            elif is_after(decl.hdr.mode) and decl.hdr.kind == TOK_NAME:
                return acc, constrs

            elif decl.hdr.mode == TOK_BEFORE and decl.hdr.kind == TOK_NOTATION:
                acc += self.parse_nested(TacKind.NOTATION)
            elif is_after(decl.hdr.mode) and decl.hdr.kind == TOK_NOTATION:
                return acc, constrs

            elif decl.hdr.mode == TOK_BEFORE and decl.hdr.kind == TOK_ATOMIC:
                acc += self.parse_nested(TacKind.ATOMIC)
            elif is_after(decl.hdr.mode) and decl.hdr.kind == TOK_ATOMIC:
                return acc, constrs

            elif decl.hdr.mode == TOK_BEFORE and decl.hdr.kind == TOK_ML:
                acc += self.parse_nested(TacKind.ML)
            elif is_after(decl.hdr.mode) and decl.hdr.kind == TOK_ML:
                return acc, constrs

            elif decl.hdr.mode == TOK_AFTER and decl.hdr.kind.startswith("Constr"):
                constrs += self.parse_constr()

            else:
                self._log_acc(acc)
                raise NameError("Parsing alignment error {}".format(decl))
        return acc, constrs
