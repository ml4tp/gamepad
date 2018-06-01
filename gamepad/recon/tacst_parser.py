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

from lib.myfile import MyFile
from lib.myutil import pp_tab
from coq.constr_decode import *
from recon.tokens import *
from coq.glob_constr_parser import GlobConstrDecoder
from coq.tactics_util import FvsTactic


"""
[Note]

Goal: String -> [TacStDecl]
Convert raw *.dump file into a list of TacStDecl "tokens".

Format ::= 'bg(pf)' [TacStDecl] Epilogue 'en(pf)'
TacStDecl ::= 'bg(ts)' Body 'en(ts)'
Epilogue ::= 
  Table<ConstrShare>
  Table<PrCtxTyps>
  Table<PrCtxBods>
  Table<PrGls>
"""


# -------------------------------------------------
# Data structures

class DeclMode(Enum):
    BEFORE = 0
    AFTER = 1
    DEADEND = 2

    def __str__(self):
        if self is DeclMode.BEFORE:
            return "B"
        elif self is DeclMode.AFTER:
            return "A"
        else:
            return "E"


class FullTac(object):
    def __init__(self, pp_tac, sexp_tac=None, lids=set(), gids=set(), tac_args=None):
        assert isinstance(pp_tac, str)
        assert isinstance(lids, set)
        assert isinstance(gids, set)

        self.pp_tac = pp_tac      # Pretty-print tactic
        self.sexp_tac = sexp_tac  # Tactic as sexpression
        self.lids = lids          # Local identifiers mentioned by tactic
        self.gids = gids          # Global identifiers mentioned by tactic
        if tac_args:
            self.tac_args = tac_args  # Args
        else:
            self.tac_args = []        # Args

    def __str__(self):
        return "({} | lids={}, gids={})".format(self.pp_tac, self.lids, self.gids)


class TacStHdr(object):
    """
    Contains the header for a tactic state declaration.
    """
    def __init__(self, callid, mode, tac, kind, ftac, gid, ngs, loc):
        assert isinstance(ftac, FullTac)
        self.callid = callid         # tactic call identifier (almost unique)
        toks = mode.split()
        self.mode = toks[0].strip()  # before/after/error
        if len(toks) == 1:
            self.afgid = None
        else:
            self.afgid = int(toks[1].strip())
        self.tac = tac               # tactic
        self.kind = kind             # tactic kind
        self.ftac = ftac             # full-tactic
        self.gid = gid               # goal identifier
        self.ngs = ngs               # number of goals
        self.loc = loc               # location in file

    def pp(self, tab=0):
        info = (self.mode, self.callid, self.gid, self.ngs,
                self.tac, self.kind, self.loc, self.ftac)
        s = "{}(id={}, gid={}, ngs={}, tac={}, kind={}, loc={}, ftac={})".format(*info)
        return pp_tab(tab, s)

    def __str__(self):
        info = (self.callid, self.mode, self.tac, self.kind,
                self.ftac, self.gid, self.ngs, self.loc)
        return "(callid: {}, mode: {}, tac: {}, kind: {},\
                ftac: {}, gid: {}, ngs: {}, loc: {})".format(*info)


class TacStCtx(object):
    def __init__(self, ctx):
        # List of idenfitier, type kernel index, and type middle index
        self.ctx = ctx   # [(ident, int, int)]

    def traverse(self):
        return [(ldecl[0], ldecl[1], ldecl[2]) for ldecl in self.ctx]

    def idents(self):
        return [ldecl[0] for ldecl in self.ctx]

    def typ_idxs(self):
        return [ldecl[1] for ldecl in self.ctx]


class TacStDecl(object):
    def __init__(self, hdr, ctx, concl_kdx, concl_mdx):
        assert isinstance(hdr, TacStHdr)
        assert isinstance(ctx, TacStCtx)
        assert isinstance(concl_kdx, int)
        assert isinstance(concl_mdx, int)

        # Data
        self.hdr = hdr               # tactic state header
        self.ctx = ctx               # ctx as [(id, typ kern idx, typ mid idx)]
        self.concl_kdx = concl_kdx   # conclusion kernel expression as index
        self.concl_mdx = concl_mdx   # conclusion middle expression as index

    def pp(self, ctx_prtyps, ctx_prgls, tab=0):
        s1 = self.hdr.pp(tab) + "\n"
        s2 = "\n".join([pp_tab(tab + 2, "{}: {}".format(ident, ctx_prtyps[ident]))
                        for ident in self.ctx.idents()]) + "\n"
        s3 = pp_tab(tab + 2, "=====================\n")
        if self.concl_kdx == -1:
            s4 = pp_tab(tab + 2, "SOLVED")
        else:
            s4 = pp_tab(tab + 2, ctx_prgls[self.concl_kdx])
        return s1 + s2 + s3 + s4

    def __str__(self):
        if self.hdr.mode == TOK_BEFORE:
            s_mode = "B"
        elif self.hdr.mode == TOK_AFTER:
            s_mode = "A"
        elif self.hdr.mode == TOK_DEAD:
            s_mode = "E"
        else:
            raise NameError("Mode {} not expected".format(self.hdr.mode))
        info = s_mode, self.hdr.callid, self.hdr.gid, self.hdr.tac, self.hdr.ftac, self.hdr.loc
        return "{}(callid={}, gid={}, tac={}, ftac={}, loc={})".format(*info)


class LemTacSt(object):
    """
    Contains the lemma and the sequence of tactic states associated with it.
    """
    def __init__(self, name, decls, ctx_prtyps, ctx_prbods, ctx_prgls, constr_share, mid_share):
        assert isinstance(name, str)
        for decl in decls:
            assert isinstance(decl, TacStDecl)

        self.name = name               # Name of the lemma
        self.decls = decls             # List of TacStDecl "tokens"

        # Decode low-level Coq expression
        self.decoder = DecodeConstr(constr_share)
        self.mid_decoder = GlobConstrDecoder(mid_share)
        self.ctx_prtyps = ctx_prtyps   # Dict[int, pp_str]
        self.ctx_prbods = ctx_prbods   # Dict[int, pp_str]
        self.ctx_prgls = ctx_prgls     # Dict[int, pp_str]

    def get_tacst_info(self):
        tacst_info = {}
        for decl in self.decls:
            gid = decl.hdr.gid
            if gid not in tacst_info:
                # TODO(deh): can be optimized
                pp_ctx = {}
                for ident, typ_idx, _ in decl.ctx.traverse():
                    pp_ctx[ident] = self.ctx_prtyps[typ_idx]
                if decl.concl_kdx == -1:
                    pp_concl = "SOLVED"
                elif decl.concl_kdx in self.ctx_prgls:
                    pp_concl = self.ctx_prgls[decl.concl_kdx]
                elif decl.concl_kdx in self.ctx_prtyps:
                    # NOTE(deh): due to an optimization in dumping,
                    # the conclusion may be stored in the context if it is seen in the
                    # context before it seen in the conclusion position.
                    pp_concl = self.ctx_prtyps[decl.concl_kdx]
                else:
                    raise NameError("Shouldn't happen")
                tacst_info[gid] = (pp_ctx, pp_concl, decl.ctx.traverse(), (decl.concl_kdx, decl.concl_mdx))
        return tacst_info

    def pp(self, tab=0):
        s1 = pp_tab(tab, self.name) + "\n"
        s2 = "\n".join([decl.pp(self.ctx_prtyps, self.ctx_prgls, tab + 2)
                       for decl in self.decls]) + "\n"
        return s1 + s2

    def __str__(self):
        msg = "\n".join([str(decl) for decl in self.decls])
        return "{}<{}>".format(self.name, msg)


# -------------------------------------------------
# Lexing/Parsing

class TacStParser(object):
    def __init__(self, filename, f_log=False):
        # Internal state
        self.filename = filename
        self.h_head = MyFile(filename)
        self.f_log = f_log
        self.exhausted = False

        # Lemma-specific state
        self.decls = []          # Accumlated decls in lemma

        # Lemma-specific decoding low-level Coq expressions
        self.constr_share = {}   # Dict[int, string], exp idx to unparsed string
        self.mid_share = {}      # Dict[int, sexpr], exp idx to sexpr
        self.ctx_prtyps = {}     # Dict[int, str], typ ident to pretty
        self.ctx_prbods = {}     # Dict[int, str], exp ident to pretty
        self.ctx_prgls = {}      # Dict[int, str], gidx to pretty

        # Accumulated lemmas
        self.lems = []

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            print(msg)

    def _reset(self):
        self.decls = []
        self.constr_share = {}
        self.mid_share = {}
        self.ctx_prtyps = {}
        self.ctx_prbods = {}
        self.ctx_prgls = {}

    def parse_decl_body(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_decl_body:before<{}>".format(h_head.peek_line()))

        line = h_head.consume_line()
        toks = line.split(TOK_SEP)
        s_ctx = toks[0].strip()
        concl = toks[1].strip().split()
        kern_idx = int(concl[0].strip())
        mid_idx = int(concl[1].strip())

        if s_ctx == "":
            ctx = []
        else:
            ctx = []
            for ldecl in s_ctx.split(","):
                toks_p = ldecl.strip().split()
                ident = toks_p[0].strip()
                typ_kern_idx = int(toks_p[1].strip())
                typ_mid_idx = int(toks_p[2].strip())
                ctx += [(ident, typ_kern_idx, typ_mid_idx)]
        ctx.reverse()
        return TacStCtx(ctx), kern_idx, mid_idx

    def parse_decl(self, callid, mode, tac, kind, loc):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_decl:before<{}>".format(h_head.peek_line()))

        # Parse declaration
        if h_head.peek_line().startswith("ngs=0"):
            # Parse *solved* goal state
            # Parse rest of header
            h_head.consume_line()  # ngs=0
            h_head.consume_line()  # en(ts)

            # Unpack
            hdr = TacStHdr(callid, mode, tac, kind, FullTac(""), GID_SOLVED, 0, loc)
            ctx = TacStCtx([])
            kern_idx = -1
            mid_idx = -1
        elif TOK_SEP in h_head.peek_line():
            # Parse *live* or *dead* goal state
            # Parse rest of header
            hdr = h_head.consume_line()
            toks = hdr.split(TOK_SEP)
            while len(toks) < 3:
                line = h_head.consume_line()
                hdr += line
                toks = hdr.split(TOK_SEP)
            ngs = int(toks[0].strip())
            pp_tac = toks[1].strip()
            ast_ftac = toks[2].strip()
            if ast_ftac:
                # Literal ' in identifier messes up sexpression parsing. Sigh*
                ast_ftac = ast_ftac.replace('\'', '!@#')
                try:
                    sexp_ftac = sexpdata.loads(ast_ftac, true="true", false="false")
                    fvs = FvsTactic()
                    tac_lids = fvs.fvs_tac(sexp_ftac)
                    tac_gids = fvs.globs
                    ftac = FullTac(pp_tac, sexp_ftac, tac_lids, tac_gids)
                except:
                    print(ast_ftac)
                    raise NameError("Sexpr parsing failed in {}".format(self.filename))
            else:
                ftac = FullTac(pp_tac)
            gid = int(toks[3].strip())

            # Unpack (note that we handle error and success here)
            hdr = TacStHdr(callid, mode, tac, kind, ftac, gid, ngs, loc)
            ctx, kern_idx, mid_idx = self.parse_decl_body()
        else:
            raise NameError("Parsing error @line{}: {}".format(h_head.line, h_head.peek_line()))
        return TacStDecl(hdr, ctx, kern_idx, mid_idx)

    def parse_begin_pf(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_begin_pf:before<{}>".format(h_head.peek_line()))

        # Parse
        line = h_head.consume_line()
        toks = line.split(TOK_SEP)
        lem_name = toks[2].strip()

        self._mylog("progress: {:4.2f}% @ {}".format(
                    h_head.progress(), lem_name), True)
        return lem_name

    def parse_skip(self, kind):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_{}:before<{}>".format(kind, h_head.peek_line()))

        # Parse
        return h_head.consume_line()

    def parse_qed(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_qed:before<{}>".format(h_head.peek_line()))

        # Parse
        return h_head.consume_line()

    def parse_begtacst(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_begtacst:before<{}>".format(h_head.peek_line()))

        # Parse header
        hdr = h_head.consume_line()
        toks = hdr.split(TOK_SEP)
        while len(toks) < 6:
            line = h_head.consume_line()
            hdr += line
            toks = hdr.split(TOK_SEP)

        # Unpack header
        callid = int(toks[1].strip())
        mode = toks[2].strip()
        tac = toks[3].strip()
        kind = toks[4].strip()
        loc = toks[5].strip()

        return callid, mode, tac, kind, loc

    def parse_endtacst(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_endtacst:before<{}>".format(h_head.peek_line()))

        # Parse
        return h_head.consume_line()

    def _parse_table_entry(self):
        hdr = self.h_head.consume_line()
        end = hdr.find(":")
        key = hdr[:end].strip()
        val = hdr[end + 1:].strip()
        return key, val

    def parse_constr_share(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_constr_share:before<{}>".format(
                    h_head.peek_line()))

        # Parse expression identifier to low-level constr expression
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_PRTYPS):
            k, v = self._parse_table_entry()
            self.constr_share[int(k)] = v

    def parse_ctx_prtyps(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_ctx_prtyps:before<{}>".format(
                    h_head.peek_line()))

        # Parse identifier to pretty-print expression
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_PRBODS):
            k, v = self._parse_table_entry()
            self.ctx_prtyps[int(k)] = v

    def parse_ctx_prbods(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_ctx_prbods:before<{}>".format(
                    h_head.peek_line()))

        # Parse identifier to pretty-print expression
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_PRGLS):
            k, v = self._parse_table_entry()
            self.ctx_prbods[int(k)] = v

    def parse_ctx_prgls(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_ctx_prgls:before<{}>".format(h_head.peek_line()))

        # Parse index to pretty-print expression
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_END_PF):
            k, v = self._parse_table_entry()
            self.ctx_prgls[int(k)] = v

    def parse_epilogue(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_epilogue:before<{}>".format(h_head.peek_line()))

        self.parse_constr_share()
        self.parse_ctx_prtyps()
        self.parse_ctx_prbods()
        self.parse_ctx_prgls()

    def seek_lemma(self, lemma):
        # Internal
        h_head = self.h_head
        self._mylog("seek_lemma<{}>".format(h_head.peek_line()))

        line = h_head.raw_peek_line()
        while line != "":
            line = line.rstrip()
            if line.startswith(TOK_BEG_PF):
                toks = line.split(TOK_SEP)
                lemma_p = toks[2].strip()
                self._mylog("progress: {:4.2f}% @ {}".format(
                            h_head.progress(), lemma_p), True)
                if lemma_p == lemma:
                    return
            h_head.raw_consume_line()
            line = h_head.raw_peek_line()
        raise NameError("Lemma {} not found".format(lemma))

    def ignore_constr_inc(self):
        # Internal
        h_head = self.h_head
        self._mylog("ignore_constr_inc<{}>".format(h_head.peek_line()))

        h_head.consume_line()
        while not h_head.peek_line().startswith("Constrs"):
            k, s_gc = self._parse_table_entry()
            s_gc = s_gc.replace('\'', '!@#')
            sexp_gc = sexpdata.loads(s_gc, true="true", false="false")
            self.mid_share[int(k)] = sexp_gc

        # Ignore incremental constr table for whole dump files
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_END_INC):
            h_head.consume_line()
        h_head.consume_line()

    def parse_lemma(self):
        """
        Parse tactic states for an entire lemma.
        """
        # Internal
        h_head = self.h_head
        self._mylog("parse_lemma<{}>".format(h_head.peek_line()))

        if self.exhausted:
            raise NameError("Already parsed file {}".format(self.filename))

        # Parse
        line = h_head.raw_peek_line()
        lemname_stk = []
        while line != "":
            line = line.rstrip()
            if line.startswith(TOK_BEG_PF):
                lem_name = self.parse_begin_pf()
                lemname_stk.append(lem_name)
            elif line.startswith(TOK_END_PF):
                self.parse_qed()
                # Accumulate lemma
                lem_name = lemname_stk.pop()
                lemma = LemTacSt(lem_name, self.decls, self.ctx_prtyps,
                                 self.ctx_prbods, self.ctx_prgls,
                                 self.constr_share, self.mid_share)
                self.lems.append(lemma)
                if h_head.raw_peek_line() == "":
                    self.exhausted = True

                # Reset for new lemma
                self._reset()

                return lemma
            elif line.startswith(TOK_BEG_SUB_PF):
                # Not keeping track of this
                self.parse_skip("begsubpf")
            elif line.startswith(TOK_END_SUB_PF):
                # Not keeping track of this
                self.parse_skip("endsubpf")
            elif line.startswith(TOK_BULLET):
                # Not keeping track of this
                self.parse_skip("bullet")
            elif line.startswith(TOK_PFSTEP):
                # Not keeping track of this
                self.parse_skip("pfstep")
            elif line.startswith(TOK_BEG_TAC_ST):
                callid, mode, tac, kind, loc = self.parse_begtacst()
                decl = self.parse_decl(callid, mode, tac, kind, loc)
                self.decls += [decl]
            elif line.startswith(TOK_END_TAC_ST):
                self.parse_endtacst()
            elif line.startswith(TOK_BEG_INC):
                self.ignore_constr_inc()
            elif line.startswith(TOK_CONSTRS):
                self.parse_epilogue()
            else:
                raise NameError("Parsing error at line {}: {}".format(
                                h_head.line, h_head.peek_line()))
            line = h_head.raw_peek_line()

    def parse_file(self):
        """
        Top-level parse function.
        """
        # Internal
        h_head = self.h_head
        self._mylog("parse<{}>".format(h_head.peek_line()))

        if self.exhausted:
            raise NameError("Already parsed file {}".format(self.filename))

        # Parse
        line = h_head.raw_peek_line()
        while line != "":
            self.parse_lemma()
            line = h_head.raw_peek_line()
        self.exhausted = True
        return self.lems

    # ------------------------------------
    # Interactive parsing

    def parse_constr_inc(self):
        # Internal
        h_head = self.h_head
        self._mylog("ignore_constr_inc<{}>".format(h_head.peek_line()))

        h_head.consume_line()
        while not h_head.peek_line().startswith("Constrs"):
            k, s_gc = self._parse_table_entry()
            s_gc = s_gc.replace('\'', '!@#')
            sexp_gc = sexpdata.loads(s_gc, true="true", false="false")
            self.mid_share[int(k)] = sexp_gc

        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_END_INC):
            k, v = self._parse_table_entry()
            self.constr_share[int(k)] = v
        h_head.consume_line()

    def parse_partial_lemma(self):
        """
        Parse partial tactic states for an entire lemma.
        """
        # Internal
        h_head = self.h_head
        self._mylog("parse_lemma<{}>".format(h_head.peek_line()))

        if self.exhausted:
            raise NameError("Already parsed file {}".format(self.filename))

        # Parse
        line = h_head.raw_peek_line()
        lemname_stk = []
        while line != "":
            line = line.rstrip()
            if line.startswith(TOK_BEG_PF):
                lem_name = self.parse_begin_pf()
                lemname_stk.append(lem_name)
            elif line.startswith(TOK_END_PF):
                self.parse_qed()
                # Accumulate lemma
                lem_name = lemname_stk.pop()
                lemma = LemTacSt(lem_name, self.decls, self.ctx_prtyps,
                                 self.ctx_prbods, self.ctx_prgls,
                                 self.constr_share, self.mid_share)
                self.lems.append(lemma)
                if h_head.raw_peek_line() == "":
                    self.exhausted = True

                # Reset for new lemma
                self._reset()

                return lemma
            elif line.startswith(TOK_BEG_SUB_PF):
                # Not keeping track of this
                self.parse_skip("begsubpf")
            elif line.startswith(TOK_END_SUB_PF):
                # Not keeping track of this
                self.parse_skip("endsubpf")
            elif line.startswith(TOK_BULLET):
                # Not keeping track of this
                self.parse_skip("bullet")
            elif line.startswith(TOK_PFSTEP):
                # Not keeping track of this
                self.parse_skip("pfstep")
            elif line.startswith(TOK_BEG_TAC_ST):
                callid, mode, tac, kind, loc = self.parse_begtacst()
                decl = self.parse_decl(callid, mode, tac, kind, loc)
                self.decls += [decl]
            elif line.startswith(TOK_END_TAC_ST):
                self.parse_endtacst()
            elif line.startswith(TOK_BEG_INC):
                self.parse_constr_inc()
            elif line.startswith(TOK_CONSTRS):
                self.parse_epilogue()
            else:
                raise NameError("Parsing error at line {}: {}".format(
                                h_head.line, h_head.peek_line()))
            line = h_head.raw_peek_line()
        # Accumulate lemma
        lem_name = lemname_stk.pop()
        return LemTacSt(lem_name, self.decls, self.ctx_prtyps,
                        self.ctx_prbods, self.ctx_prgls,
                        self.constr_share, self.mid_share)
