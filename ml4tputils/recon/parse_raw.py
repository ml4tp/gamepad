from enum import Enum

from lib.myfile import MyFile
from lib.myutil import pp_tab
from coq.decode import *
from recon.tokens import *

"""
[Note]

Goal: String -> [TacStDecl]
Convert raw *.dump file into a list of TacStDecl "tokens".

Format ::= 'bg(pf)' [TacStDecl] Epilogue 'en(pf)'
TacStDecl ::= 'bg(ts)' Body 'en(ts)'
Epilogue ::= 
  Table<CtxTyps>
  Table<CtxBods>
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
        if isinstance(self, DeclMode.BEFORE):
            return "B"
        elif isinstance(self, DeclMode.AFTER):
            return "A"
        else:
            return "E"


class TacStHdr(object):
    """
    Contains the header for a tactic state declaration.
    """
    def __init__(self, callid, mode, tac, kind, ftac, gid, ngs, loc):
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


class TacStDecl(object):
    def __init__(self, hdr, ldecls, concl_idx):
        assert isinstance(hdr, TacStHdr)
        assert isinstance(ldecls, list)
        assert isinstance(concl_idx, int)

        # Data
        self.hdr = hdr                # tactic state header
        self.ldecls = ldecls          # ctx as [(id, typ idx, body idx)]
        self.concl_idx = concl_idx    # conclusion expression as index

    def pp(self, ctx_prtyps, ctx_prgls, tab=0):
        s1 = self.hdr.pp(tab) + "\n"
        s2 = "\n".join([pp_tab(tab + 2, "{}: {}".format(x, ctx_prtyps[x[0]])) for x in self.ldecls]) + "\n"
        s3 = pp_tab(tab + 2, "=====================\n")
        if self.concl_idx == -1:
            s4 = pp_tab(tab + 2, "SOLVED")
        else:
            s4 = pp_tab(tab + 2, ctx_prgls[self.concl_idx])
        return s1 + s2 + s3 + s4

    def __str__(self):
        if self.hdr.mode == TOK_BEFORE:
            s_mode = "B"
        elif self.hdr.mode == TOK_AFTER:
            s_mode = "A"
        elif self.hdr.mode == TOK_DEAD:
            s_mode = "E"
        info = s_mode, self.hdr.callid, self.hdr.gid, self.hdr.tac, self.hdr.loc
        return "{}(callid={}, gid={}, tac={}, loc={})".format(*info)


class LemTacSt(object):
    """
    Contains the lemma and the sequence of tactic states associated with it.
    """
    def __init__(self, name, decls, ctx_typs, ctx_bods, ctx_prtyps,
                 ctx_prbods, ctx_prgls, constr_share):
        assert isinstance(name, str)
        for decl in decls:
            assert isinstance(decl, TacStDecl)

        self.name = name               # Name of the lemma
        self.decls = decls             # List of TacStDecl "tokens"

        # Decode low-level Coq expression
        self.decoder = DecodeCoqExp(ctx_typs, ctx_bods, constr_share)
        self.ctx_prtyps = ctx_prtyps   # Pretty-print typs in context
        self.ctx_prbods = ctx_prbods   # Pretty-print bods in context
        self.ctx_prgls = ctx_prgls     # Pretty-print goals in context

    def get_tacst_info(self):
        tacst_info = {}
        for decl in self.decls:
            gid = decl.hdr.gid
            if gid not in tacst_info:
                # TODO(deh): can be optimized
                ctx = {}
                for ldecl in decl.ldecls:
                    ident = ldecl[0]
                    typ_idx = ldecl[1]
                    ctx[ident] = self.ctx_prtyps[typ_idx]
                if decl.concl_idx == -1:
                    goal = "SOLVED"
                else:
                    goal = self.ctx_prgls[decl.concl_idx]
                tacst_info[gid] = (ctx, goal, [(x[0], x[1]) for x in decl.ldecls], decl.concl_idx)
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

        # Lemma-sepcific state
        self.decls = []          # Accumlated decls in lemma

        # Lemma-sepcific decoding low-level Coq expressions
        self.ctx_typs = {}       # Dict[str, int], typ ident to exp idx
        self.ctx_bods = {}       # Dict[str, int], exp ident to exp idx
        self.constr_share = {}   # Dict[int, string], exp idx to unparsed string

        # Pretty print information
        self.ctx_prtyps = {}     # Dict[str, str], typ ident to pretty
        self.ctx_prbods = {}     # Dict[str, str], exp ident to pretty
        self.ctx_prgls = {}      # Dict[int, str], gidx to pretty

        # Accumulated lemmas
        self.lems = []

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            print(msg)

    def _reset(self):
        self.decls = []
        self.ctx_typs = {}
        self.ctx_bods = {}
        self.constr_share = {}
        self.ctx_prtyps = {}
        self.ctx_prbods = {}
        self.ctx_prgls = {}

    def parse_decl_body(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_decl_body:before<{}>".format(h_head.peek_line()))

        line = h_head.consume_line()
        toks = line.split(TOK_SEP)
        ctx_idents = toks[0].strip()
        cid = int(toks[1].strip())

        if ctx_idents == "":
            idents = []
        else:
            idents = [ident.strip() for ident in ctx_idents.split(",")]
        # TODO(deh): Fix coq dump to print in reverse order?
        idents.reverse()
        return idents, cid

    def parse_decl_body2(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_decl_body2:before<{}>".format(h_head.peek_line()))

        line = h_head.consume_line()
        toks = line.split(TOK_SEP)
        ctx = toks[0].strip()
        concl_idx = int(toks[1].strip())

        if ctx == "":
            ldecls = []
        else:
            ldecls = []
            for ldecl in ctx.split(","):
                toks_p = ldecl.strip().split()
                ident = toks_p[0].strip()
                typ_idx = int(toks_p[1].strip())
                if len(toks_p) == 3:
                    body_idx = int(toks_p[2].strip())
                    ldecls += [(ident, typ_idx, body_idx)]
                else:
                    ldecls += [(ident, typ_idx)]
        # TODO(deh): Fix coq dump to print in reverse order?
        ldecls.reverse()
        return ldecls, concl_idx

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
            hdr = TacStHdr(callid, mode, tac, kind, "", GID_SOLVED, 0, loc)
            ldecls = []
            concl_idx = -1
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
            ftac = toks[1].strip()
            gid = int(toks[2].strip())

            # Unpack (note that we handle error and success here)
            hdr = TacStHdr(callid, mode, tac, kind, ftac, gid, ngs, loc)
            # ctx_idents, concl_idx = self.parse_decl_body()
            ldecls, concl_idx = self.parse_decl_body2()
        else:
            raise NameError("Parsing error @line{}: {}".format(
                            h_head.line, h_head.peek_line()))
        return TacStDecl(hdr, ldecls, concl_idx)

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

    def parse_begsubpf(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_begsubpf:before<{}>".format(h_head.peek_line()))

        # Parse
        return h_head.consume_line()

    def parse_endsubpf(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_endsubpf:before<{}>".format(h_head.peek_line()))

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

        return (callid, mode, tac, kind, loc)

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

    def parse_ctx_typs(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_ctx_typs:before<{}>".format(h_head.peek_line()))

        # Parse identifier to expression identifier
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_BODS):
            k, v = self._parse_table_entry()
            self.ctx_typs[k] = int(v)

    def parse_ctx_bods(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_ctx_bods:before<{}>".format(h_head.peek_line()))

        # Parse identifier to expression identifier
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_CONSTRS):
            k, v = self._parse_table_entry()
            self.ctx_bods[k] = int(v)

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

        # self.parse_ctx_typs()
        # self.parse_ctx_bods()
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
                lemma = LemTacSt(lem_name, self.decls, self.ctx_typs,
                                 self.ctx_bods, self.ctx_prtyps,
                                 self.ctx_prbods, self.ctx_prgls,
                                 self.constr_share)
                self.lems.append(lemma)
                if h_head.raw_peek_line() == "":
                    self.exhausted = True

                # Reset for new lemma
                self._reset()

                return lemma
            elif line.startswith(TOK_BEG_SUB_PF):
                self.parse_begsubpf()
                # TODO(deh): keep track of this?
            elif line.startswith(TOK_END_SUB_PF):
                self.parse_endsubpf()
                # TODO(deh): keep track of this?
            elif line.startswith(TOK_BEG_TAC_ST):
                callid, mode, tac, kind, loc = self.parse_begtacst()
                decl = self.parse_decl(callid, mode, tac, kind, loc)
                self.decls += [decl]
            elif line.startswith(TOK_END_TAC_ST):
                self.parse_endtacst()
            # elif line.startswith(TOK_TYPS):
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
