from enum import Enum

from lib.myfile import MyFile
from lib.myutil import pp_tab
from coq.decode import *

"""
[Note]

Goal: String -> [TacStDecl]
Convert raw *.dump file into a list of TacStDecl "tokens".
"""


# -------------------------------------------------
# Tokens

TOK_SEP = "{!}"
TOK_DIV = "============================"
TOK_BEFORE = "bf"
TOK_AFTER = "af"
TOK_AFTER_ERR = "dead"
TOK_BEG_TAC_ST = "bg(ts)"
TOK_END_TAC_ST = "en(ts)"
TOK_BEG_SUB_PF = "bg(spf)"
TOK_END_SUB_PF = "en(spf)"
TOK_BEG_PF = "bg(pf)"
TOK_END_PF = "en(pf)"
TOK_TYPS = "Typs"
TOK_BODS = "Bods"
TOK_CONSTRS = "Constrs"
TOK_PRTYPS = "PrTyps"
TOK_PRBODS = "PrBods"
TOK_PRGLS = "PrGls"

TOK_ATOM = "Atom"
TOK_ML = "ML"
TOK_NAME = "Name"
TOK_NOTE = "Not"


def is_after(mode):
    return mode.startswith(TOK_AFTER) or mode.startswith(TOK_AFTER_ERR)


# -------------------------------------------------
# Data structures

GID_SOLVED = -1
GID_FAILED = -2


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
    def __init__(self, uid, mode, tac, kind, ftac, gid, ngs, loc):
        self.uid = uid           # declaration identifier (almost unique)
        self.mode = mode         # before/after/error
        self.tac = tac           # tactic
        self.kind = kind         # tactic kind
        self.ftac = ftac         # full-tactic
        self.gid = gid           # goal identifier
        self.ngs = ngs           # number of goals
        self.loc = loc           # location in file

    def pp(self, tab=0):
        info = (self.mode, self.uid, self.gid, self.ngs,
                self.tac, self.kind, self.loc, self.ftac)
        s = "{}(id={}, gid={}, ngs={}, tac={}, kind={}, loc={}, ftac={})".format(*info)
        return pp_tab(tab, s)

    def __str__(self):
        info = (self.uid, self.mode, self.tac, self.kind,
                self.ftac, self.gid, self.ngs, self.loc)
        return "(uid: {}, mode: {}, tac: {}, kind: {},\
                ftac: {}, gid: {}, ngs: {}, loc: {})".format(*info)


class TacStDecl(object):
    def __init__(self, hdr, ctx_idents, concl_idx):
        assert isinstance(hdr, TacStHdr)
        assert isinstance(ctx_idents, list)
        assert isinstance(concl_idx, int)

        # Data
        self.hdr = hdr                # tactic state header
        self.ctx_idents = ctx_idents  # ctx as [id]
        self.concl_idx = concl_idx    # conc as int

        # Pretty-printing
        self.prtyps_table = {}        # Dict[ident, str]
        self.prbods_table = {}        # Dict[ident, str]
        self.prgls_table = {}         # Dict[idx, str]

    def pp(self, tab=0):
        s1 = self.hdr.pp(tab) + "\n"
        s2 = "\n".join([pp_tab(tab + 2, "{}: {}".format(x, self.prtyps_table[x])) for x in self.ctx_idents]) + "\n"
        s3 = pp_tab(tab + 2, "=====================\n")
        if self.concl_idx == -1:
            s4 = pp_tab(tab + 2, "SOLVED")
        else:
            s4 = pp_tab(tab + 2, self.prgls_table[self.concl_idx])
        return s1 + s2 + s3 + s4

    def __str__(self):
        if self.hdr.mode == TOK_BEFORE:
            s_mode = "B"
        elif self.hdr.mode == TOK_AFTER:
            s_mode = "A"
        elif self.hdr.mode == TOK_AFTER_ERR:
            s_mode = "E"
        info = s_mode, self.hdr.uid, self.hdr.gid, self.hdr.tac, self.hdr.loc
        return "{}(uid={}, gid={}, tac={}, loc={})".format(*info)


class LemTacSt(object):
    """
    Contains the lemma and the sequence of tactic states associated with it.
    """
    def __init__(self, name, decls, typs_table, bods_table, constrs_table):
        assert isinstance(name, str)
        for decl in decls:
            assert isinstance(decl, TacStDecl)

        self.name = name                     # Name of the lemma
        self.decls = decls                   # List of TacStDecl "tokens"

        # Decode low-level Coq expression
        self.decoder = DecodeCoqExp(typs_table, bods_table, constrs_table)

    def get_tacst_info(self):
        tacst_info = {}
        for decl in self.decls:
            gid = decl.hdr.gid
            if gid not in tacst_info:
                # TODO(deh): can be optimized
                ctx = {}
                for ident in decl.ctx_idents:
                    ctx[ident] = decl.prtyps_table[ident]
                if decl.concl_idx == -1:
                    goal = "SOLVED"
                else:
                    goal = decl.prgls_table[decl.concl_idx]
                tacst_info[gid] = (ctx, goal, decl.ctx_idents, decl.concl_idx)
        return tacst_info

    def pp(self, tab=0):
        s1 = pp_tab(tab, self.name) + "\n"
        s2 = "\n".join([decl.pp(tab + 2) for decl in self.decls]) + "\n"
        # s3 = self.decoder.pp(tab)
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
        self.decls = []           # Accumlated decls in lemma

        # Lemma-sepcific decoding low-level Coq expressions
        self.typs_table = {}      # Dict[str, int], typ ident to exp idx
        self.bods_table = {}      # Dict[str, int], exp ident to exp idx
        self.constrs_table = {}   # Dict[int, string], exp idx to unparsed string

        # Pretty print information
        self.prtyps_table = {}    # Dict[str, str], typ ident to pretty
        self.prbods_table = {}    # Dict[str, str], exp ident to pretty
        self.prgls_table = {}     # Dict[int, str], gidx to pretty

        # Accumulated lemmas
        self.lems = []

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            print(msg)

    def _reset(self):
        self.decls = []
        self.typs_table = {}
        self.bods_table = {}
        self.constrs_table = {}
        self.prtyps_table = {}
        self.prbods_table = {}
        self.prgls_table = {}

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
        # TODO(deh): Fix coq dump to print put in correct order?
        idents.reverse()
        return idents, cid

    def parse_decl(self, d_id, mode, tac, kind, loc):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_decl:before<{}>".format(h_head.peek_line()))

        # Parse declaration
        if h_head.peek_line().startswith("ngs=0"):
            # Parse rest of header
            h_head.consume_line()  # ngs=0
            h_head.consume_line()  # en(ts)

            # Unpack
            hdr = TacStHdr(d_id, mode, tac, kind, "", GID_SOLVED, 0, loc)
            ctx_idents = []
            concl_idx = -1
        elif TOK_SEP in h_head.peek_line():
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
            hdr = TacStHdr(d_id, mode, tac, kind, ftac, gid, ngs, loc)
            ctx_idents, concl_idx = self.parse_decl_body()
        else:
            raise NameError("Parsing error @line{}: {}".format(
                            h_head.line, h_head.peek_line()))
        return TacStDecl(hdr, ctx_idents, concl_idx)

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
        d_id = int(toks[1].strip())
        mode = toks[2].strip()
        tac = toks[3].strip()
        kind = toks[4].strip()
        loc = toks[5].strip()

        return (d_id, mode, tac, kind, loc)

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

    def parse_typs_table(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_typs_table:before<{}>".format(h_head.peek_line()))

        # Parse identifier to expression identifier
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_BODS):
            k, v = self._parse_table_entry()
            self.typs_table[k] = int(v)

    def parse_bods_table(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_bods_table:before<{}>".format(h_head.peek_line()))

        # Parse identifier to expression identifier
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_CONSTRS):
            k, v = self._parse_table_entry()
            self.bods_table[k] = int(v)

    def parse_constrs_table(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_constrs_table:before<{}>".format(
                    h_head.peek_line()))

        # Parse expression identifier to low-level constr expression
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_PRTYPS):
            k, v = self._parse_table_entry()
            self.constrs_table[int(k)] = v

    def parse_prtyps_table(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_prtyps_table:before<{}>".format(
                    h_head.peek_line()))

        # Parse identifier to pretty-print expression
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_PRBODS):
            k, v = self._parse_table_entry()
            self.prtyps_table[k] = v

    def parse_prbods_table(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_prbods_table:before<{}>".format(
                    h_head.peek_line()))

        # Parse identifier to pretty-print expression
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_PRGLS):
            k, v = self._parse_table_entry()
            self.prbods_table[k] = v

    def parse_prgls_table(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_prgls_table:before<{}>".format(h_head.peek_line()))

        # Parse index to pretty-print expression
        h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_END_PF):
            k, v = self._parse_table_entry()
            self.prgls_table[int(k)] = v

    def parse_epilogue(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_epilogue:before<{}>".format(h_head.peek_line()))

        self.parse_typs_table()
        self.parse_bods_table()
        self.parse_constrs_table()
        self.parse_prtyps_table()
        self.parse_prbods_table()
        self.parse_prgls_table()

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
                for decl in self.decls:
                    decl.prtyps_table = self.prtyps_table
                    decl.prbods_table = self.prbods_table
                    decl.prgls_table = self.prgls_table
                lem_name = lemname_stk.pop()
                lemma = LemTacSt(lem_name, self.decls, self.typs_table,
                                 self.bods_table, self.constrs_table)
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
                did, mode, tac, kind, loc = self.parse_begtacst()
                decl = self.parse_decl(did, mode, tac, kind, loc)
                self.decls += [decl]
            elif line.startswith(TOK_END_TAC_ST):
                self.parse_endtacst()
            elif line.startswith(TOK_TYPS):
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
