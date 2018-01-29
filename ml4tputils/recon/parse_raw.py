from enum import Enum
import sexpdata

from lib.myfile import MyFile
from lib.myutil import pp_tab
from coq.decode import *
from recon.tokens import *
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
    def __init__(self, callid, mode, tac, kind, ftac, gid, ngs, loc, sexp_ftac=None):
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
        self.sexp_ftac = sexp_ftac   # sexpression of full-tactic

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
        # List of idenfitier, type index, and optional body index
        self.ctx = ctx   # [(ident, int, int option)]

    def traverse(self):
        return [(ldecl[0], ldecl[1]) for ldecl in self.ctx]

    def idents(self):
        return [ldecl[0] for ldecl in self.ctx]

    def typ_idxs(self):
        return [ldecl[1] for ldecl in self.ctx]


class TacStDecl(object):
    def __init__(self, hdr, ctx, concl_idx):
        assert isinstance(hdr, TacStHdr)
        assert isinstance(ctx, TacStCtx)
        assert isinstance(concl_idx, int)

        # Data
        self.hdr = hdr               # tactic state header
        self.ctx = ctx               # ctx as [(id, typ idx, body idx)]
        self.concl_idx = concl_idx   # conclusion expression as index

    def pp(self, ctx_prtyps, ctx_prgls, tab=0):
        s1 = self.hdr.pp(tab) + "\n"
        s2 = "\n".join([pp_tab(tab + 2, "{}: {}".format(x, ctx_prtyps[ident]))
                        for ident in self.ctx.idents()]) + "\n"
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
        info = s_mode, self.hdr.callid, self.hdr.gid, self.hdr.tac, self.hdr.ftac, self.hdr.loc
        return "{}(callid={}, gid={}, tac={}, ftac={}, loc={})".format(*info)


class LemTacSt(object):
    """
    Contains the lemma and the sequence of tactic states associated with it.
    """
    def __init__(self, name, decls, ctx_prtyps, ctx_prbods,
                 ctx_prgls, constr_share):
        assert isinstance(name, str)
        for decl in decls:
            assert isinstance(decl, TacStDecl)

        self.name = name               # Name of the lemma
        self.decls = decls             # List of TacStDecl "tokens"

        # Decode low-level Coq expression
        self.decoder = DecodeCoqExp(constr_share)
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
                for ident, typ_idx in decl.ctx.traverse():
                    pp_ctx[ident] = self.ctx_prtyps[typ_idx]
                if decl.concl_idx == -1:
                    pp_concl = "SOLVED"
                else:
                    pp_concl = self.ctx_prgls[decl.concl_idx]
                tacst_info[gid] = (pp_ctx, pp_concl, decl.ctx.traverse(),
                                   decl.concl_idx)
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
        self.constr_share = {}   # Dict[int, string], exp idx to unparsed string
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
        concl_idx = int(toks[1].strip())

        if s_ctx == "":
            ctx = []
        else:
            ctx = []
            for ldecl in s_ctx.split(","):
                toks_p = ldecl.strip().split()
                ident = toks_p[0].strip()
                typ_idx = int(toks_p[1].strip())
                if len(toks_p) == 3:
                    body_idx = int(toks_p[2].strip())
                    ctx += [(ident, typ_idx, body_idx)]
                else:
                    ctx += [(ident, typ_idx)]
        # TODO(deh): Fix coq dump to print in reverse order?
        ctx.reverse()
        return TacStCtx(ctx), concl_idx

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
            ctx = TacStCtx([])
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
            # gid = int(toks[2].strip())
            ast_ftac = toks[2].strip()
            if ast_ftac:
                print("PARSING", ftac, "AST", ast_ftac)
                # TODO(deh): need to handle this shit properly
                ast_ftac = ast_ftac.replace('\'', '!@#')
                try:
                    sexp_ftac = sexpdata.loads(ast_ftac, true="true", false="false")
                    print("FVS", FvsTactic().fvs_tac(sexp_ftac))
                except:
                    raise NameError("WTF " + self.filename)
            else:
                sexp_ftac = None
            # TODO(deh): get rid of grefs?
            # TODO(deh): get rid of lrefs?
            gid = int(toks[5].strip())

            # Unpack (note that we handle error and success here)
            hdr = TacStHdr(callid, mode, tac, kind, ftac, gid, ngs, loc, sexp_ftac)
            # ctx, concl_idx = self.parse_decl_body()
            self.h_head.consume_line()
            ctx = TacStCtx([])
            concl_idx = -1
        else:
            raise NameError("Parsing error @line{}: {}".format(
                            h_head.line, h_head.peek_line()))
        return TacStDecl(hdr, ctx, concl_idx)

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

        # Ignore for whole dump files
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
                        self.constr_share)
