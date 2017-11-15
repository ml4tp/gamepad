from enum import Enum

from lib.myfile import MyFile
from lib.myutil import pp_tab
from coq_ast import *

"""
[Note]

Goal: String -> [TacStDecl]
Convert raw *.dump file into a list of TacStDecl "tokens".
"""


# -------------------------------------------------
# Tokens

TOK_SEP = "{!}"
TOK_DIV = "============================"
TOK_BEFORE = "before"
TOK_AFTER = "after"
TOK_AFTER_ERR = "afterE"
TOK_BEG_TAC_ST = "begin(tacst)"
TOK_END_TAC_ST = "end(tacst)"
TOK_BEG_SUB_PF = "begin(subpf)"
TOK_END_SUB_PF = "end(subpf)"
TOK_BEG_PF = "begin(pf)"
TOK_END_PF = "end(pf)"
TOK_TYPS = "Typs"
TOK_BODS = "Bods"
TOK_CONSTRS = "Constrs"


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
    """
    Contains information between 'begin(tacst)' and 'end(tacst)'
    """
    def __init__(self, hdr, ctx, goal, ast_ctx, ast_goal):
        assert isinstance(hdr, TacStHdr)
        assert isinstance(ctx, dict)
        assert isinstance(goal, str)
        assert isinstance(ast_ctx, list)
        assert isinstance(ast_goal, int)

        self.hdr = hdr            # tactic state header
        self.ctx = ctx            # context as Dict[id, str]
        self.goal = goal          # goal as string
        self.ast_ctx = ast_ctx    # ctx as [id]
        self.ast_goal = ast_goal  # goal as int

    def pp(self, tab=0):
        s1 = self.hdr.pp(tab) + "\n"
        s2 = "\n".join([pp_tab(tab + 2, "{}: {}".format(x, ty)) for (x, ty) in self.ctx.items()]) + "\n"
        s3 = pp_tab(tab + 2, "=====================\n")
        s4 = pp_tab(tab + 2, self.goal)
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
        self.decoder = CoqExpDecode(typs_table, bods_table, constrs_table)

    def get_tacst_info(self):
        tacst_info = {}
        for decl in self.decls:
            gid = decl.hdr.gid
            if gid not in tacst_info:
                tacst_info[gid] = (decl.ctx, decl.goal, decl.ast_ctx, decl.ast_goal)
        return tacst_info

    def pp(self, tab=0):
        s1 = pp_tab(tab, self.name) + "\n"
        s2 = "\n".join([decl.pp(tab + 2) for decl in self.decls]) + "\n"
        s3 = self.decoder.pp(tab)
        return s1 + s2 + s3

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
        self.typs_table = {}      # Dict[int, int], typ idx to exp idx
        self.bods_table = {}      # Dict[int, int], exp idx to exp idx
        self.constrs_table = {}   # Dict[int, string], exp idx to unparsed string

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

    def parse_sep(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_sep:before<{}>".format(h_head.peek_line()))

        # Parse separator
        line = h_head.consume_line()
        return line

    def parse_newline(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_newline:before<{}>".format(h_head.peek_line()))

        # Parse new line
        line = h_head.consume_line()
        return line

    def parse_local_decl(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_local_decl:before<{}>".format(h_head.peek_line()))

        # Parse local decl
        ldecl = h_head.consume_line()
        idx = ldecl.find(':')
        if idx < 0:
            raise NameError("Parsing local declaration but found {}".
                            format(ldecl))
        _idents = ldecl[:idx].strip()
        typ = ldecl[idx + 1:].strip()

        # The context is compacted so that multiple identifiers
        # may have the same type
        idents = [x.strip() for x in _idents.split(",")]

        # Parse rest of type it is on newline
        line = h_head.peek_line()
        while line != TOK_DIV and line.find(':') < 0:
            typ += " " + line.strip()
            line = h_head.advance_line()
        return (idents, typ)

    def parse_local_ctx(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_local_ctx:before<{}>".format(h_head.peek_line()))

        # Parse local context
        local_ctx = {}
        line = h_head.peek_line()
        while line.find(':') >= 0:
            idents, typ = self.parse_local_decl()
            for ident in idents:
                local_ctx[ident] = typ
            line = h_head.peek_line()
        return local_ctx

    def parse_pf_div(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_pf_div:before<{}>".format(h_head.peek_line()))

        # Parse proof divider
        line = h_head.consume_line()
        if line != TOK_DIV:
            raise NameError("Found {} instead of {}".format(line, TOK_DIV))
        return line

    def parse_goal(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_goal:before<{}>".format(h_head.peek_line()))

        # Parse goal
        goal = h_head.consume_line()
        line = h_head.peek_line()
        while not line.startswith(TOK_SEP):
            goal += line
            line = h_head.advance_line()
        return goal

    def parse_local_ast_ctx(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_local_ast_ctx:before<{}>".format(h_head.peek_line()))

        # Parse local ctx
        line = h_head.consume_line()
        if line == "":
            return []
        else:
            idents = [ident.strip() for ident in line.split(",")]
            return idents

    def parse_ast_goal(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_ast_goal:before<{}>".format(h_head.peek_line()))

        goal = h_head.consume_line()
        return int(goal)

    def parse_decl(self, d_id, mode, tac, kind, loc):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_decl:before<{}>".format(h_head.peek_line()))

        # Parse declaration
        if h_head.peek_line().startswith("ngs=0"):
            # Parse rest of header
            h_head.consume_line()  # ngs=0
            h_head.consume_line()  # end(tacst)

            # Unpack
            hdr = TacStHdr(d_id, mode, tac, kind, "", GID_SOLVED, 0, loc)
            ctx = {}
            goal = "ML4TP_SOLVED"
            ast_ctx = []
            ast_goal = -1
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
            ctx = self.parse_local_ctx()
            self.parse_pf_div()
            goal = self.parse_goal()
            self.parse_sep()
            ast_ctx = self.parse_local_ast_ctx()
            self.parse_pf_div()
            ast_goal = self.parse_ast_goal()
        else:
            raise NameError("Parsing error @line{}: {}".format(h_head.line, h_head.peek_line()))
        return TacStDecl(hdr, ctx, goal, ast_ctx, ast_goal)

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

    def parse_typs_table(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_typs_table:before<{}>".format(h_head.peek_line()))

        # Parse identifier to expression identifier
        _ = h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_BODS):
            hdr = h_head.consume_line()
            end = hdr.find(":")
            ident = hdr[:end].strip()
            edx = int(hdr[end+1:].strip())
            self.typs_table[ident] = edx

    def parse_bods_table(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_bods_table:before<{}>".format(h_head.peek_line()))

        # Parse identifier to expression identifier
        _ = h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_CONSTRS):
            hdr = h_head.consume_line()
            end = hdr.find(":")
            ident = hdr[:end].strip()
            bdx = int(hdr[end+1:].strip())
            self.bods_table[ident] = bdx

    def parse_constrs_table(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_constrs_table:before<{}>".format(h_head.peek_line()))

        # Parse expression identifier to low-level constr expression
        _ = h_head.consume_line()
        while not h_head.peek_line().startswith(TOK_END_PF):
            hdr = h_head.consume_line()
            end = hdr.find(":")
            edx = int(hdr[:end].strip())
            low_constr = hdr[end+1:].strip()
            self.constrs_table[edx] = low_constr

    def parse_epilogue(self):
        # Internal
        h_head = self.h_head
        self._mylog("@parse_epilogue:before<{}>".format(h_head.peek_line()))

        self.parse_typs_table()
        self.parse_bods_table()
        self.parse_constrs_table()

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
        while line != "":
            line = line.rstrip()
            if line.startswith(TOK_BEG_PF):
                # TODO(deh): this does not handle opening a proof
                # within a proof
                lem_name = self.parse_begin_pf()
            elif line.startswith(TOK_END_PF):
                self.parse_qed()
                # Accumulate lemma
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
            elif line.startswith("AfterHOHOHO"):
                # TODO(deh): Kludge, fix coq
                self.h_head.consume_line()
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
