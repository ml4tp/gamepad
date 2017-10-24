from lib.myfile import MyFile

"""
[Note]

Goal: String -> [TacStDecl]

AST:
[TacStDecl] ::= decls
TacStDecl ::= decl

BNF:
decls ::= decl | decl '\n' decls
decl ::= hdr '\n' ctx '============================' '\n' goal

ctx ::= ldecl | ldecl '\n' ctx
ldecl ::= id ':' string '\n'

hdr ::= kind '{!}' tac '{!}' full_tac '{!}' int '{!}' int
kind ::= 'AFTER' | 'BEFORE'
tac ::= string
full_tac ::= string
int ::= [0-9]+
"""


# -------------------------------------------------
# Tokens

TOK_SEP = "{!}"
TOK_DIV = "============================"
TOK_BEFORE = "before"
TOK_AFTER = "after"
TOK_BEG_TAC_ST = "begin(tacst)"
TOK_END_TAC_ST = "end(tacst)"
TOK_BEG_SUB_PF = "begin(subpf)"
TOK_END_SUB_PF = "end(subpf)"
TOK_BEG_PF = "begin(pf)"
TOK_END_PF = "end(pf)"


# -------------------------------------------------
# Data structures

class TacStHdr(object):
    """
    Contains the header for a tactic state declaration.
    """
    def __init__(self, mode, tac, kind, ftac, gid, ngs, loc, depth):
        self.mode = mode
        self.tac = tac
        self.kind = kind
        self.ftac = ftac
        self.gid = gid
        self.ngs = ngs
        self.loc = loc
        self.depth = depth

    def __str__(self):
        return "({} tac: {}  ftac: {}  gid: {}  ngs: {}  depth: {})".format(
               self.mode, self.tac, self.ftac, self.gid, self.ngs, self.depth)


class TacStDecl(object):
    """
    TacStDecl = 'begin(tacst)' ... 'end(tacst)'
    """
    def __init__(self, tac_st_hdr, ctx, goal):
        self.hdr = tac_st_hdr
        self.ctx = ctx
        self.goal = goal

    def dump(self):
        return "{}\n{}\n{}".format(str(self.hdr), str(self.ctx),
                                   str(self.goal))

    def __str__(self):
        if self.hdr.mode == TOK_BEFORE:
            return "B({},{},{})".format(self.hdr.gid, self.hdr.tac, self.hdr.loc)
        else:
            return "A({},{},{})".format(self.hdr.gid, self.hdr.tac, self.hdr.loc)

    def __hash__(self):
        msg = "{}{}".format(self.hdr.loc, self.hdr.gid)
        return int.from_bytes(msg.encode(), "little")


class LemTacSt(object):
    """
    Contains the lemma and the sequence of tactic states associated with it.
    """
    def __init__(self, name, decls):
        self.name = name
        self.decls = decls

    def __str__(self):
        msg = "\n".join([str(decl) for decl in self.decls])
        return "{}<{}>".format(self.name, msg)


# TODO(deh): deprecate?
def mk_root_decl():
    return TacStDecl(TacStHdr(TOK_AFTER, "root", "", "", 0, 0, ""), "", "", 0)


# TODO(deh): deprecate?
def mk_term_decl(gid):
    return TacStDecl(TacStHdr(TOK_AFTER, "term", "", "", gid, 0, ""), "", "", 0)


# -------------------------------------------------
# Parsing

class TacStParser(object):
    def __init__(self, filename, f_log=False):
        self.filename = filename
        self.f_head = MyFile(filename)
        self.f_log = f_log
        self.log = []
        self.lems = []
        self.decls = []
        self.exhausted = False

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            # self.log.append(msg)
            print(msg)

    def parse_hdr(self, depth):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_hdr:before<{}>".format(f_head.peek_line()))

        # Parse header
        hdr = f_head.consume_line()
        toks = hdr.split(TOK_SEP)
        while len(toks) < 4:
            line = f_head.consume_line()
            hdr += line
            toks = hdr.split(TOK_SEP)

        # Unpack initial header
        mode = toks[0].strip()
        tac = toks[1].strip()
        kind = toks[2].strip()
        ngs = int(toks[3].strip())
        loc = toks[4].strip()

        if ngs == 0:
            # Does not have rest of header
            ftac = ""
            gid = -1
        else:
            # Parse and unpack rest of header
            while len(toks) != 7:
                line = f_head.consume_line()
                hdr += line
                toks = hdr.split(TOK_SEP)
            ftac = toks[5].strip()
            gid = int(toks[6].strip())

        tac_st_hdr = TacStHdr(mode, tac, kind, ftac, gid, ngs, loc, depth)
        return tac_st_hdr

    def parse_local_decl(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_local_decl:before<{}>".format(f_head.peek_line()))

        # Parse local decl
        ldecl = f_head.consume_line()
        idx = ldecl.find(':')
        if idx < 0:
            raise NameError("Parsing local declaration but found {}".
                            format(ldecl))
        name = ldecl[:idx].strip()
        typ = ldecl[idx:].strip()

        # Parse rest of type it is on newline
        line = f_head.peek_line()
        while line != TOK_DIV and line.find(':') < 0:
            typ += " " + line.strip()
            line = f_head.advance_line()
        return (name, typ)

    def parse_local_ctx(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_local_ctx:before<{}>".format(f_head.peek_line()))

        # Parse local context
        local_decls = []
        line = f_head.peek_line()
        while line.find(':') >= 0:
            name, typ = self.parse_local_decl()
            local_decls += [(name, typ)]
            line = f_head.peek_line()
        return local_decls

    def parse_newline(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_newline:before<{}>".format(f_head.peek_line()))

        # Parse new line
        line = f_head.consume_line()
        return line

    def parse_pf_div(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_pf_div:before<{}>".format(f_head.peek_line()))

        # Parse proof divider
        line = f_head.consume_line()
        if line != TOK_DIV:
            raise NameError("Found {} instead of {}".format(line, TOK_DIV))
        return line

    def parse_goal(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_goal:before<{}>".format(f_head.peek_line()))

        # Parse goal
        goal = f_head.consume_line()
        line = f_head.peek_line()
        while not line.startswith(TOK_END_TAC_ST):
            goal += line
            line = f_head.advance_line()
        return goal

    def parse_decl(self, depth):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_decl:before<{}>".format(f_head.peek_line()))

        # Parse declaration
        tac_st_hdr = self.parse_hdr(depth)
        ctx = self.parse_local_ctx()
        if f_head.peek_line().startswith(TOK_END_TAC_ST):
            goal = "DEH_SOLVED"
        else:
            self.parse_pf_div()
            goal = self.parse_goal()
        return TacStDecl(tac_st_hdr, ctx, goal)

    def parse_begin_pf(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_begin_pf:before<{}>".format(f_head.peek_line()))

        # Parse
        line = f_head.consume_line()
        toks = line.split(TOK_SEP)
        lem_name = toks[2].strip()

        self._mylog("progress: {:4.2f}% @ {}".format(
                    f_head.progress(), lem_name), True)
        return lem_name

    def parse_begsubpf(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_begsubpf:before<{}>".format(f_head.peek_line()))

        # Parse
        return f_head.consume_line()

    def parse_endsubpf(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_endsubpf:before<{}>".format(f_head.peek_line()))

        # Parse
        return f_head.consume_line()

    def parse_qed(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_qed:before<{}>".format(f_head.peek_line()))

        # Parse
        return f_head.consume_line()

    def parse_begtacst(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_begtacst:before<{}>".format(f_head.peek_line()))

        # Parse
        line = f_head.consume_line()
        toks = line.split(TOK_SEP)
        return int(toks[1])

    def parse_endtacst(self):
        # Internal
        f_head = self.f_head
        self._mylog("@parse_endtacst:before<{}>".format(f_head.peek_line()))

        # Parse
        return f_head.consume_line()

    def parse_lemma(self):
        """
        Parse tactic states for an entire lemma.
        """
        # Internal
        f_head = self.f_head
        self._mylog("parse_lemma<{}>".format(f_head.peek_line()))

        if self.exhausted:
            raise NameError("Already parsed file {}".format(self.filename))

        # Parse
        line = f_head.raw_peek_line()
        while line != "":
            line = line.rstrip()
            if line.startswith(TOK_BEG_PF):
                lem_name = self.parse_begin_pf()
                # TODO(deh): this does not handle opening a proof
                # within a proof
                self.decls = []
            elif line.startswith(TOK_END_PF):
                self.parse_qed()
                # Accumulate lemma
                lemma = LemTacSt(lem_name, self.decls)
                self.lems.append(lemma)
                if f_head.raw_peek_line() == "":
                    self.exhausted = True
                return lemma
            elif line.startswith(TOK_BEG_SUB_PF):
                self.parse_begsubpf()
                # TODO(deh): keep track of this?
            elif line.startswith(TOK_END_SUB_PF):
                self.parse_endsubpf()
                # TODO(deh): keep track of this?
            elif line.startswith(TOK_BEG_TAC_ST):
                depth = self.parse_begtacst()
                decl = self.parse_decl(depth)
                self.decls += [decl]
            elif line.startswith(TOK_END_TAC_ST):
                self.parse_endtacst()
            else:
                raise NameError("Parsing error at line {}: {}".format(
                                f_head.line, f_head.peek_line()))
            line = f_head.raw_peek_line()

    def parse_file(self):
        """
        Top-level parse function.
        """
        # Internal
        f_head = self.f_head
        self._mylog("parse<{}>".format(f_head.peek_line()))

        if self.exhausted:
            raise NameError("Already parsed file {}".format(self.filename))

        # Parse
        line = f_head.raw_peek_line()
        while line != "":
            self.parse_lemma()
            line = f_head.raw_peek_line()
        self.exhausted = True
        return self.lems
