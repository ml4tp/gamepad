from lib.myiter import MyIter
from parse_raw import *

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


class DumbTac(Tac):
    def __init__(self, uid, name, bf_decls, af_decls, bods, terminal=False):
        assert isinstance(name, str)
        for bf_decl in bf_decls:
            assert isinstance(bf_decl, TacStDecl)
        for af_decl in af_decls:
            assert isinstance(af_decl, TacStDecl)
        for body in bods:
            for tac in body:
                assert isinstance(tac, Tac)

        super().__init__(uid, terminal)
        self.name = name
        self.bf_decls = bf_decls
        self.af_decls = af_decls
        self.bods = bods

    def my_name():
        return self.name

    def has_subtac(self):
        # TODO(deh): is this correct?
        return len(self.bods) > 0

    def in_edges(self):
        return [bf_decl.hdr.gid for bf_decl in self.bf_decls]

    def out_edges(self):
        return [af_decl.hdr.gid for af_decl in self.af_decls]

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

        return DumbTac(self._getuid(), befores[0].hdr.tac, befores, afters, [])

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

        return DumbTac(self._getuid(), befores[0].hdr.tac, befores, afters, [])

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

        return DumbTac(self._getuid(), befores[0].hdr.tac, befores, afters, bods)

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

        return DumbTac(self._getuid(), befores[0].hdr.tac, befores, afters, [body])

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
