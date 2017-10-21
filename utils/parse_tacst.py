from lib.myiter import MyIter
from parse_raw import *

"""
[Note]

Goal: [TacStDecl] -> [Tac]

AST:
Tacs ::= Tac | Tac Tacs
Tac ::= intro(alias, core)
      | reflexivity(alias, core)
      | have(alias, plugin, body)
      | generic(tac)
"""


# -------------------------------------------------
# Data structures

class Tac(object):
    def __init__(self, uid):
        self.uid = uid

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


class IntroTac(Tac):
    def __init__(self, uid, alias, core):
        assert isinstance(alias[0], TacStDecl)
        assert isinstance(alias[1], TacStDecl)
        assert isinstance(core[0], TacStDecl)
        assert isinstance(core[1], TacStDecl)

        super().__init__(uid)
        self.alias = alias
        self.core = core

    def has_subtac(self):
        return False

    def in_edge(self):
        return self.alias[0].hdr.gid

    def out_edges(self):
        return [self.alias[1].hdr.gid]

    def __str__(self):
        es = [str(self.alias[0]), str(self.core[0]),
              str(self.core[1]), str(self.alias[1])]
        return "Intro({}; {})".format(self.uid, ", ".join(es))


class ReflTac(Tac):
    def __init__(self, uid, alias, core):
        assert isinstance(alias[0], TacStDecl)
        assert isinstance(alias[1], TacStDecl)
        assert isinstance(core, TacStDecl)

        super().__init__(uid)
        self.alias = alias
        self.core = core

    def has_subtac(self):
        return False

    def in_edge(self):
        return self.alias[0].hdr.gid

    def out_edges(self):
        return [self.alias[1].hdr.gid]

    def __str__(self):
        es = [str(self.alias[0]), str(self.alias[1]), str(self.core)]
        return "Refl({}; {})".format(self.uid, ", ".join(es))


class SsrhaveTac(Tac):
    def __init__(self, uid, alias, core, body):
        assert isinstance(alias[0], TacStDecl)
        assert isinstance(alias[1], TacStDecl)
        assert isinstance(core[0], TacStDecl)
        assert isinstance(core[1], TacStDecl)
        for tac in body:
            assert isinstance(tac, Tac)

        super().__init__(uid)
        self.alias = alias
        self.core = core
        self.body = body

    def has_subtac(self):
        return True

    def in_edge(self):
        return self.alias[0].hdr.gid

    def out_edges(self):
        return [self.core[1].hdr.gid]

    def __str__(self):
        es = [str(self.alias[0]), str(self.core[0]),
              str(self.core[1]), str(self.alias[1])]
        body = [str(tac) for tac in self.body]
        return "Srrhave({}; {}; {})".format(self.uid, ", ".join(es),
                                            ", ".join(body))


class GenericTac(Tac):
    def __init__(self, uid, before, afters):
        assert isinstance(before, TacStDecl)
        for after in afters:
            assert isinstance(after, TacStDecl)

        super().__init__(uid)
        self.before = before
        self.afters = afters

    def has_subtac(self):
        return False

    def in_edge(self):
        return self.before.hdr.gid

    def out_edges(self):
        return [after.hdr.gid for after in self.afters]

    def __str__(self):
        if not self.afters:
            return "Terminal({}; {})".format(self.uid, str(self.before))
        elif len(self.afters) == 1:
            return "Generic({}; {}, {})".format(self.uid, str(self.before),
                                                str(self.afters[0]))
        else:
            ps = ["({}, {})".format(self.before, after)
                  for after in self.afters]
            return "Generic({}; {})".format(self.uid, ", ".join(ps))


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

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            # self.log.append(msg)
            print(msg)

    def _getuid(self):
        uid = self.uidcnt
        self.uidcnt += 1
        return uid

    def parse_intro(self):
        """
        before(intro)
          before(intro@0)
          after(intro@0)
        after(intro)
        """
        # Internal
        it = self.it
        self._mylog("@parse_intro:before<{}>".format(it.peek()))

        # Reconstruct intro tactic
        bf_intro = next(it)
        bf_intro0 = next(it)
        af_intro0 = next(it)
        af_intro = next(it)
        return IntroTac(self._getuid(), (bf_intro, af_intro),
                        (bf_intro0, af_intro0))

    def parse_refl(self):
        """
        before(reflexivity)
        after(reflexivity)
        before(reflexivity@0)
        """
        # Internal
        it = self.it
        self._mylog("@parse_refl:before<{}>".format(it.peek()))

        bf_refl = next(it)
        af_refl = next(it)
        bf_refl0 = next(it)
        return ReflTac(self._getuid(), (bf_refl, af_refl), bf_refl0)

    def parse_ssrhave(self):
        """
        before(ssrhavefwdwbinders)
          before(ssrhave@0)
            TacTree
          after(ssrhave@0)
        after(ssrhavefwdwbinders)
        """
        # Internal
        it = self.it
        self._mylog("@parse_srrhave:before<{}>".format(it.peek()))

        # Reconstruct Ssreflect have tactic
        bf_havefwd = next(it)
        bf_have0 = next(it)
        body = self.parse_tactree()
        af_have0 = next(it)
        af_havefwd = next(it)
        return SsrhaveTac(self._getuid(), (bf_havefwd, af_havefwd),
                          (bf_have0, af_have0), body)

    def parse_generic(self):
        # Internal
        it = self.it
        self._mylog("@parse_generic:before<{}>".format(it.peek()))

        # Reconstruct base tactic
        acc = []
        decl = next(it)
        if not it.has_next():
            # TODO(deh): kludge, need to signal terminal state
            self._mylog("Terminal 1")
        elif decl.hdr.tac != it.peek().hdr.tac:
            # TODO(deh): kludge, need to signal terminal state
            self._mylog("Terminal 2")
        else:
            ngs = it.peek().hdr.ngs
            for _ in range(0, ngs - decl.hdr.ngs + 1):
                decl_p = next(it)
                acc += [decl_p]
        return GenericTac(self._getuid(), decl, acc)

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
            if decl.hdr.mode == TOK_BEFORE and \
               decl.hdr.tac == "intro":
                acc += [self.parse_intro()]
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac == "reflexivity":
                acc += [self.parse_refl()]
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac == "have (ssrhavefwdwbinders)":
                acc += [self.parse_ssrhave()]
            elif decl.hdr.mode == TOK_AFTER and \
                 decl.hdr.tac == "<ssreflect_plugin::ssrhave@0> $fwd":
                 return acc
            elif decl.hdr.mode == TOK_BEFORE:
                acc += [self.parse_generic()]
            else:
                self._mylog("Contents of accumulator before error")
                for before, after in acc:
                    self._mylog(before, after)
                raise NameError("Parsing error {}".format(decl))
        return acc
