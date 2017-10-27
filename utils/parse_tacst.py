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

# TODO(deh): new proof format that (hopefully) gives all before/afters
#            should simplify parsing


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


class FixedTac(Tac):
    def __init__(self, uid, name, alias, core, terminal=False):
        assert isinstance(name, str)
        assert isinstance(alias[0], TacStDecl)
        assert isinstance(alias[1], TacStDecl)
        assert isinstance(core[0], TacStDecl)
        assert isinstance(core[1], TacStDecl)

        super().__init__(uid, terminal)
        self.name = name
        self.alias = alias
        self.core = core

    def my_name():
        return self.name

    def has_subtac(self):
        return False

    def in_edge(self):
        return self.alias[0].hdr.gid

    def out_edges(self):
        return [self.core[1].hdr.gid]

    def __str__(self):
        es = [str(self.alias[0]), str(self.core[0]),
              str(self.core[1]), str(self.alias[1])]
        return "{}({}; {})".format(self.name, self.uid, ", ".join(es))


class VaryTac(Tac):
    def __init__(self, uid, name, alias, bf_core, af_cores, terminal=False):
        assert isinstance(alias[0], TacStDecl)
        assert isinstance(alias[1], TacStDecl)
        assert isinstance(bf_core, TacStDecl)
        for after in af_cores:
            assert isinstance(after, TacStDecl)

        super().__init__(uid, terminal)
        self.name = name
        self.alias = alias
        self.bf_core = bf_core
        self.af_cores = af_cores

    def my_name():
        return self.name

    def has_subtac(self):
        return False

    def in_edge(self):
        return self.bf_core.hdr.gid

    def out_edges(self):
        return [after.hdr.gid for after in self.af_cores]

    def __str__(self):
        ps1 = [str(self.alias[0]), str(self.alias[1]), str(self.bf_core)]
        ps2 = [str(after) for after in self.af_cores]
        return "{}({}; {})".format(self.name, self.uid, ", ".join(ps1 + ps2))


class FixedNestedTac(Tac):
    def __init__(self, uid, name, alias, core, body):
        assert isinstance(alias[0], TacStDecl)
        assert isinstance(alias[1], TacStDecl)
        assert isinstance(core[0], TacStDecl)
        assert isinstance(core[1], TacStDecl)
        for tac in body:
            assert isinstance(tac, Tac)

        super().__init__(uid)
        self.name = name
        self.alias = alias
        self.core = core
        self.body = body

    def my_name():
        return self.name

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
        return "{}({}; {}; {})".format(self.name, self.uid, ", ".join(es),
                                       ", ".join(body))


class VaryNestedTac(Tac):
    def __init__(self, uid, name, bf_alias, bf_core,
                 af_cores, af_aliases, body, terminal=False):
        assert isinstance(bf_alias, TacStDecl)
        assert isinstance(bf_core, TacStDecl)
        for after in af_cores:
            assert isinstance(after, TacStDecl)
        for after in af_aliases:
            assert isinstance(after, TacStDecl)
        for tac in body:
            assert isinstance(tac, Tac)

        super().__init__(uid, terminal)
        self.name = name
        self.bf_alias = bf_alias
        self.bf_core = bf_core
        self.af_cores = af_cores
        self.af_aliases = af_aliases
        self.body = body

    def my_name():
        return self.name

    def has_subtac(self):
        return True

    def in_edge(self):
        return self.bf_alias.hdr.gid

    def out_edges(self):
        return [after.hdr.gid for after in self.af_aliases]

    def __str__(self):
        ps = ["({}, {})".format(self.bf_alias, after)
              for after in self.af_aliases]
        body = ", ".join([str(x) for x in self.body])
        return "{}({}; {}; {})".format(self.name, self.uid,
                                       ", ".join(ps), body)


class NestTermTac(Tac):
    def __init__(self, uid, alias_name, core_name, alias, core, extra):
        assert isinstance(alias, TacStDecl)
        assert isinstance(core, TacStDecl)
        for decl in extra:
            assert isinstance(decl, TacStDecl)

        super().__init__(uid)
        self.alias_name = alias_name
        self.core_name = core_name
        self.alias = alias
        self.core = core
        self.extra = extra

    def my_name():
        return self.alias_name

    def has_subtac(self):
        return False

    def in_edge(self):
        return self.alias.hdr.gid

    def out_edges(self):
        return [self.core.hdr.gid]

    def __str__(self):
        es = [str(self.alias), str(self.core)]
        return "{}({}; {})".format(self.alias_name, self.uid, ", ".join(es))


class SsrtclNestedTac(Tac):
    def __init__(self, uid, name, bf_core, af_cores, body):
        assert isinstance(bf_core, TacStDecl)
        for after in af_cores:
            assert isinstance(after, TacStDecl)
        for tac in body:
            assert isinstance(tac, Tac)

        super().__init__(uid)
        self.name = name
        self.bf_core = bf_core
        self.af_cores = af_cores
        self.body = body

    def my_name():
        return self.name

    def has_subtac(self):
        return True

    def in_edge(self):
        return self.bf_core.hdr.gid

    def out_edges(self):
        return [after.hdr.gid for after in self.af_cores]

    def __str__(self):
        es = [str(self.bf_core)] + [str(after) for after in self.af_cores]
        body = [str(tac) for tac in self.body]
        return "{}({}; {}; {})".format(self.name, self.uid, ", ".join(es),
                                       ", ".join(body))

class SsrrewriteKludgeTac(Tac):
    def __init__(self, uid, bf_aliases, af_aliases, bf_cores, af_cores):
        for before in bf_aliases:
            assert isinstance(before, TacStDecl)
        for after in af_aliases:
            assert isinstance(after, TacStDecl)
        for before in bf_cores:
            assert isinstance(before, TacStDecl)
        for after in af_cores:
            assert isinstance(after, TacStDecl)

        super().__init__(uid)
        self.bf_aliases = bf_aliases
        self.af_aliases = af_aliases
        self.bf_cores = bf_cores
        self.af_cores = af_cores

    def my_name():
        return "SsrrewriteKludge"

    def has_subtac(self):
        return False

    def in_edge(self):
        return self.bf_aliases[0].hdr.gid

    def out_edges(self):
        return [after.hdr.gid for after in self.af_aliases]

    def __str__(self):
        return "SsrrewriteKludge()"


class GenericTac(Tac):
    def __init__(self, uid, before, afters, terminal=False):
        assert isinstance(before, TacStDecl)
        for after in afters:
            assert isinstance(after, TacStDecl)

        super().__init__(uid, terminal)
        self.before = before
        self.afters = afters

    def my_name():
        return self.name

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
        self.depth = 0

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            # self.log.append(msg)
            print(" " * (2 * self.depth) + str(msg))

    def _getuid(self):
        uid = self.uidcnt
        self.uidcnt += 1
        return uid

    def parse_fixed_stk(self, name, terminal=False):
        """
        before(name)
          before(name@0)
          after(name@0)
        after(name)
        """
        # Internal
        it = self.it
        self._mylog("@parse_fixed_stk:before<{}>".format(it.peek()))

        # Reconstruct quad tactic that is nested
        bf_name = next(it)
        bf_name0 = next(it)
        af_name0 = next(it)
        af_name = next(it)
        return FixedTac(self._getuid(), name,
                        (bf_name, af_name), (bf_name0, af_name0), terminal)

    def parse_fixed_seq(self, name, terminal=False):
        """
        before(name)
        after(name)
        before(name@0)
        after(name@0)
        """
        # Internal
        it = self.it
        self._mylog("@parse_fixed_seq:before<{}>".format(it.peek()))

        # Reconstruct quad tactic that is sequential
        bf_name = next(it)
        af_name = next(it)
        bf_name0 = next(it)
        af_name0 = next(it)
        return FixedTac(self._getuid(), name,
                        (bf_name, af_name), (bf_name0, af_name0), terminal)

    def parse_vary_seq(self, name, terminal=False):
        """
        header:
        before(name)
        after(name)
        before(name0)

        tail:
        after(name0-1)
        after(name0-n)
        """
        # Internal
        it = self.it
        self._mylog("@parse_vary_seq:before<{}>".format(it.peek()))

        # Reconstruct header
        bf_name = next(it)
        af_name = next(it)
        bf_name0 = next(it)

        # Reconstruct tail
        acc = []
        terminal = False
        if it.peek().hdr.gid == GID_SOLVED:
            # Parse successful terminal state
            self._mylog("Successful terminal state")
            terminal = True
            acc += [next(it)]
        elif it.peek().hdr.mode == "afterE":
            # Parse failed terminal state
            self._mylog("Failed terminal state")
            terminal = True
            acc += [next(it)]
        else:
            # Parse constant or expanding number of goals
            ngs = it.peek().hdr.ngs
            for _ in range(0, ngs - bf_name0.hdr.ngs + 1):
                acc += [next(it)]
        return VaryTac(self._getuid(), name, (bf_name, af_name),
                       bf_name0, acc, terminal)

    def parse_nestterm(self, alias_name, core_name):
        """
        before(discriminate)
          before(discriminate@0)
          [after(discriminate@0)]
        [after(discriminate)]
        """
        # Internal
        it = self.it
        self._mylog("@parse_nestterm:before<{}>".format(it.peek()))

        bf_name = next(it)
        bf_name0 = next(it)
        extra = []
        if it.has_next() and \
           it.peek().hdr.tac.startswith(core_name):
            af_name0 = next(it)
            extra += [af_name0]
            if it.has_next() and \
               it.peek().hdr.tac.startswith(alias_name):
                af_name = next(it)
                extra += [af_name]
        return NestTermTac(self._getuid(), alias_name, core_name,
                           bf_name, bf_name0, extra)

    def parse_fixed_stk_nested(self, name):
        """
        before(name)
          before(name@0)
            TacTree
          after(name@0)
        after(name)
        """
        # Internal
        it = self.it
        self._mylog("@parse_fixed_stk_nested:before<{}>".format(it.peek()))

        # Reconstruct Ssreflect have tactic
        bf_name = next(it)
        bf_name0 = next(it)
        self.depth += 1
        body = self.parse_tactree()
        self.depth -= 1
        af_name0 = next(it)
        af_name = next(it)
        return FixedNestedTac(self._getuid(), name, (bf_name, af_name),
                              (bf_name0, af_name0), body)

    def parse_vary_stk_nested(self, name, nested=True):
        """
        before(name)
          before(name@0)
            TacTree
          after(name@0-1)
          ...
          after(name@0-n)
        after(name-1)
        ...
        after(name-n)
        """
        # Internal
        it = self.it
        self._mylog("@parse_vary_stk_nested:before<{}>".format(it.peek()))

        # Reconstruct tactic header
        bf_name = next(it)
        bf_name0 = next(it)

        if nested:
            body = self.parse_tactree()
        else:
            body = []

        # Reconstruct tactic tail
        acc0 = []
        acc = []
        terminal = False

        if it.peek().hdr.gid == GID_SOLVED:
            # Parse successful terminal state
            self._mylog("Successful terminal state")
            terminal = True
            acc0 += [next(it)]
            acc += [next(it)]
        elif it.peek().hdr.mode == "afterE":
            # Parse failed terminal state
            self._mylog("Failed terminal state")
            terminal = True
            acc0 += [next(it)]
            acc += [next(it)]
        else:
            # Parse constant or expanding number of goals
            ngs = it.peek().hdr.ngs
            for _ in range(0, ngs - bf_name0.hdr.ngs + 1):
                acc0 += [next(it)]
            for _ in range(0, ngs - bf_name.hdr.ngs + 1):
                acc += [next(it)]
        return VaryNestedTac(self._getuid(), name, bf_name, bf_name0,
                             acc0, acc, body, terminal)

    def parse_ssrrewrite_kludge(self):
        """
        before(name-1)
          before(name@0-1)
          after(name@0-1)
        ...
        before(name-n)
          before(name@0-n)
          after(name@0-n)
        """
        # Internal
        it = self.it
        self._mylog("@parse_ssrrewrite_kludge<{}>".format(it.peek()))

        loc = it.peek().hdr.loc

        bf_aliases = []
        bf_cores = []
        af_cores = []
        af_aliases = []
        while True:
            decl = it.peek()
            if decl.hdr.mode == TOK_BEFORE and \
               decl.hdr.loc == loc:
                bf_aliases += [next(it)]
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrrewrite@0>"):
                bf_cores += [next(it)]
            elif decl.hdr.mode == TOK_AFTER and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrrewrite@0>"):
                af_cores += [next(it)]
            elif decl.hdr.mode == TOK_AFTER and \
                 decl.hdr.loc == loc:
                af_aliases += [next(it)]
            else:
                break
        return SsrrewriteKludgeTac(self._getuid(), bf_aliases,
                                   af_aliases, bf_cores, af_cores)

    def parse_ssrtcl_nested(self, name):
        """
        before(name@0)
          TacTree
        after(name@0-1)
        ...
        after(name@0-n)
        """
        # Internal
        it = self.it
        self._mylog("@parse_srrtcl_nested:before<{}>".format(it.peek()))

        # Reconstruct head
        bf_name0 = next(it)
        self.depth += 1
        body = self.parse_tactree()
        self.depth -= 1

        # Reconstruct tail
        acc = []
        if it.peek().hdr.gid == GID_SOLVED:
            # Parse successful terminal state
            self._mylog("Successful terminal state")
            terminal = True
            acc += [next(it)]
        elif it.peek().hdr.mode == "afterE":
            # Parse failed terminal state
            self._mylog("Failed terminal state")
            terminal = True
            acc += [next(it)]
        else:
            # Parse constant or expanding number of goals
            ngs = it.peek().hdr.ngs
            for _ in range(0, ngs - bf_name0.hdr.ngs + 1):
                acc += [next(it)]
        return SsrtclNestedTac(self._getuid(), name, bf_name0, acc, body)

    def parse_generic(self):
        # Internal
        it = self.it
        self._mylog("@parse_generic:before<{}>".format(it.peek()))

        # Reconstruct base tactic
        acc = []
        decl = next(it)
        terminal = False
        if not it.has_next():
            # TODO(deh): kludge?
            self._mylog("Terminal kludge1?")
            terminal = True
        elif decl.hdr.tac != it.peek().hdr.tac:
            # TODO(deh): kludge?
            self._mylog("Terminal kludge2?")
            terminal = True
        elif it.peek().hdr.ngs == 0:
            # Parse terminal state
            self._mylog("Terminal number of goals is 0")
            terminal = True
            acc += [next(it)]
        else:
            # Parse constant or expanding number of goals
            ngs = it.peek().hdr.ngs
            for _ in range(0, ngs - decl.hdr.ngs + 1):
                # decl_p = next(it)
                acc += [next(it)]
        return GenericTac(self._getuid(), decl, acc, terminal)

    # TODO(deh): Complete kludge, need to fix
    def parse_kludge(self, burn):
        # Internal
        it = self.it
        self._mylog("@parse_generic:before<{}>".format(it.peek()))

        decl = next(it)
        acc = []
        for _ in range(burn - 1):
            acc += [next(it)]
        return GenericTac(self._getuid(), decl, acc, False)

    # TODO(deh): Complete kludge, need to fix
    def parse_kludge_apply(self):
        # Internal
        it = self.it
        self._mylog("@parse_generic:before<{}>".format(it.peek()))

        decl = next(it)
        acc = []
        acc += [next(it)]
        acc += [next(it)]
        acc += [next(it)]
        return GenericTac(self._getuid(), decl, acc, False)

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


            # ----------------------------------------------
            # Ssreflect tactics

            # TODO(deh): Investigate kludge
            #if decl.hdr.loc == "(./BGsection1.v,60666,60679)":
            #    acc += [self.parse_kludge(7)]
            if decl.hdr.loc == "(./BGsection1.v,60420,60424)":
                acc += [self.parse_kludge(20)]
            elif decl.hdr.loc == "(./BGsection2.v,13550,13556)":
                acc += [self.parse_kludge(3)]
            elif decl.hdr.loc == "(./BGsection6.v,13539,13544)":
                acc += [self.parse_kludge(4)]
            elif decl.hdr.loc == "(./BGsection8.v,2178,2189)":
                acc += [self.parse_kludge(8)]
            elif decl.hdr.loc == "(./BGsection9.v,24713,24739)":
                acc += [self.parse_kludge(8)]
            elif decl.hdr.loc == "(./BGsection11.v,5300,5327)":
                acc += [self.parse_kludge(7)]
            elif decl.hdr.loc == "(./BGsection12.v,4462,4480)":
                acc += [self.parse_kludge(8)]
            elif decl.hdr.loc == "(./BGsection12.v,24997,25021)":
                acc += [self.parse_kludge(8)]
                

            # Non-terminal, fixed-width, stack cases
            # Non-terminal, fixed-width, sequential cases
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("congr (ssrcongrarg)"):
                acc += [self.parse_fixed_seq("Ssrcongr")]
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("pose (ssrfwdid) (ssrposefwd)"):
                acc += [self.parse_fixed_seq("Ssrpose")]
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("set (ssrfwdid) (ssrsetfwd) (ssrclauses)"):
                acc += [self.parse_fixed_seq("Ssrset")]

            # Fixed-width, nested cases (paired)
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("by (ssrhintarg)"):
                acc += [self.parse_fixed_stk_nested("Ssrby")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrtclby@0>"):
                return acc

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("exact (ssrexactarg)"):
                acc += [self.parse_fixed_stk_nested("Ssrexact")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrexact@0>"):
                return acc

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("suff (ssrsufffwd)"):
                acc += [self.parse_fixed_stk_nested("Ssrsuff")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrsuff@0>"):
                return acc

            # Variable-width, non-nested cases
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("case (ssrcasearg) (ssrclauses)"):
                acc += [self.parse_vary_stk_nested("Ssrcase", nested=False)]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrcase@0>"):
                return acc
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrcase@1>"):
                return acc

            elif decl.hdr.mode == TOK_BEFORE and\
                 decl.hdr.tac.startswith("suffices"):
                acc += [self.parse_vary_stk_nested("Ssrsuffices", nested=False)]
            elif decl.hdr.mode == TOK_BEFORE and\
                 decl.hdr.tac.startswith("wlog (ssrhpats_nobs) (ssrwlogfwd) (ssrhint)"):
                acc += [self.parse_vary_stk_nested("Ssrwlog", nested=False)]
            elif decl.hdr.mode == TOK_BEFORE and\
                 decl.hdr.tac.startswith("without loss"):
                acc += [self.parse_vary_stk_nested("Ssrwithoutloss", nested=False)]

            # Variable-width, nested cases (paired)
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("apply (ssrapplyarg)"):
                acc += [self.parse_vary_stk_nested("Ssrapply")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrapply@0>"):
                return acc
            #elif decl.hdr.mode.startswith(TOK_AFTER) and \
            #     decl.hdr.tac.startswith("<ssreflect_plugin::ssrapply@1>"):
            #    return acc

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("apply") and \
                 self.it.lookahead(1).hdr.tac.startswith("<ssreflect_plugin::ssrapply@1>"):
                acc += [self.parse_vary_stk_nested("Ssrapply1", nested=False)]

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("elim (ssrarg) (ssrclauses)"):
                acc += [self.parse_vary_stk_nested("Ssrelim")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrelim@0>"):
                return acc

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("have (ssrhavefwdwbinders)"):
                acc += [self.parse_vary_stk_nested("Ssrhave")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrhave@0>"):
                return acc

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("move (ssrmovearg) (ssrclauses)"):
                acc += [self.parse_vary_stk_nested("Ssrmove")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrmove@1>"):
                return acc

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("move (ssrmovearg) (ssrrpat)"):
                acc += [self.parse_vary_stk_nested("Ssrmove")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrmove@0>"):
                return acc

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("rewrite (ssrrwargs) (ssrclauses)"):
                f_kludge = False
                n = 1
                while True:
                    decl_p = self.it.lookahead(n)
                    if decl_p.hdr.mode == TOK_AFTER and \
                       decl.hdr.loc == decl_p.hdr.loc:
                        break
                    elif decl_p.hdr.mode == TOK_BEFORE and \
                         decl.hdr.loc == decl_p.hdr.loc:
                        f_kludge = True
                        break
                    n += 1
                if f_kludge:
                    acc += [self.parse_ssrrewrite_kludge()]
                else:
                    acc += [self.parse_vary_stk_nested("Ssrrewrite")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrrewrite@0>"):
                return acc

            # Tactical cases (paired)
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrtcldo@0>"):
                acc += [self.parse_ssrtcl_nested("Ssrtcldo")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrtcldo@0>"):
                return acc

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrtclintros@0>"):
                acc += [self.parse_ssrtcl_nested("Ssrtclintros")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrtclintros@0>"):
                return acc

            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrtclseq@0>"):
                acc += [self.parse_ssrtcl_nested("Ssrtclseq")]
            elif decl.hdr.mode.startswith(TOK_AFTER) and \
                 decl.hdr.tac.startswith("<ssreflect_plugin::ssrtclseq@0>"):
                return acc

            # ----------------------------------------------
            # Coq tactics

            # Non-terminal, fixed-width, stack cases
            elif decl.hdr.mode == TOK_BEFORE and \
               decl.hdr.tac.startswith("intro") and \
               not decl.hdr.tac.startswith("intros"):
                acc += [self.parse_fixed_stk("Intro")]
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("case"):
                acc += [self.parse_fixed_stk("Case")]

            # Terminal, fixed-width, stack cases
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("auto"):
                acc += [self.parse_fixed_stk("Auto", True)]
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("contradiction"):
                acc += [self.parse_fixed_stk("Contradiction", True)]
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("exact"):
                acc += [self.parse_fixed_stk("Exact", True)]
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("trivial"):
                acc += [self.parse_fixed_stk("trivial", True)]

            # Terminal, fixed-width, sequential cases
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("assumption"):
                acc += [self.parse_fixed_seq("Assumption", True)]
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("reflexivity"):
                acc += [self.parse_fixed_seq("Reflexivity", True)]

            # Variable-width, stack cases
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("exists"):
                acc += [self.parse_vary_stk_nested("Exists", nested=False)]

            # Variable-width, sequential cases
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("split"):
                acc += [self.parse_vary_seq("Split")]

            # TODO(deh): look at this again, terminal optional nested cases
            elif decl.hdr.mode == TOK_BEFORE and \
                 decl.hdr.tac.startswith("discriminate"):
                acc += [self.parse_nestterm("discriminate",
                                            "<extratactics::discriminate@0>")]

            # See generic for variable-width, sequential cases
            # Variable-depth nested cases
            elif decl.hdr.mode == TOK_BEFORE:
                # apply
                # rewrite
                # simpl
                acc += [self.parse_generic()]
            else:
                self._mylog("Contents of accumulator before error")
                for tac in acc:
                    self._mylog(tac)
                raise NameError("Parsing error {}".format(decl))
        return acc
