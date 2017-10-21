import argparse
import matplotlib.pyplot as plt
import networkx as nx
import numpy as np

from lib.myiter import MyIter
from parse import *

"""
[Note]

Reconstruct tactic trees.

tstps ::= tstp | tstp tstps
tstp ::= b(n) a(1) ... a(n)
       | b(havefwd) b(have@0) nodes a(have@0) a(havefwd)

Case:
before(n-subgoal)
after(subgoal-1)
after(...)
after(subgoal-n)

Case:
before(ssrhavefwdwbinders)
  before(ssrhave@0)
    TacTree
  after(ssrhave@0)
after(ssrhavefwdwbinders)
"""


# -------------------------------------------------
# Preprocessing

# TODO(deh): deprecate?
def cleanup_lemma(lemma):
    decls = []
    for decl in lemma.decls:
        if decl.hdr.mode == "after1":
            continue
        if decl.hdr.tac == "intro":
            # print("REMOVING", decl)
            continue
        if decl.hdr.tac == "have (ssrhavefwdwbinders)":
            # print("REMOVING", decl)
            continue
        decls += [decl]
    lemma.decls = decls
    return lemma


def cleanup_lemmas(lemmas):
    for lemma in lemmas:
        cleanup_lemma(lemma)
    return lemmas


# -------------------------------------------------
# Data structure for reconstructing tactic tree.

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


class BaseTac(Tac):
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
            return "Base({}; {}, {})".format(self.uid, str(self.before),
                                             str(self.afters[0]))
        else:
            ps = ["({}, {})".format(self.before, after)
                  for after in self.afters]
            return "Base({}; {})".format(self.uid, ", ".join(ps))


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


# -------------------------------------------------
# Reconstructing tactic tree.

class TacTreeParser(object):
    def __init__(self, lemma, f_log=False):
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

    def parse_base(self):
        # Internal
        it = self.it
        self._mylog("@parse_base:before<{}>".format(it.peek()))

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
        return BaseTac(self._getuid(), decl, acc)

    def parse_intro(self):
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
        # Internal
        it = self.it
        self._mylog("@parse_refl:before<{}>".format(it.peek()))

        bf_refl = next(it)
        af_refl = next(it)
        bf_refl0 = next(it)
        return ReflTac(self._getuid(), (bf_refl, af_refl), bf_refl0)

    def parse_ssrhave(self):
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

    def parse_tactree(self):
        """
        Top-level recon function.
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
                acc += [self.parse_base()]
            else:
                self._mylog("Contents of accumulator before error")
                for before, after in acc:
                    self._mylog(before, after)
                raise NameError("Parsing error {}".format(decl))
        return acc


# -------------------------------------------------
# Building tactic tree.

class TacTreeBuilder(object):
    def __init__(self, tacs, f_log=False):
        for tac in tacs:
            assert isinstance(tac, Tac)

        self.tree = nx.DiGraph()
        self.tacs = tacs
        self.it_tacs = MyIter(tacs)
        self.f_log = f_log

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            # self.log.append(msg)
            print(msg)

    def _connect(self, curr_tac):
        for out_gid in curr_tac.out_edges():
            it = MyIter(self.tacs)
            while it.has_next():
                next_tac = next(it)
                in_gid = next_tac.in_edge()
                if out_gid == in_gid and curr_tac.uid != next_tac.uid:
                    self.tree.add_edge(curr_tac.uid, next_tac.uid)
                    self._mylog("Adding edge: {}-{}".
                                format(curr_tac.uid, next_tac.uid),
                                f_log=False)

    def build_base(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_base:before<{}>".format(it_tacs.peek()))

        # Build tactics without subtrees
        curr_tac = next(it_tacs)
        self._connect(curr_tac)

    def build_ssrhave(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_ssrhave:before<{}>".format(it_tacs.peek()))

        # Build ssrhave
        curr_tac = next(it_tacs)

        # Connect have goal
        builder = TacTreeBuilder(curr_tac.body, self.f_log)
        builder.build_tactree()
        # Merge graph into tree
        self.tree = nx.compose(self.tree, builder.tree)
        self._mylog("Merging: {}".format(self.tree.edges), f_log=False)
        if curr_tac.body:
            self.tree.add_edge(curr_tac.uid, curr_tac.body[0].uid)

        # Connect other goal
        self._connect(curr_tac)

    def build_subtac(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_subtac:before<{}>".format(it_tacs.peek()))

        # Build tactics with subtrees
        curr_tac = next(it_tacs)
        builder = TacTreeBuilder(curr_tac.body, self.f_log)
        builder.build_tactree()
        # Merge graph into tree
        self.tree = nx.compose(self.tree, builder.tree)
        self._mylog("Merging: {}".format(self.tree.edges), f_log=False)

        # Connect other goal
        self._connect(curr_tac)

    def build_tactree(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_tactree:before<{}>".format(it_tacs.peek()))

        while it_tacs.has_next():
            curr_tac = it_tacs.peek()
            if isinstance(curr_tac, SsrhaveTac):
                self.build_ssrhave()
            elif curr_tac.has_subtac():
                self.build_subtac()
            else:
                self.build_base()

    def show(self):
        nx.drawing.nx_pylab.draw_kamada_kawai(self.tree, with_labels=True)
        plt.show()


# -------------------------------------------------
# Reconstructing tactic tree.

def before_after(lemma):
    decls = lemma.decls
    bfaf = []
    stk = []
    foobar = []
    it = iter(MyIter(decls))
    while it.has_next():
        decl = next(it)
        if decl.hdr.mode == TOK_BEFORE:
            stk.append(decl)
        else:
            bf_decl = stk.pop()
            if decl.hdr.tac != bf_decl.hdr.tac:
                # TODO(deh): kludge, need to signal terminal state
                bfaf += [(bf_decl, bf_decl)]
                bf_decl = stk.pop()

            foobar += [(bf_decl, decl)]
            for _ in range(0, decl.hdr.ngs - bf_decl.hdr.ngs):
                decl_p = next(it)
                bfaf += [(bf_decl, decl_p)]
    for bf, af in bfaf:
        print(bf, af)
    return bfaf


def recon_tac_tree(lemma, f_draw=False):
    # Connect before/after tactics
    bfaf = before_after(lemma)

    # Build tree
    tree = nx.DiGraph()
    it = iter(MyIter(bfaf))
    root = it.peek()[1]
    tree.add_edge(mk_root_decl(), root)
    while it.has_next():
        curr_before, curr_after = next(it)
        it2 = iter(MyIter(bfaf))
        while it2.has_next():
            next_before, next_after = next(it2)
            if curr_after.hdr.gid == next_before.hdr.gid:
                tree.add_edge(curr_after, next_after)

            #if ssreflect_plugin::ssrhave@0
            # print("ADDING", curr_after, next_after)

    # Display tree
    if f_draw:
        nx.drawing.nx_pylab.draw_kamada_kawai(tree, with_labels=True)
        plt.show()

    return root, tree


# -------------------------------------------------
# Compute statistics

class TacStStats(object):
    def __init__(self, root, tree):
        self.root = root
        self.tree = tree

    def cnt_tac_sts(self):
        return len(self.tree.nodes)

    def cnt_have(self):
        cnt = 0
        for decl in self.tree.nodes:
            if decl.hdr.tac == "<ssreflect_plugin::ssrhave@0> $fwd":
                cnt += 1
            else:
                print("Skipping", decl)
        return cnt

    def cnt_term_tac_sts(self):
        # TODO(deh): broken
        term = []
        for node in self.tree.nodes:
            if len(self.tree.adj[node]) == 0:
                term += [node]
        return term

    def foobar(self):
        return nx.algorithms.simple_paths.all_simple_paths(self.tree, root=self.root)


def basic_have_stats(lemmas):
    total = 0
    haves = 0
    pfsizes = []
    for lemma in lemmas:
        size = 0
        for decl in lemma.decls:
            if decl.hdr.mode == TOK_BEFORE:
                if decl.hdr.tac == "<ssreflect_plugin::ssrhave@0> $fwd":
                    haves += 1
                total += 1
                size += 1
        pfsizes += [size]
    return (len(lemmas), haves, total, 1.0 * haves / (total + 1),
            np.mean(pfsizes))


def visualize(file):
    ts_parser = TacStParser(file, f_log=False)
    lemmas = ts_parser.parse_file()
    # cleanup_lemmas(lemmas)

    cnt = 0
    for lemma in lemmas:
        cnt += 1
        # lemma_p = cleanup_lemma(lemma)

        it = MyIter(lemma.decls)
        tr_parser = TacTreeParser(lemma)
        tacs = tr_parser.parse_tactree()
        for tac in tacs:
            print(tac)
            # print("HERE", before, after)
        tr_builder = TacTreeBuilder(tacs, False)
        print("")
        print("")
        print("")
        tr_builder.build_tactree()
        tr_builder.show()

        """
        root, tree = recon_tac_tree(lemma_p, f_draw=True)
        ts_stats = TacStStats(root, tree)
        print("# tactic states: {}".format(ts_stats.cnt_tac_sts()))
        print("# have: {}".format(ts_stats.cnt_have()))
        print("chains: {}".format(ts_stats.cnt_term_tac_sts()))
        """


if __name__ == "__main__":
    # Set up command line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("file",
                           help="Enter the file you want to visualize.")
    args = argparser.parse_args()

    visualize(args.file)

    # test_foo()
    # test_odd_order()


"""
def test_foo():
    filename = "./foo.dump"
    with open(filename, 'r') as f:
        tsparser = TacStParser(f, True)
        lemmas = tsparser.parse()
        lemmas_clean = []
        for lemma in lemmas:
            print(lemma)
            lemma_p = cleanup_lemma(lemma)
            print(lemma_p)

            root, tree = recon_tac_tree(lemma_p, f_draw=True)
            ts_stats = TacStStats(root, tree)
            print("# tactic states: {}".format(ts_stats.cnt_tac_sts()))
            print("# have: {}".format(ts_stats.cnt_have()))
            print("chains: {}".format(ts_stats.cnt_term_tac_sts()))


def test_odd_order():
    filename = "/Users/dehuang/Documents/research/pnh/mathcomp-odd-order-1.6.1/mathcomp/odd_order/build.log"
    with open(filename, 'r') as f:
        tsparser = TacStParser(f, False)
        for i in range(0, 34):
            lemmas = tsparser.parse()
            lemmas_clean = []
            for lemma in lemmas:
                # print(lemma)
                lemma_p = cleanup_lemma(lemma)
                # print(lemma_p)
            print(basic_have_stats(lemmas))
"""
