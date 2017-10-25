import matplotlib.pyplot as plt
import networkx as nx

from parse_tacst import *

"""
[Note]

Goal: [Tac] -> TacTree
"""


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
            if isinstance(curr_tac, FixedNestedTac):
                self.build_ssrhave()
            elif curr_tac.has_subtac():
                self.build_subtac()
            else:
                self.build_base()

    def show(self):
        nx.drawing.nx_pylab.draw_kamada_kawai(self.tree, with_labels=True)
        plt.show()


# -------------------------------------------------
# TODO(deh): deprecate?

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


# TODO(deh): deprecate?
def cleanup_lemmas(lemmas):
    for lemma in lemmas:
        cleanup_lemma(lemma)
    return lemmas
