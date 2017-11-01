from enum import Enum
import matplotlib.pyplot as plt
import networkx as nx

from parse_tacst2 import *

"""
[Note]

Goal: [Tac] -> TacTree
"""

class PathKind(Enum):
    CONST = 0
    CONSTB = 1
    BRANCH = 2
    NARROW = 3


class Path(object):
    def __init__(self, kind, bf_decl, body, af_decls):
        assert isinstance(kind, PathKind)
        assert isinstance(bf_decl, TacStDecl)
        for tac in body:
            assert isinstance(tac, PathTac)
        for af_decl in af_decls:
            assert isinstance(af_decl, TacStDecl)

        self.kind = kind
        self.bf_decl = bf_decl
        self.af_decls = af_decls
        self.body = body

    def __str__(self):
        body = ", ".join([str(tac) for tac in self.body])
        af_decls = ", ".join([str(af_decl) for af_decl in self.af_decls])
        return "<{}; {}; {}>".format(self.bf_decl, body, af_decls)


class PathTac(object):
    def __init__(self, uid, name, kind, paths):
        assert isinstance(kind, TacKind)
        for path in paths:
            assert isinstance(path, Path)

        super().__init__(uid)
        self.name = name
        self.kind = kind
        self.paths = paths

    def my_name():
        return self.name

    def has_subtac(self):
        # TODO(deh): is this correct?
        return len(self.bods) > 0

    def in_edges(self):
        return [bf_decl.hdr.gid for bf_decl in self.bf_decls]

    def out_edges(self):
        return [af_decl.hdr.gid for af_decl in self.af_decls]

    def pp(self, tab=0):
        s1 = "{}({}, {}) {{\n".format(self.name, self.uid, self.kind)
        paths = "\n".join([(tab + 2) * " " + str(path) for path in self.paths])
        return s1 + paths + "\n}"

    def __str__(self):
        paths = "\n".join([str(path) for path in self.paths])
        return "{}({}; {}; {})".format(self.name, self.uid, self.kind, paths)

# -------------------------------------------------
# Building tactic tree.

class TacPathBuilder(object):
    def __init__(self, tacs, f_log=False):
        for tac in tacs:
            assert isinstance(tac, RawTac)

        self.tree = nx.DiGraph()
        self.tacs = tacs
        self.it_tacs = MyIter(tacs)
        self.f_log = f_log

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            # self.log.append(msg)
            print(msg)

    def build_constant(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_constant:before<{}>".format(it_tacs.peek()))
        self.cnt += 1

        # Build
        tac = next(it_tacs)
        paths = []
        for bf_decl, af_decl in zip(tac.bf_decls, tac.af_decls):
            paths += [Path(PathKind.CONST, bf_decl, [], [af_decl])]
        return PathTac(tac.uid, tac.name, tac.kind, paths)

    def build_constant_body(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_constant_body:before<{}>".format(it_tacs.peek()))

        # Build
        tac = next(it_tacs)
        paths = []
        for bf_decl, body, af_decl in zip(tac.bf_decls, tac.bods, tac.af_decls):
            tp_builder = TacPathBuilder(body)
            body_p = tp_builder.build_tacpath()
            paths += [Path(PathKind.CONSTB, bf_decl, body_p, [af_decl])]
        return PathTac(tac.uid, tac.name, tac.kind, paths)

    def build_branching(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_branching:before<{}>".format(it_tacs.peek()))

        # Compute branching ratio
        tac = next(it_tacs)
        nbf = len(tac.bf_decls)
        nbod = len(tac.bods)
        naf = len(tac.af_decls)
        af2bf = int(naf / nbf)

        # Build
        paths = []
        for i in range(0, nbf):
            bf_decl = tac.bf_decls[i]
            tp_builder = TacPathBuilder(tac.bods[i])
            body_p = tp_builder.build_tacpath()
            start = i * af2bf
            end = i * af2bf + af2bf
            af_decls = tac.af_decls[start:end]
            paths += [Path(PathKind.BRANCH, bf_decl, body_p, af_decls)]
        return PathTac(tac.uid, tac.name, tac.kind, paths)

    def build_narrowing(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_narrowing:before<{}>".format(it_tacs.peek()))

        # Build
        tac = next(it_tacs)
        paths = []
        for bf_decl, body in zip(tac.bf_decls, tac.bods):
            tp_builder = TacPathBuilder(body)
            body_p = tp_builder.build_tacpath()
            paths += [Path(PathKind.NARROW, bf_decl, body_p, tac.af_decls)]
        return PathTac(tac.uid, tac.name, tac.kind, paths)

    def build_kludge(self):
        # Internal
        it_tacs = self.it_tacs

        """
        (<TacKind.NOTATION: 3>, 2, 2, 1): 159?
        (<TacKind.NOTATION: 3>, 4, 4, 1): 21,
        (<TacKind.NOTATION: 3>, 3, 3, 1): 47,
        (<TacKind.NOTATION: 3>, 8, 8, 1): 1,
        (<TacKind.NOTATION: 3>, 6, 6, 1): 4,
        (<TacKind.NOTATION: 3>, 5, 5, 1): 8,
        (<TacKind.NOTATION: 3>, 7, 7, 1): 1,
        (<TacKind.NOTATION: 3>, 13, 13, 1): 1,

        (<TacKind.ML: 4>, 2, 1, 1): 9,
        (<TacKind.ML: 4>, 3, 1, 1): 4,
        (<TacKind.ML: 4>, 4, 1, 1): 3,
        (<TacKind.ML: 4>, 5, 1, 1): 1,
        (<TacKind.ML: 4>, 13, 1, 1): 1,
        (<TacKind.ML: 4>, 6, 1, 1): 1,

        (<TacKind.NOTATION: 3>, 1, 1, 0): 4,
        (<TacKind.ML: 4>, 1, 1, 0): 4,

        (<TacKind.NOTATION: 3>, 2, 2, 3): 22,
        (<TacKind.NOTATION: 3>, 4, 4, 10): 2,
        (<TacKind.NOTATION: 3>, 5, 5, 7): 1,
        (<TacKind.NOTATION: 3>, 5, 5, 6): 1,
        (<TacKind.NOTATION: 3>, 3, 3, 5): 3,
        (<TacKind.NOTATION: 3>, 3, 3, 4): 7,
        (<TacKind.NOTATION: 3>, 3, 3, 16): 1
        (<TacKind.NOTATION: 3>, 2, 2, 5): 4,
        (<TacKind.NOTATION: 3>, 3, 3, 7): 1,
        (<TacKind.NOTATION: 3>, 2, 2, 7): 1,

        (<TacKind.NOTATION: 3>, 4, 4, 2): 12,
        (<TacKind.NOTATION: 3>, 3, 3, 2): 19,
        (<TacKind.NOTATION: 3>, 7, 7, 4): 1,
        (<TacKind.NOTATION: 3>, 7, 7, 2): 2,
        (<TacKind.NOTATION: 3>, 6, 6, 4): 2,
        (<TacKind.NOTATION: 3>, 8, 8, 3): 1,
        (<TacKind.NOTATION: 3>, 4, 4, 3): 2,
        (<TacKind.NOTATION: 3>, 5, 5, 2): 5,
        (<TacKind.NOTATION: 3>, 9, 9, 3): 1,
        
        (<TacKind.ML: 4>, 4, 1, 4): 1,
        (<TacKind.ML: 4>, 3, 1, 3): 1,
        (<TacKind.ML: 4>, 2, 1, 2): 19,
        
        (<TacKind.ML: 4>, 3, 1, 2): 1,
        (<TacKind.ML: 4>, 2, 1, 6): 1,
        (<TacKind.ML: 4>, 2, 1, 3): 1,
        (<TacKind.ML: 4>, 2, 1, 4): 4,
        """

        tac = next(it_tacs)
        self._mylog("ERROR: Cannot reconstruct paths where \
                     (nbf={}, nbod={}, naf={}) in {}".format(
                     nbf, nbod, naf, curr_tac))
        tp_builder = TacPathBuilder(body)
        body_p = tp_builder.build_tacpath()

        return PathTac(tac.uid, "FAILBOAT", tac.kind, [])


    def build_tacpath(self):
        # Internal
        it_tacs = self.it_tacs
        if it_tacs.has_next():
            self._mylog("@build_tacpath:before<{}>".format(it_tacs.peek()))
        else:
            self._mylog("@build_tacpath:before<{}>".format("empty"))

        acc = []
        while it_tacs.has_next():
            curr_tac = it_tacs.peek()

            nbf = len(curr_tac.bf_decls)
            nbod = len(curr_tac.bods)
            naf = len(curr_tac.af_decls)
            if nbf == naf and nbf == nbod:
                acc += [self.build_constant()]
            elif nbf == naf and nbod == 0:
                acc += [self.build_constant2()]
            elif naf % nbf == 0 and nbf == nbod:
                acc += [self.build_branching()]
            elif naf == 1 and nbf == nbod:
                acc += [self.build_narrowing()]
            else:
                acc += [self.build_kludge()]
                """
                raise NameError("ERROR: Cannot reconstruct paths where \
                                 (nbf={}, nbod={}, naf={}) in {}".format(
                                 nbf, nbod, naf, curr_tac))
                """
        return acc


# -------------------------------------------------
# Building tactic tree.

class TacInfo(object):
    pass


class Edge(object):
    pass


class AtomicEdge(Edge):
    def __init__(self, before, after, tacinfo):
        assert isinstance(before, TacStDecl)
        assert isinstance(after, TacStDecl)
        assert isinstance(tacinfo, TacInfo)

        self.before = before
        self.after = after
        self.tacinfo = tacinfo


class PathEdge(Edge):
    def __init__(self, before, after, edges, tacinfo):
        assert isinstance(before, TacStDecl)
        assert isinstance(after, TacStDecl)
        for edge in edges:
            assert isinstance(edge, Edge)
        assert isinstance(tacinfo, TacInfo)

        self.before = before
        self.after = after
        self.edges = edges
        self.tacinfo = tacinfo



class TacTreeBuilder(object):
    def __init__(self, tacs, f_log=False):
        for tac in tacs:
            assert isinstance(tac, RawTac)

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

    def build_atomic(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_atomic:before<{}>".format(it_tacs.peek()))

        # Build atomic tactics
        curr_tac = next(it_tacs)
        self._connect(curr_tac)

    def build_subtac(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_subtac:before<{}>".format(it_tacs.peek()))

        # Build ssrhave
        curr_tac = next(it_tacs)

        # Connect have goal
        for body in curr_tac.bods:
            builder = TacTreeBuilder(body, self.f_log)
            builder.build_tactree()
            # Merge graph into tree
            self.tree = nx.compose(self.tree, builder.tree)
            self._mylog("Merging: {}".format(self.tree.edges), f_log=False)
            if body:
                self.tree.add_edge(curr_tac.uid, body[0].uid)

        # Connect other goal
        self._connect(curr_tac)

    def build_tactree(self):
        # Internal
        it_tacs = self.it_tacs
        if it_tacs.has_next():
            self._mylog("@build_tactree:before<{}>".format(it_tacs.peek()))
        else:
            self._mylog("@build_tactree:before<{}>".format("empty"))

        while it_tacs.has_next():
            curr_tac = it_tacs.peek()
            if curr_tac.has_subtac():
                self.build_subtac()
            else:
                self.build_base()

    def show(self):
        nx.drawing.nx_pylab.draw_kamada_kawai(self.tree, with_labels=True)
        plt.show()
