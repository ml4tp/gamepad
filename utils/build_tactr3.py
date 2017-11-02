from enum import Enum
import matplotlib.pyplot as plt
import networkx as nx
import matplotlib.pyplot as plt

from parse_tacst2 import *


class TacEdge(object):
    def __init__(self, eid, tid, name, kind, ftac, src, tgt):
        self.eid = eid
        self.tid = tid
        self.name = name
        self.kind = kind
        self.ftac = ftac
        self.src = src
        self.tgt = tgt

    def __str__(self):
        return "({}, {}, {}, {} -> {})".format(self.eid, self.tid, self.name, self.src, self.tgt)

class TacTreeBuilder(object):
    def __init__(self, tacs, eid=0, solvgid=0, errgid=0, f_log=True):
        for tac in tacs:
            assert isinstance(tac, RawTac)

        # Reconstruction state
        self.tacs = tacs
        self.it_tacs = MyIter(tacs)   
        self.edges = []
        self.graph = nx.MultiDiGraph()

        # Internal counters
        self.eid = eid
        self.solvgid = solvgid
        self.errgid = errgid

        # Internal statistics
        self.f_log = f_log
        self.numtacs = 0
        self.notok = []

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            # self.log.append(msg)
            print(msg)

    def _add_edges(self, edges):
        self.edges += edges
        for edge in edges:
            self.graph.add_edge(edge.src, edge.tgt, key=edge.eid)

    def _fresh_eid(self):
        eid = self.eid
        self.eid += 1
        return eid

    def _fresh_errgid(self):
        errgid = self.errgid
        self.errgid += 1
        return "e" + str(errgid)

    def _fresh_solvgid(self):
        solvgid = self.solvgid
        self.solvgid += 1
        return "t" + str(solvgid)

    def _launch_rec(self, tacs):
        tr_builder = TacTreeBuilder(tacs, eid=self.eid,
                                    solvgid=self.solvgid, errgid=self.errgid)
        tr_builder.build_tacs()
        self.eid = tr_builder.eid
        self.solvgid = tr_builder.solvgid
        self.errgid = tr_builder.errgid
        self.notok += tr_builder.notok
        self.numtacs += tr_builder.numtacs
        return tr_builder.edges, tr_builder.graph

    def _is_terminal(self, decl):
        return decl.hdr.gid == GID_SOLVED or decl.hdr.mode == "afterE"

    def _mk_edge(self, tac, bf_decl, af_decl):
        if af_decl.hdr.gid == GID_SOLVED:
            edge = TacEdge(self._fresh_eid(), tac.uid, tac.name,
                           tac.kind, bf_decl.hdr.ftac,
                           bf_decl.hdr.gid, self._fresh_solvgid())
        elif af_decl.hdr.mode == "afterE":
            edge = TacEdge(self._fresh_eid(), tac.uid, tac.name,
                           tac.kind, bf_decl.hdr.ftac,
                           bf_decl.hdr.gid, self._fresh_errgid())
        else:
            edge = TacEdge(self._fresh_eid(), tac.uid, tac.name,
                           tac.kind, bf_decl.hdr.ftac,
                           bf_decl.hdr.gid, af_decl.hdr.gid)
        return edge

    def _mk_edge2(self, tac, bf_decl, gid):
        edge = TacEdge(self._fresh_eid(), tac.uid, tac.name,
                       tac.kind, bf_decl.hdr.ftac,
                       bf_decl.hdr.gid, gid)
        return edge

    def build_atomic(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_atomic:before<{}>".format(it_tacs.peek()))
        self.numtacs += 1

        tac = next(it_tacs)
        nbf = len(tac.bf_decls)
        naf = len(tac.af_decls)
        edges = []
        if nbf == naf:
            for bf_decl, af_decl in zip(tac.bf_decls, tac.af_decls):
                edges += [self._mk_edge(tac, bf_decl, af_decl)]
        elif naf % nbf == 0:
            # Compute branching ratio
            nbod = len(tac.bods)
            af2bf = int(naf / nbf)

            for i in range(0, nbf):
                start = i * af2bf
                end = i * af2bf + af2bf
                bf_decl = tac.bf_decls[i]
                for af_decl in tac.af_decls[start:end]:
                    edges += [self._mk_edge(tac, bf_decl, af_decl)]
        else:
            self.notok += [tac]

        self._add_edges(edges)

    def build_name(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_name:before<{}>".format(it_tacs.peek()))
        self.numtacs += 1

        tac = next(it_tacs)
        nbf = len(tac.bf_decls)
        naf = len(tac.af_decls)
        edges = []
        if nbf == naf:
            for bf_decl, af_decl in zip(tac.bf_decls, tac.af_decls):
                edges += [self._mk_edge(tac, bf_decl, af_decl)]
        else:
            self.notok += [tac]

        self._add_edges(edges)

    def build_notation(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_notation:before<{}>".format(it_tacs.peek()))
        self.numtacs += 1

        tac = next(it_tacs)
        for bf_decl, body in zip(tac.bf_decls, tac.bods):
            # 1. connect up body
            edges, _ = self._launch_rec(body)

            # TODO(deh): Skip notation?
            # TODO(deh): check for weirdness here
            # Accumulate changes
            self._add_edges(edges)

    def build_ml(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_ml:before<{}>".format(it_tacs.peek()))
        self.numtacs += 1

        tac = next(it_tacs)
        body = tac.bods[0]

        if tac.name.startswith("<coretactics::intro@0>"):
            # 1-1
            if len(tac.bf_decls) == len(tac.af_decls):
                edges = []
                for bf_decl, af_decl in zip(tac.bf_decls, tac.af_decls):
                    edges += [self._mk_edge(tac, bf_decl, af_decl)]
                # Accumulate changes
                self._add_edges(edges)
            else:
                self.notok += [tac]
        elif tac.name.startswith("<coretactics::constructor@0>") or \
             tac.name.startswith("<coretactics::exists@1>") or \
             tac.name.startswith("<coretactics::split@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrapply@1>") or \
             tac.name.startswith("<ssreflect_plugin::ssrcase@1>"):
            """
            TACTIC, # BEFORE, # BODY, # AFTER, FREQUENCY
            <coretactics::constructor@0>, 2, 0, 2, 2
            <coretactics::exists@1>, 4, 0, 4, 1
            <coretactics::exists@1>, 3, 0, 3, 1
            <coretactics::exists@1>, 2, 0, 4, 2
            <coretactics::exists@1>, 2, 0, 3, 1
            <coretactics::exists@1>, 2, 0, 2, 2
            <coretactics::exists@1>, 1, 0, 5, 1
            <coretactics::exists@1>, 1, 0, 3, 9
            <coretactics::exists@1>, 1, 0, 2, 415
            <coretactics::exists@1>, 1, 0, 1, 282
            <coretactics::split@0>, 2, 0, 4, 1
            <coretactics::split@0>, 2, 0, 1, 1
            <coretactics::split@0>, 1, 0, 5, 78
            <coretactics::split@0>, 1, 0, 4, 130
            <coretactics::split@0>, 1, 0, 3, 533
            <coretactics::split@0>, 1, 0, 2, 906
            <coretactics::split@0>, 1, 0, 1, 9278
            <ssreflect_plugin::ssrapply@1>, 2, 0, 2, 1
            <ssreflect_plugin::ssrapply@1>, 1, 0, 7, 1
            <ssreflect_plugin::ssrapply@1>, 1, 0, 5, 2
            <ssreflect_plugin::ssrapply@1>, 1, 0, 4, 1
            <ssreflect_plugin::ssrapply@1>, 1, 0, 3, 7
            <ssreflect_plugin::ssrapply@1>, 1, 0, 2, 12
            <ssreflect_plugin::ssrapply@1>, 1, 0, 1, 23
            <ssreflect_plugin::ssrcase@1>, 2, 0, 2, 2
            <ssreflect_plugin::ssrcase@1>, 1, 0, 2, 9
            <ssreflect_plugin::ssrcase@1>, 1, 0, 1, 14
            """
            # TODO(DEH): kludge
            if len(tac.af_decls) == len(tac.bf_decls):
                edges = []
                for bf_decl, af_decl in zip(tac.bf_decls, tac.af_decls):
                    edges += [self._mk_edge(tac, bf_decl, af_decl)]
                # Accumulate changes
                self._add_edges(edges)
            elif len(tac.bf_decls) == 1:
                edges = []
                bf_decl = tac.bf_decls[0]
                for af_decl in tac.af_decls:
                    edges += [self._mk_edge(tac, bf_decl, af_decl)]
                # Accumulate changes
                self._add_edges(edges)
            else:
                self.notok += [tac]
        elif tac.name.startswith("<g_auto::auto@0>") or \
             tac.name.startswith("<g_auto::eauto@0>"):
            """
            <g_auto::auto@0>, 13, 0, 1, 1
            <g_auto::auto@0>, 6, 0, 1, 1
            <g_auto::auto@0>, 5, 0, 1, 1
            <g_auto::auto@0>, 4, 0, 1, 1
            <g_auto::auto@0>, 1, 0, 1, 2
            <g_auto::eauto@0>, 4, 0, 1, 1
            """
            if len(tac.af_decls) == 1 and len(body) == 0:
                edges = []
                af_decl = tac.af_decls[0]
                for bf_decl in tac.bf_decls:
                    edges += [self._mk_edge(tac, bf_decl, af_decl)]
                # Accumulate changes
                self._add_edges(edges)
            else:
                self.notok += [tac]
            pass
        elif tac.name.startswith("<coretactics::assumption@0>") or \
             tac.name.startswith("<coretactics::clear@0>") or \
             tac.name.startswith("<coretactics::clearbody@0>") or \
             tac.name.startswith("<coretactics::constructor@1>") or \
             tac.name.startswith("<coretactics::exact@0>") or \
             tac.name.startswith("<coretactics::left@0>") or \
             tac.name.startswith("<coretactics::right@0>") or \
             tac.name.startswith("<coretactics::symmetry@0>") or \
             tac.name.startswith("<coretactics::transitivity@0>") or \
             tac.name.startswith("<extratactics::contradiction@0>") or \
             tac.name.startswith("<extratactics::discriminate@0>") or \
             tac.name.startswith("<g_auto::trivial@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrclear@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrcongr@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrmove@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrmove@2>") or \
             tac.name.startswith("<ssreflect_plugin::ssrpose@2>") or \
             tac.name.startswith("<ssreflect_plugin::ssrset@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrwithoutloss@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrwithoutlossss@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrwlogss@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrwlogs@0>"):
            if len(tac.bf_decls) == 1 and len(body) == 0:
                edges = []
                bf_decl = tac.bf_decls[0]
                for af_decl in tac.af_decls:
                    edges += [self._mk_edge(tac, bf_decl, af_decl)]
                # Accumulate changes
                self._add_edges(edges)
            else:
                self.notok += [tac]
        elif tac.name.startswith("<ssreflect_plugin::ssrapply@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrcase@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrelim@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrexact@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrexact@1>") or \
             tac.name.startswith("<ssreflect_plugin::ssrhave@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrmove@1>") or \
             tac.name.startswith("<ssreflect_plugin::ssrrewrite@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrsuff@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrsuffices@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrtclseq@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrwlog@0>"):
            if len(tac.bf_decls) == 1:
                edges = []
                if body:
                    # 1. connect up body
                    body_edges, body_graph = self._launch_rec(body)

                    # 2. connect up body to top-level
                    if body_edges:
                        for bf_decl in tac.bf_decls:
                            edges += [self._mk_edge2(tac, bf_decl,
                                      body_edges[0].src)]

                # 3. connect me up
                bf_decl = tac.bf_decls[0]
                for af_decl in tac.af_decls:
                    edges += [self._mk_edge(tac, bf_decl, af_decl)]

                # Accumulate changes
                if body:
                    self._add_edges(body_edges)
                self._add_edges(edges)
            else:
                self.notok += [tac]
        elif tac.name.startswith("<ssreflect_plugin::ssrtclby@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrtcldo@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrtclintros@0>"):
            # 1. connect up body
            body_edges, body_graph = self._launch_rec(body)

            # 2. connect up top-level before/after
            edges = []
            has_path = [0 for _ in range(len(tac.bf_decls))]
            for i, bf_decl in enumerate(tac.bf_decls):
                for af_decl in tac.af_decls:
                    try:
                        if nx.has_path(body_graph, bf_decl.hdr.gid, af_decl.hdr.gid):
                            edges += [self._mk_edge(tac, bf_decl, af_decl)]
                            has_path[i] += 1
                            break
                    except nx.exception.NodeNotFound:
                        has_path[i] += 1

            # Accumulate changes
            self._add_edges(body_edges)
            self._add_edges(edges)

            # Check for weirdness
            if any(x == 0 for x in has_path):
                self.notok += [tac]
        else:
            # TODO(deh): deprecate this case
            # 1. connect up body
            body_edges, body_graph = self._launch_rec(body)

            # 2. connect up top-level before/after
            edges = []
            has_path = [0 for _ in range(len(tac.bf_decls))]
            for i, bf_decl in enumerate(tac.bf_decls):
                for af_decl in tac.af_decls:
                    try:
                        if nx.has_path(body_graph, bf_decl.hdr.gid, af_decl.hdr.gid):
                            edges += [self._mk_edge(tac, bf_decl, af_decl)]
                            has_path[i] += 1
                            break
                    except nx.exception.NodeNotFound:
                        has_path[i] += 1

            # Accumulate changes
            self._add_edges(body_edges)
            self._add_edges(edges)

            # Check for weirdness
            if any(x == 0 for x in has_path):
                self.notok += [tac]

    def build_tacs(self):
        # Internal
        it_tacs = self.it_tacs
        
        while it_tacs.has_next():
            tac = it_tacs.peek()
            if tac.kind == TacKind.ATOMIC:
                self.build_atomic()
            elif tac.kind == TacKind.NAME:
                self.build_name()
            elif tac.kind == TacKind.ML:
                self.build_ml()
            elif tac.kind == TacKind.NOTATION:
                self.build_notation()
            else:
                raise NameError("TacKind {} not supported".format(tac.kind))

    def check_success(self):
        print("notok: {}, total: {}".format(len(self.notok), self.numtacs))
        ug = nx.Graph(self.graph)
        n = nx.algorithms.components.connected.number_connected_components(ug)
        print("# connected components: {}".format(n))
        return n == 1, n

    def show(self):
        # print("Graph edges:\n", "\n".join(map(str, self.graph.edges)))
        # print("TacEdges:\n", "\n".join(map(str, self.edges)))
        if self.graph.edges:
            nx.drawing.nx_pylab.draw_kamada_kawai(self.graph, with_labels=True)
            plt.show()
