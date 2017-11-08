from enum import Enum
import matplotlib.pyplot as plt
import networkx as nx
import plotly
import plotly.plotly as py
from plotly.graph_objs import *

from parse_tacst import *


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


class TacTree(object):
    def __init__(self, name, edges, graph, gid2info):
        self.name = name
        self.edges = edges
        self.graph = graph
        self.gid2info = gid2info

        self._build_tacsts()
        self._build_tacs()

    def _build_tacsts(self):
        self.tacsts = []
        for node in self.graph.nodes():
            if node in self.gid2info:
                ctx, goal = self.gid2info[node]
                self.tacsts += [(node, ctx, goal)]

    def _build_tacs(self):
        self.tactics = {}
        for edge in self.edges:
            if edge.tid in self.tactics:
                self.tactics[edge.tid] += [edge]
            else:
                self.tactics[edge.tid] = [edge]

    def gids(self):
        return [ gid for gid, _, _ in self.tacsts ]

    def contexts(self):
        return [ ctx for _, ctx, _ in self.tacsts ]

    def goals(self):
        return [ gid for _, _, goal in self.tacsts ]

    def in_edge(self, gid):
        gids = list(self.graph.predecessors(gid))
        acc = []
        for edge in self.edges:
            if edge.src in gids and edge.tgt == gid:
                acc += [edge]
        return acc

    def out_edges(self, gid):
        gids = list(self.graph.successors(gid))
        acc = []
        for edge in self.edges:
            if edge.tgt in gids and edge.src == gid:
                acc += [edge]
        return acc

    def dump(self):
        print(">>>>>>>>>>>>>>>>>>>>")
        print("Tactic states:", self.tacsts)
        print("Tactics:", self.tactics)
        for gid in self.gids():
            print("In edge for {}:".format(gid), self.in_edge(gid))
            print("Out edges for {}:".format(gid), self.out_edges(gid))
        print("<<<<<<<<<<<<<<<<<<<<")


class TacTreeBuilder(object):
    def __init__(self, name, tacs, gid2info, eid=0, solvgid=0, errgid=0, f_log=False):
        for tac in tacs:
            assert isinstance(tac, RawTac)

        self.name = name

        # Reconstruction state
        self.tacs = tacs
        self.it_tacs = MyIter(tacs)   
        self.edges = []
        self.graph = nx.MultiDiGraph()
        self.gid2info = gid2info

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
        tr_builder = TacTreeBuilder(self.name, tacs, self.gid2info, eid=self.eid,
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
        if bf_decl.hdr.gid == GID_SOLVED:
            return []

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
        return [edge]

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
                edges += self._mk_edge(tac, bf_decl, af_decl)
        elif naf % nbf == 0:
            # Compute branching ratio
            nbod = len(tac.bods)
            af2bf = int(naf / nbf)

            for i in range(0, nbf):
                start = i * af2bf
                end = i * af2bf + af2bf
                bf_decl = tac.bf_decls[i]
                for af_decl in tac.af_decls[start:end]:
                    edges += self._mk_edge(tac, bf_decl, af_decl)
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
                edges += self._mk_edge(tac, bf_decl, af_decl)
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
                    edges += self._mk_edge(tac, bf_decl, af_decl)
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
                    edges += self._mk_edge(tac, bf_decl, af_decl)
                # Accumulate changes
                self._add_edges(edges)
            elif len(tac.bf_decls) == 1:
                edges = []
                bf_decl = tac.bf_decls[0]
                for af_decl in tac.af_decls:
                    edges += self._mk_edge(tac, bf_decl, af_decl)
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
                    edges += self._mk_edge(tac, bf_decl, af_decl)
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
                    edges += self._mk_edge(tac, bf_decl, af_decl)
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
                            # every gid that does not have a parent is connected to the top
                            for edge in body_edges:
                                self_edges = 0
                                for edge_p in body_graph.in_edges(edge.src):
                                    if edge_p[0] == edge_p[1]:
                                        self_edges += 1
                                if body_graph.in_degree(edge.src) == self_edges:
                                    edges += [self._mk_edge2(tac, bf_decl,
                                              edge.src)]
                            #edges += [self._mk_edge2(tac, bf_decl,
                            #          body_edges[0].src)]

                # 3. connect me up
                bf_decl = tac.bf_decls[0]
                for af_decl in tac.af_decls:
                    edges += self._mk_edge(tac, bf_decl, af_decl)

                # Accumulate changes
                if body:
                    self._add_edges(body_edges)
                self._add_edges(edges)
            else:
                self.notok += [tac]
        elif tac.name.startswith("<ssreflect_plugin::ssrtclby@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrtcldo@0>") or \
             tac.name.startswith("<ssreflect_plugin::ssrtclintros@0>"):
            # NOTE(deh): ssrtclby@0 always ends in terminal?
            # 1. connect up body
            body_edges, body_graph = self._launch_rec(body)

            # 2. connect up top-level before/after
            edges = []
            has_path = [0 for _ in range(len(tac.bf_decls))]
            for i, bf_decl in enumerate(tac.bf_decls):
                for af_decl in tac.af_decls:
                    try:
                        if nx.has_path(body_graph, bf_decl.hdr.gid, af_decl.hdr.gid):
                            edges += self._mk_edge(tac, bf_decl, af_decl)
                            has_path[i] += 1
                            break
                    except nx.exception.NodeNotFound:
                        has_path[i] += 1

            # 3. connect me up
            for bf_decl in tac.bf_decls:
                for af_decl in tac.af_decls:
                    edges += self._mk_edge(tac, bf_decl, af_decl)

            # Accumulate changes
            self._add_edges(body_edges)
            self._add_edges(edges)

            # Check for weirdness
            if any(x == 0 for x in has_path):
                self.notok += [tac]
        else:
            pass

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
        ccs = list(nx.algorithms.components.connected.connected_components(ug))
        n = len(ccs)
        # n = nx.algorithms.components.connected.number_connected_components(ug)
        print("# connected components: {}".format(n))
        return n == 1, n

    def get_tactree(self, f_verbose):
        tactr = TacTree(self.name, self.edges, self.graph, self.gid2info)

        if f_verbose:
            tactr.dump()

        return tactr

    def show(self):
        # print("Graph edges:\n", "\n".join(map(str, self.graph.edges)))
        # print("TacEdges:\n", "\n".join(map(str, self.edges)))
        if self.graph.edges:
            nx.drawing.nx_pylab.draw_kamada_kawai(self.graph, with_labels=True)
            plt.show()

    def show_jupyter(self):
        G = self.graph
        pos = nx.drawing.layout.kamada_kawai_layout(G)

        # Edges
        edge_trace = Scatter(x=[], y=[], line=Line(width=0.5,color='#888'),
                             hoverinfo=None, mode='lines')
        for edge in G.edges():
            x0, y0 = pos[edge[0]]
            x1, y1 = pos[edge[1]]
            edge_trace['x'] += [x0, x1, None]
            edge_trace['y'] += [y0, y1, None]

        # Edge info
        marker = Marker(showscale=True, colorscale='YIGnBu', reversescale=True,
                        color=[], size=5, line=dict(width=2))
        einfo_trace = Scatter(x=[], y=[], text=[], mode='markers', 
                             hoverinfo='text', marker=marker)
        for edge in self.edges:
            x0, y0 = pos[edge.src]
            x1, y1 = pos[edge.tgt]
            einfo_trace['x'].append((x0 + x1) / 2)
            einfo_trace['y'].append((y0 + y1) / 2)
            einfo = "ftac: {}".format(edge.ftac)
            einfo_trace['text'].append(einfo)

        # Nodes
        colorbar = dict(thickness=15, title='Node Info',
                        xanchor='left', titleside='right')
        marker = Marker(showscale=True, colorscale='YIGnBu', reversescale=True,
                        color=[], size=10, colorbar=colorbar, line=dict(width=2))
        node_trace = Scatter(x=[], y=[], text=[], mode='markers', 
                             hoverinfo='text', marker=marker)
        for node in G.nodes():
            x, y = pos[node]
            node_trace['x'].append(x)
            node_trace['y'].append(y)

        info = self.gid2info
        for node in pos.keys():
            if node in info:
                ctx, goal = info[node]
                s_ctx = "<br>".join([x + ": " + t for x, t in ctx])
                node_info = "gid: {}<br>{}<br>=====================<br>{}".format(node, s_ctx, goal)
            else:
                node_info = "gid: {}".format(node)
            node_trace['text'].append(node_info)

        # Display
        layout = Layout(title="<br>Reconstruction of {}".format(self.name),
                        titlefont=dict(size=16),
                        showlegend=False,
                        hovermode='closest',
                        margin=dict(b=20,l=5,r=5,t=40),
                        annotations=[ dict(showarrow=False,
                                           xref="paper", yref="paper",
                                           x=0.005, y=-0.002 ) ],
                        xaxis=XAxis(showgrid=False, zeroline=False, showticklabels=False),
                        yaxis=YAxis(showgrid=False, zeroline=False, showticklabels=False))
        fig = Figure(data=Data([edge_trace, node_trace, einfo_trace]), layout=layout)

        plotly.offline.init_notebook_mode(connected=True)
        plotly.offline.iplot(fig, filename='networkx')
        # py.iplot(fig, filename='networkx')