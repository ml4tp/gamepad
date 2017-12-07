import json
import matplotlib.pyplot as plt
import networkx as nx
import plotly
from plotly.graph_objs import *

from coq.decode import DecodeCoqExp
from recon.parse_rawtac import *
from recon.tactr import TacStKind, TacTrNode, TacEdge, TacTree
from recon.tactics import TACTICS, Conn, Type

"""
[Note]

Goal: [TacStDecl] -> [Tac]

NOTE(deh): is this still true?
Pop from empty list:
BGsection 3, 4
PFsection 5

BGsection 4:
rank2_coprime_comm_cprod

NOTE(deh):
1. open problem actually ... how to scope done
   (in coq, more generally LTAC name calls)
2. If the before state is solved, then we ignore the tactic.
3. What about self-edges?
4. If tcldo is dead, then don't do body?
5. why are we duplicating some edges?

name calls have no body, bf/af is 1-1
for atom/ml/notation, should be able to connect bf/af using goal id

"""


# -------------------------------------------------
# Tactic Tree Building

class TacTreeBuilder(object):
    def __init__(self, name, tacs, tacst_info, gid_tactic, decoder, kludge,
                 ftac_inscope=None, gensym_edgeid=GenSym(),
                 gensym_errid=GenSym(),
                 gensym_termid=GenSym(),
                 gid2tid={}, tid_gensyms={},
                 f_log=False):
        for tac in tacs:
            assert isinstance(tac, RawTac)
        assert isinstance(decoder, DecodeCoqExp)

        # Internal state
        self.f_log = f_log
        self.numtacs = 0
        self.notok = []

        # Lemma-specific state
        self.name = name            # Name of the lemma
        self.decoder = decoder      # Expression decoder for lemma

        # Reconstruction state
        self.tacs = tacs
        self.it_tacs = MyIter(tacs)
        self.edges = []                     # [TacEdge]
        # graph with goal ids as nodes, tactics as edges
        self.graph = nx.MultiDiGraph()
        self.tacst_info = tacst_info        # Dict[int, tacst]
        self.ftac_inscope = ftac_inscope    # full-tactic in scope?
        self.gid_tactic = gid_tactic        # Dict[int, TacEdge]

        # Internal symbol generation for reconstruction
        self.gensym_edgeid = gensym_edgeid
        self.gensym_errid = gensym_errid
        self.gensym_termid = gensym_termid

        # Mapping goal ids to tactic state ids
        self.gid2tid = gid2tid
        self.tid_gensyms = tid_gensyms

        self.kludge = kludge

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            print(msg)

    def _fresh_edgeid(self):
        return self.gensym_edgeid.gensym()

    def _fresh_errid(self):
        return TacTrNode(self.gensym_errid.gensym(), TacStKind.DEAD)

    def _fresh_termid(self):
        return TacTrNode(self.gensym_termid.gensym(), TacStKind.TERM)

    def _add_edges(self, edges):
        self.edges += edges
        for edge in edges:
            self.graph.add_edge(edge.src, edge.tgt, key=edge.eid)

    def _live_tacst_id(self, decl):
        gid = decl.hdr.gid
        if gid in self.gid2tid:
            return self.gid2tid[gid]
        else:
            tid = TacTrNode(gid, TacStKind.LIVE)
            self.gid2tid[gid] = tid
            return tid

    def _mk_edge(self, tac, bf_decl, af_decl):
        # Skip adding tactics which begin in solved states
        if bf_decl.hdr.gid == GID_SOLVED:
            return []

        if self.ftac_inscope:
            ftac = self.ftac_inscope
        else:
            ftac = bf_decl.hdr.ftac

        if af_decl.hdr.gid == GID_SOLVED:
            bf_tid = self._live_tacst_id(bf_decl)
            edge = TacEdge(self._fresh_edgeid(), tac.tid, tac.name, tac.tkind,
                           ftac, bf_tid, self._fresh_termid())
        elif af_decl.hdr.mode == TOK_DEAD:
            bf_tid = self._live_tacst_id(bf_decl)
            edge = TacEdge(self._fresh_edgeid(), tac.tid, tac.name, tac.tkind,
                           ftac, bf_tid, self._fresh_errid())
        # elif bf_decl.hdr.gid == af_decl.hdr.gid:
        #     # Take care of self-loops
        #     bf_tid = self._live_tacst_id(bf_decl)
        #     if bf_tid in self.tid_gensyms:
        #         gensym = self.tid_gensyms[bf_tid]
        #     else:
        #         gensym = GenSym()
        #         self.tid_gensyms[bf_tid] = gensym
        #     af_tid = TacTrNode(af_decl.hdr.gid, TACST_LIVE, order=gensym.gensym())
        #     self.gid2tid[af_decl.hdr.gid] = af_tid
        #     # self.tacst_info2[bf_tid] = self.tacst_info[af_tid.gid]
        #     edge = TacEdge(self._fresh_edgeid(), tac.tid, tac.name, tac.tkind,
        #                    ftac, bf_tid, af_tid)
        else:
            bf_tid = self._live_tacst_id(bf_decl)
            af_tid = self._live_tacst_id(af_decl)
            edge = TacEdge(self._fresh_edgeid(), tac.tid, tac.name, tac.tkind,
                           ftac, bf_tid, af_tid)

        if edge.src in self.gid_tactic:
            self.gid_tactic[edge.src] += [edge]
        else:
            self.gid_tactic[edge.src] = [edge]

        #print("ADDING EDGE", edge)
        return [edge]

    def _mk_body_edge(self, tac, bf_decl, af_tid):
        if self.ftac_inscope:
            ftac = self.ftac_inscope
        else:
            ftac = bf_decl.hdr.ftac

        edge = TacEdge(self._fresh_edgeid(), tac.tid, tac.name, tac.tkind,
                       ftac, self._live_tacst_id(bf_decl), af_tid, True)
        return edge

    def _launch_rec(self, tacs, ftac_inscope):
        tr_builder = TacTreeBuilder(self.name, tacs, self.tacst_info,
                                    self.gid_tactic, self.decoder, self.kludge,
                                    ftac_inscope=ftac_inscope,
                                    gensym_edgeid=self.gensym_edgeid,
                                    gensym_errid=self.gensym_errid,
                                    gensym_termid=self.gensym_termid,
                                    gid2tid=self.gid2tid,
                                    tid_gensyms=self.tid_gensyms)
        tr_builder.build_tacs()
        self.notok += tr_builder.notok
        self.numtacs += tr_builder.numtacs
        return tr_builder.edges, tr_builder.graph

    def build_name(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_name:before<{}>".format(it_tacs.peek()))
        self.numtacs += 1

        # Skip Name
        tac = next(it_tacs)

    def build_foo(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_foo:before<{}>".format(it_tacs.peek()))
        self.numtacs += 1

        tac = next(it_tacs)

        if tac.body:
            # 1. Recursively connect up body
            body_edges, body_graph = self._launch_rec(tac.body, tac.ftac)
            self._add_edges(body_edges)

            # 2. Connect body to top-level
            # Every gid that does not have a parent is connected to the top
            edges = []
            seen = set()
            for edge in body_edges:
                self_edges = 0
                for edge_p in body_graph.in_edges(edge.src):
                    if edge_p[0] == edge_p[1]:
                        self_edges += 1
                if (body_graph.in_degree(edge.src) == self_edges and
                    not edge.src in seen):
                    edges += [self._mk_body_edge(tac, tac.bf_decl, edge.src)]
                    seen.add(edge.src)
            self._add_edges(edges)

        if not tac.name.startswith("<ssreflect_plugin::ssrtclseq@0>"):
            # 3. Connect me up
            edges = []
            for af_decl in tac.af_decls:
                edges += self._mk_edge(tac, tac.bf_decl, af_decl)
            self._add_edges(edges)

    def build_tacs(self):
        # Internal
        it_tacs = self.it_tacs

        while it_tacs.has_next():
            tac = it_tacs.peek()
            if tac.tkind == TacKind.NAME:
                self.build_name()
            else:
                self.build_foo()

    def check_success(self, f_verbose=False):
        ug = nx.Graph(self.graph)
        ccs = list(nx.algorithms.components.connected.connected_components(ug))
        n = len(ccs)
        if f_verbose:
            print("notok: {}, total: {}".format(len(self.notok), self.numtacs))
            print("# connected components: {}".format(n))
        return n == 1, n

    def get_tactree(self, f_verbose=False):
        # print("NODES", self.graph.nodes)
        # print("EDGES", self.graph.edges)

        tactr = TacTree(self.name, self.edges, self.graph,
                        self.tacst_info, self.gid_tactic, self.decoder)

        if f_verbose:
            tactr.dump()

        return tactr

    def show(self):
        if self.graph.edges:
            nx.drawing.nx_pylab.draw_kamada_kawai(self.graph, with_labels=True)
            plt.show()

    def show_jupyter(self):
        G = self.graph
        pos = nx.drawing.layout.kamada_kawai_layout(G)

        # Edges
        edge_trace = Scatter(x=[], y=[], line=Line(width=0.5, color='#888'),
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
        marker = Marker(showscale=True, colorscale='YIGnBu', reversescale=True,
                        color=[], size=10, line=dict(width=2))
        node_trace = Scatter(x=[], y=[], text=[], mode='markers',
                             hoverinfo='text', marker=marker)
        for node in G.nodes():
            x, y = pos[node]
            node_trace['x'].append(x)
            node_trace['y'].append(y)

        # Node info
        for node in pos.keys():
            if node.gid in self.tacst_info:
                ctx, goal, ctx_e, goal_e = self.tacst_info[node.gid]
                s_ctx = "<br>".join([z + ": " + t for z, t in ctx.items()])
                node_info = "gid: {}<br>{}<br>=====================<br>{}".format(node, s_ctx, goal)
            else:
                node_info = "gid: {}".format(node)
            node_trace['text'].append(node_info)

        # Display
        layout = Layout(title="<br>Reconstruction of {}".format(self.name),
                        titlefont=dict(size=16),
                        showlegend=False,
                        hovermode='closest',
                        margin=dict(b=20, l=5, r=5, t=40),
                        xaxis=XAxis(showgrid=False, zeroline=False,
                                    showticklabels=False),
                        yaxis=YAxis(showgrid=False, zeroline=False,
                                    showticklabels=False))
        fig = Figure(data=Data([edge_trace, node_trace, einfo_trace]),
                     layout=layout)
        plotly.offline.init_notebook_mode(connected=True)
        plotly.offline.iplot(fig, filename='networkx')
