import json
import matplotlib.pyplot as plt
import networkx as nx
import plotly
from plotly.graph_objs import *

from coq.decode import DecodeCoqExp
from recon.parse_rawtac import *
from recon.tactr import TacStKind, TacTrNode, TacEdge, TacTree

"""
[Note]

Goal: [TacStDecl] -> [Tac]

Observations/Issues: 
1. open problem actually ... how to scope done
   (in coq, more generally LTAC name calls)
2. If the before state is solved, then we ignore the tactic.
3. What about self-edges?
4. If tcldo is dead, then don't do body? (solved)
5. why are we duplicating some edges? (Is this still true?)
"""


# -------------------------------------------------
# Tactic Tree Building

class TacTreeBuilder(object):
    def __init__(self, name, rawtacs, tacst_info, gid_tactic, decoder,
                 ftac_inscope=None, gs_nodeid=GenSym(),
                 gs_edgeid=GenSym(), gs_deadid=GenSym(), gs_termid=GenSym(),
                 gid2node={}, tid_gensyms={},
                 f_log=False):
        for rawtac in rawtacs:
            assert isinstance(rawtac, RawTac)
        assert isinstance(decoder, DecodeCoqExp)

        # Internal state
        self.f_log = f_log
        self.numtacs = 0
        self.notok = []

        # Lemma-specific state
        self.name = name                    # Name of the lemma
        self.tacst_info = tacst_info        # Dict[int, tacst]
        self.decoder = decoder              # Expression decoder for lemma

        # Reconstruction state
        self.rawtacs = rawtacs              # [RawTac]
        self.it_rawtacs = MyIter(rawtacs)   # Iter<RawTac>
        self.edges = []                     # [TacEdge]
        # graph with goal ids as nodes, tactics as edges
        self.graph = nx.MultiDiGraph()
        self.ftac_inscope = ftac_inscope    # full-tactic in scope?
        self.gid_tactic = gid_tactic        # Dict[int, TacEdge]

        # Internal symbol generation for reconstruction
        self.gs_nodeid = gs_nodeid
        self.gs_edgeid = gs_edgeid
        self.gs_deadid = gs_deadid
        self.gs_termid = gs_termid

        # Mapping goal ids to tactic state ids
        self.gid2node = gid2node
        self.tid_gensyms = tid_gensyms

    def _mylog(self, msg, f_log=False):
        if f_log or self.f_log:
            print(msg)

    def _fresh_nodeid(self):
        return self.gs_nodeid.gensym()

    def _fresh_edgeid(self):
        return self.gs_edgeid.gensym()

    def _add_edges(self, edges):
        self.edges += edges
        for edge in edges:
            self.graph.add_edge(edge.src, edge.tgt, key=edge.eid)

    def _mk_dead_node(self):
        return TacTrNode(self._fresh_nodeid(), self.gs_deadid.gensym(),
                         TacStKind.DEAD)

    def _mk_term_node(self):
        return TacTrNode(self._fresh_nodeid(), self.gs_termid.gensym(),
                         TacStKind.TERM)

    def _mk_live_node(self, decl):
        gid = decl.hdr.gid
        if gid in self.gid2node:
            return self.gid2node[gid]
        else:
            tid = TacTrNode(self._fresh_nodeid(), gid, TacStKind.LIVE)
            self.gid2node[gid] = tid
            return tid

    def _mk_edge(self, rawtac, bf_decl, af_decl):
        # Skip adding tactics which begin in solved states
        if bf_decl.hdr.gid == GID_SOLVED:
            return []

        if self.ftac_inscope:
            ftac = self.ftac_inscope
        else:
            # TODO(deh): fix Coq dump to handle old printing of full-tactic
            ftac = bf_decl.hdr.tac

        if af_decl.hdr.gid == GID_SOLVED:
            bf_node = self._mk_live_node(bf_decl)
            edge = TacEdge(self._fresh_edgeid(),
                           rawtac.uid, rawtac.name, rawtac.tkind,
                           ftac, bf_node, self._mk_term_node())
        elif af_decl.hdr.mode == TOK_DEAD:
            bf_node = self._mk_live_node(bf_decl)
            edge = TacEdge(self._fresh_edgeid(),
                           rawtac.uid, rawtac.name, rawtac.tkind,
                           ftac, bf_node, self._mk_dead_node())
        # TODO(deh): how do we handle self-edges?
        # elif bf_decl.hdr.gid == af_decl.hdr.gid:
        #     # Take care of self-loops
        #     bf_tid = self._mk_live_node(bf_decl)
        #     if bf_tid in self.tid_gensyms:
        #         gensym = self.tid_gensyms[bf_tid]
        #     else:
        #         gensym = GenSym()
        #         self.tid_gensyms[bf_tid] = gensym
        #     af_tid = TacTrNode(af_decl.hdr.gid, TACST_LIVE, order=gensym.gensym())
        #     self.gid2node[af_decl.hdr.gid] = af_tid
        #     # self.tacst_info2[bf_tid] = self.tacst_info[af_tid.gid]
        #     edge = TacEdge(self._fresh_edgeid(), tac.uid, tac.name, tac.tkind,
        #                    ftac, bf_tid, af_tid)
        else:
            bf_node = self._mk_live_node(bf_decl)
            af_node = self._mk_live_node(af_decl)
            edge = TacEdge(self._fresh_edgeid(),
                           rawtac.uid, rawtac.name, rawtac.tkind,
                           ftac, bf_node, af_node)

        # TODO(deh): is this correct? should be node to edge?
        if edge.src in self.gid_tactic:
            self.gid_tactic[edge.src] += [edge]
        else:
            self.gid_tactic[edge.src] = [edge]

        return [edge]

    def _mk_body_edge(self, rawtac, bf_decl, af_node):
        if self.ftac_inscope:
            ftac = self.ftac_inscope
        else:
            # TODO(deh): fix Coq dump to handle old printing of full-tactic
            ftac = bf_decl.hdr.tac

        edge = TacEdge(self._fresh_edgeid(),
                       rawtac.uid, rawtac.name, rawtac.tkind,
                       ftac, self._mk_live_node(bf_decl), af_node, True)
        return edge

    def _launch_rec(self, rawtacs, ftac_inscope):
        tr_builder = TacTreeBuilder(self.name, rawtacs, self.tacst_info,
                                    self.gid_tactic, self.decoder,
                                    ftac_inscope=ftac_inscope,
                                    gs_nodeid=self.gs_nodeid,
                                    gs_edgeid=self.gs_edgeid,
                                    gs_deadid=self.gs_deadid,
                                    gs_termid=self.gs_termid,
                                    gid2node=self.gid2node,
                                    tid_gensyms=self.tid_gensyms)
        tr_builder.build_tacs()
        self.notok += tr_builder.notok
        self.numtacs += tr_builder.numtacs
        return tr_builder.edges, tr_builder.graph

    def build_name(self):
        # Internal
        it_rawtacs = self.it_rawtacs
        self._mylog("@build_name:before<{}>".format(it_rawtacs.peek()))
        self.numtacs += 1

        # Skip Name
        tac = next(it_rawtacs)

    def build_nested(self):
        # Internal
        it_rawtacs = self.it_rawtacs
        self._mylog("@build_nested:before<{}>".format(it_rawtacs.peek()))
        self.numtacs += 1

        tac = next(it_rawtacs)

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
            # TODO(deh): what other ones to avoid?
            # 3. Connect me up
            edges = []
            for af_decl in tac.af_decls:
                edges += self._mk_edge(tac, tac.bf_decl, af_decl)
            self._add_edges(edges)

    def build_tacs(self):
        # Internal
        it_rawtacs = self.it_rawtacs

        while it_rawtacs.has_next():
            tac = it_rawtacs.peek()
            if tac.tkind == TacKind.NAME:
                self.build_name()
            else:
                self.build_nested()

    def get_tactree(self, f_verbose=False):
        tactr = TacTree(self.name, self.edges, self.graph,
                        self.tacst_info, self.gid_tactic, self.decoder)

        if f_verbose:
            tactr.dump()
        return tactr
