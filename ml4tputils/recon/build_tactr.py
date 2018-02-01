import json
import matplotlib.pyplot as plt
import networkx as nx
import plotly
from plotly.graph_objs import *

from coq.decode import DecodeCoqExp
from recon.parse_raw import FullTac 
from recon.parse_rawtac import *
from recon.tactr import TacStKind, TacTrNode, TacEdge, TacTree, parse_full_tac

"""
[Note]

Goal: [TacStDecl] -> [Tac]

Observations/Issues: 
1. how to scope done (need to instrument ssreflect)
2. If the before state is solved, then we ignore the tactic.
3. What about self-edges? (solved, keep track of them)
4. If tcldo is dead, then don't do body? (solved)
5. why are we duplicating some edges? (Is this still true?)
"""


# -------------------------------------------------
# Tactic Tree Building

class TacTreeBuilder(object):
    def __init__(self, name, rawtacs, tacst_info, gid_tactic, decoder,
                 ftac_inscope=None,
                 gs_nodeid=GenSym(), gs_edgeid=GenSym(),
                 gs_deadid=GenSym(), gs_termid=GenSym(),
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

    def _select_ftac(self, rawtac, bf_decl):
        if rawtac.tkind == TacKind.ATOMIC:
            ftac = rawtac.ftac
            # print("    ATOMIC", ftac)
        elif rawtac.name == "ml4tp.MYDONE":
            ftac = rawtac.ftac
            ftac.pp_tac = "ssrdone"
        elif self.ftac_inscope:
            ftac = self.ftac_inscope
            # print("    SCOPE", ftac)
        else:
            ftac = bf_decl.hdr.ftac
            # print("    BFDECL", ftac)

        return ftac

    def _mk_edge(self, rawtac, bf_decl, af_decl):
        # Skip adding tactics which begin in solved states
        if bf_decl.hdr.gid == GID_SOLVED:
            return []

        ftac = self._select_ftac(rawtac, bf_decl)

        if af_decl.hdr.gid == GID_SOLVED:
            bf_node = self._mk_live_node(bf_decl)
            edge = TacEdge(self._fresh_edgeid(),
                           rawtac.uid, rawtac.name, rawtac.tkind,
                           parse_full_tac(ftac), bf_node, self._mk_term_node())
        elif af_decl.hdr.mode == TOK_DEAD:
            bf_node = self._mk_live_node(bf_decl)
            edge = TacEdge(self._fresh_edgeid(),
                           rawtac.uid, rawtac.name, rawtac.tkind,
                           parse_full_tac(ftac), bf_node, self._mk_dead_node())
        # Note(deh): handling self-edges by keeping track of multiple tactics
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
                           parse_full_tac(ftac), bf_node, af_node)

        # Note(deh): handling self-edges by keeping track of multiple tactics
        if edge.src in self.gid_tactic:
            self.gid_tactic[edge.src] += [edge]
        else:
            self.gid_tactic[edge.src] = [edge]

        # if edge.name.startswith("<ssreflect_plugin::ssrtcldo@0>"):
        #     print("HERE", rawtac)
        #     print("ftac_inscope", self.ftac_inscope)
        #     assert False

        return [edge]

    def _mk_body_edge(self, rawtac, bf_decl, af_node):
        ftac = self._select_ftac(rawtac, bf_decl)

        edge = TacEdge(self._fresh_edgeid(),
                       rawtac.uid, rawtac.name, rawtac.tkind,
                       parse_full_tac(ftac), self._mk_live_node(bf_decl), af_node, True)

        if edge.src in self.gid_tactic:
            self.gid_tactic[edge.src] += [edge]
        else:
            self.gid_tactic[edge.src] = [edge]

        # if edge.name.startswith("<ssreflect_plugin::ssrtcldo@0>"):
        #     print("HERE", rawtac.pp())
        #     print("ftac_inscope", self.ftac_inscope)
        #     assert False

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

    def _is_tclintros_intern(self, tac):
        # return (tac.name == "ml4tp.SIE" or tac.name == "ml4tp.SI" or
        #         tac.name == "ml4tp.SC" or tac.name == "ml4tp.SPC" or
        #         tac.name == "ml4tp.SPS" or tac.name == "ml4tp.SPC2")
        return (tac.name == "ml4tp.SI" or   # intro part of tclintros
                tac.name == "ml4tp.SC" or   # clear part of tclintros
                tac.name == "ml4tp.SPS" or  # simpl pattern
                tac.name == "ml4tp.SPC2")   # case pattern

    def _is_tclintros_all(self, tac):
        return (tac.name == "ml4tp.SIO" or  # original tactic wrapped by tclintros
                self._is_tclintros_intern(tac))

    def build_nested(self):
        # Internal
        it_rawtacs = self.it_rawtacs
        self._mylog("@build_nested:before<{}>".format(it_rawtacs.peek()))
        self.numtacs += 1

        tac = next(it_rawtacs)

        if tac.name == "ml4tp.MYDONE":
            edges = self._mk_edge(tac, tac.bf_decl, tac.af_decls[0])
            self._add_edges(edges)
            return

        # print("DOING", tac.name, tac.ftac, "INSCOPE", self.ftac_inscope)
        if tac.body:
            # 1. Recursively connect up body
            if self._is_tclintros_all(tac):
                ftac = self.ftac_inscope
                # print("CHOOSING SCOPE", ftac)
            elif (tac.name.startswith("ml4tp.TacSolveIn") or
                  tac.name.startswith("ml4tp.TacFirstIn")):
                ftac = tac.ftac
            else:
                ftac = tac.ftac
                # print("CHOOSING CURR", ftac)
            body_edges, body_graph = self._launch_rec(tac.body, ftac)
            self._add_edges(body_edges)

            # 2. Connect body to top-level
            # Every gid that does not have a parent is connected to the top
            root_nodes = []
            edges = []
            seen = set()
            for edge in body_edges:
                self_edges = 0
                for edge_p in body_graph.in_edges(edge.src):
                    if edge_p[0] == edge_p[1]:
                        self_edges += 1
                if (body_graph.in_degree(edge.src) == self_edges and
                    edge.src not in seen):
                    root_nodes += [edge.src]
                    seen.add(edge.src)
                    if tac.bf_decl.hdr.gid != edge.src.gid:
                        # print("ADDING BODY EDGE", tac.name, tac.tkind, tac.bf_decl.hdr.gid, edge.src.gid, edge.src.kind)
                        edges += [self._mk_body_edge(tac, tac.bf_decl, edge.src)]
            self._add_edges(edges)

            # 3. Handle tacticals that can try multiple possibilities
            #    with failure. Add error node to those that don't go anywhere.
            if (tac.name.startswith("ml4tp.TacSolveIn") or
                tac.name.startswith("ml4tp.TacFirstIn")):
                for node in body_graph.nodes():
                    if node.kind != TacStKind.LIVE:
                        continue
                    self_edges = 0
                    for edge_p in body_graph.in_edges(node):
                        if edge_p[0] == edge_p[1]:
                            self_edges += 1
                    if body_graph.out_degree(node) == self_edges:
                        if node.gid == tac.af_decls[0].hdr.gid:
                            bf_node = self.gid2node[node.gid]
                            af_node = self._mk_dead_node()
                            edge = TacEdge(self._fresh_edgeid(),
                                           tac.uid, tac.name, tac.tkind,
                                           parse_full_tac(tac.ftac),
                                           bf_node, af_node)
                            # Note(deh): handling self-edges by keeping track of multiple tactics
                            if edge.src in self.gid_tactic:
                                self.gid_tactic[edge.src] += [edge]
                            else:
                                self.gid_tactic[edge.src] = [edge]
                            self._add_edges([edge])

        if self._is_tclintros_intern(tac):
            # 4. Connect up the internals of <ssreflect_plugin::ssrtclintros@0>
            edges = []
            for af_decl in tac.af_decls:
                # print("ADDING INTRO EDGE", tac.name, tac.tkind, tac.bf_decl.hdr.gid, af_decl.hdr.gid, af_decl.hdr.mode)
                edges += self._mk_edge(tac, tac.bf_decl, af_decl)
            self._add_edges(edges)
        elif tac.name.startswith("ml4tp.DOEND"):
            edges = []
            for af_decl in tac.af_decls:
                # print("ADDING INTRO EDGE", tac.name, tac.tkind, tac.bf_decl.hdr.gid, af_decl.hdr.gid, af_decl.hdr.mode)
                edges += self._mk_edge(tac, tac.bf_decl, af_decl)
            self._add_edges(edges)
        elif tac.name.startswith("<ssreflect_plugin::ssrapply"):
            # 5. Apply uses the intros tactical (look at ssreflect source code)
            #.   Connect if intros tactical was not used.
            if not any([tac_p.name == "ml4tp.SI" for tac_p in tac.body]):
                edges = []
                for af_decl in tac.af_decls:
                    # print("ADDING APPLY EDGE", tac.name, tac.tkind, tac.bf_decl.hdr.gid, af_decl.hdr.gid, af_decl.hdr.mode)
                    edges += self._mk_edge(tac, tac.bf_decl, af_decl)
                self._add_edges(edges)
        elif not (tac.tkind == TacKind.NOTATION or
                  tac.tkind == TacKind.NAME or
                  tac.name.startswith("<ssreflect_plugin::ssrtclseq@0>") or
                  tac.name.startswith("<ssreflect_plugin::ssrtclintros@0>") or
                  tac.name.startswith("<ssreflect_plugin::ssrtcldo@0>") or
                  tac.name.startswith("<ssreflect_plugin::ssrtclby@0>")):
            # 6. Connect me up
            edges = []
            for af_decl in tac.af_decls:
                # print("ADDING EDGE", tac.name, tac.tkind, tac.bf_decl.hdr.gid, af_decl.hdr.gid, af_decl.hdr.mode)
                edges += self._mk_edge(tac, tac.bf_decl, af_decl)
            self._add_edges(edges)

    def build_tacs(self):
        # Internal
        it_rawtacs = self.it_rawtacs

        while it_rawtacs.has_next():
            tac = it_rawtacs.peek()
            self.build_nested()

    def get_tactree(self, f_verbose=False):
        tactr = TacTree(self.name, self.edges, self.graph,
                        self.tacst_info, self.gid_tactic, self.decoder)

        for _, gid, _, _, ctx, concl_idx, tacs in tactr.bfs_traverse():
            assert isinstance(gid, int)
            for ident, idx in ctx:
                assert isinstance(ident, str)
                assert isinstance(idx, int)
            assert isinstance(concl_idx, int)
            for tac in tacs:
                assert isinstance(tac, TacEdge)

        # tactr.bfs_traverse()
        # for edge in tactr.edges:
        #     print("HERE1", edge.ftac)
        #     print("HERE2", edge.ftac.lids)
        #     print("HERE3", edge.ftac.gids)
            # if edge.name.startswith("<ssreflect_plugin::ssrtcldo@0>"):
            #     print(edge)
            #     raise NameError("WTF")
        if f_verbose:
            tactr.dump()
        return tactr
