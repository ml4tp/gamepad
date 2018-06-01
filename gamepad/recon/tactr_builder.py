# Copyright 2018 The GamePad Authors. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# ==============================================================================

import networkx as nx

from coq.constr_decode import DecodeConstr
from coq.tactics import parse_full_tac, is_tclintros_intern, is_tclintros_all
from recon.rawtac_builder import *
from recon.tactr import TacStKind, TacTrNode, TacEdge, TacTree


"""
[Note]

Goal: [TacStDecl] -> [Tac]
"""


# -------------------------------------------------
# Tactic Tree Building

class TacTreeBuilder(object):
    """
    Build a tactic tree from a list of RawTacs.
    """
    def __init__(self, name, rawtacs, tacst_info, gid_node, gid_tactic, decoder, mid_decoder, ftac_inscope=None,
                 gs_nodeid=GenSym(), gs_edgeid=GenSym(), gs_deadid=GenSym(), gs_termid=GenSym(), f_log=False):
        for rawtac in rawtacs:
            assert isinstance(rawtac, RawTac)
        assert isinstance(decoder, DecodeConstr)

        # Internal state
        self.f_log = f_log
        self.num_tacs = 0
        self.not_ok = []

        # Lemma-specific state
        self.name = name                    # Name of the lemma
        self.tacst_info = tacst_info        # Dict[int, tacst]
        self.decoder = decoder              # Kern-level expression decoder for lemma
        self.mid_decoder = mid_decoder      # Mid-level expression decoder for lemma

        # Reconstruction state
        self.rawtacs = rawtacs              # Raw tactics to process (List[RawTac])
        self.it_rawtacs = MyIter(rawtacs)   # Iterator of raw tactics to process (Iter[RawTac])
        self.edges = []                     # Tactic edge accumulator (List[TacEdge])
        self.graph = nx.MultiDiGraph()      # TacTrNode as nodes, TacTrEdge.eid as edge
        self.ftac_inscope = ftac_inscope    # Full-tactic in scope
        self.gid_node = gid_node            # Map goal id to tactic node (Dict[int, TacTrNode])
        self.gid_tactic = gid_tactic        # Map source goal id to tactic edge (Dict[int, TacTrEdge])

        # Internal symbol generation for reconstruction
        self.gs_nodeid = gs_nodeid
        self.gs_edgeid = gs_edgeid
        self.gs_deadid = gs_deadid
        self.gs_termid = gs_termid

    # -------------------------------------------
    # Helper methods

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
        return TacTrNode(self._fresh_nodeid(), self.gs_deadid.gensym(), TacStKind.DEAD)

    def _mk_term_node(self):
        return TacTrNode(self._fresh_nodeid(), self.gs_termid.gensym(), TacStKind.TERM)

    def _mk_live_node(self, decl):
        gid = decl.hdr.gid
        if gid in self.gid_node:
            return self.gid_node[gid]
        else:
            tid = TacTrNode(self._fresh_nodeid(), gid, TacStKind.LIVE)
            self.gid_node[gid] = tid
            return tid

    def _select_ftac(self, rawtac, bf_decl):
        if rawtac.tkind == TacKind.ATOMIC:
            ftac = rawtac.ftac
        elif rawtac.name == "ml4tp.MYDONE":
            ftac = rawtac.ftac
            ftac.pp_tac = "ssrdone"
        elif self.ftac_inscope:
            ftac = self.ftac_inscope
        else:
            ftac = bf_decl.hdr.ftac

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
        else:
            bf_node = self._mk_live_node(bf_decl)
            af_node = self._mk_live_node(af_decl)
            edge = TacEdge(self._fresh_edgeid(),
                           rawtac.uid, rawtac.name, rawtac.tkind,
                           parse_full_tac(ftac), bf_node, af_node)

        # Handling self-edges by keeping track of multiple tactics
        if edge.src in self.gid_tactic:
            self.gid_tactic[edge.src] += [edge]
        else:
            self.gid_tactic[edge.src] = [edge]

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

        return edge

    def _launch_rec(self, rawtacs, ftac_inscope):
        tr_builder = TacTreeBuilder(self.name, rawtacs, self.tacst_info,
                                    self.gid_node, self.gid_tactic, self.decoder, self.mid_decoder,
                                    ftac_inscope=ftac_inscope,
                                    gs_nodeid=self.gs_nodeid,
                                    gs_edgeid=self.gs_edgeid,
                                    gs_deadid=self.gs_deadid,
                                    gs_termid=self.gs_termid)
        tr_builder.build_tacs()
        self.not_ok += tr_builder.not_ok
        self.num_tacs += tr_builder.num_tacs
        return tr_builder.edges, tr_builder.graph

    # -------------------------------------------
    # Building methods

    def build_nested(self):
        # Internal
        it_rawtacs = self.it_rawtacs
        self._mylog("@build_nested:before<{}>".format(it_rawtacs.peek()))
        self.num_tacs += 1

        tac = next(it_rawtacs)

        if tac.name == "ml4tp.MYDONE":
            edges = self._mk_edge(tac, tac.bf_decl, tac.af_decls[0])
            self._add_edges(edges)
            return
        elif tac.name == "surgery":
            edges = self._mk_edge(tac, tac.bf_decl, tac.af_decls[0])
            self._add_edges(edges)
            return

        if tac.body:
            # 1. Recursively connect up body
            if is_tclintros_all(tac):
                ftac = self.ftac_inscope
            elif (tac.name.startswith("ml4tp.TacSolveIn") or
                  tac.name.startswith("ml4tp.TacFirstIn")):
                ftac = tac.ftac
            else:
                ftac = tac.ftac
            body_edges, body_graph = self._launch_rec(tac.body, ftac)
            self._add_edges(body_edges)

            # 2. Connect body to top-level
            #    Every gid that does not have a parent is connected to the top
            root_nodes = []
            edges = []
            seen = set()
            for edge in body_edges:
                self_edges = 0
                for edge_p in body_graph.in_edges(edge.src):
                    if edge_p[0] == edge_p[1]:
                        self_edges += 1
                if body_graph.in_degree(edge.src) == self_edges and edge.src not in seen:
                    root_nodes += [edge.src]
                    seen.add(edge.src)
                    if tac.bf_decl.hdr.gid != edge.src.gid:
                        edges += [self._mk_body_edge(tac, tac.bf_decl, edge.src)]
            self._add_edges(edges)

            # 3. Handle tacticals that can try multiple possibilities
            #    with failure. Add error node to those that don't go anywhere.
            if tac.name.startswith("ml4tp.TacSolveIn") or tac.name.startswith("ml4tp.TacFirstIn"):
                for node in body_graph.nodes():
                    if node.kind != TacStKind.LIVE:
                        continue
                    self_edges = 0
                    for edge_p in body_graph.in_edges(node):
                        if edge_p[0] == edge_p[1]:
                            self_edges += 1
                    if body_graph.out_degree(node) == self_edges:
                        if node.gid == tac.af_decls[0].hdr.gid:
                            bf_node = self.gid_node[node.gid]
                            af_node = self._mk_dead_node()
                            edge = TacEdge(self._fresh_edgeid(),
                                           tac.uid, tac.name, tac.tkind,
                                           parse_full_tac(tac.ftac),
                                           bf_node, af_node)
                            # Handling self-edges by keeping track of multiple tactics
                            if edge.src in self.gid_tactic:
                                self.gid_tactic[edge.src] += [edge]
                            else:
                                self.gid_tactic[edge.src] = [edge]
                            self._add_edges([edge])

        if is_tclintros_intern(tac):
            # 4. Connect up the internals of <ssreflect_plugin::ssrtclintros@0>
            edges = []
            for af_decl in tac.af_decls:
                edges += self._mk_edge(tac, tac.bf_decl, af_decl)
            self._add_edges(edges)
        elif tac.name.startswith("ml4tp.DOEND"):
            # 5. Handle the end of a do
            edges = []
            for af_decl in tac.af_decls:
                edges += self._mk_edge(tac, tac.bf_decl, af_decl)
            self._add_edges(edges)
        elif tac.name.startswith("<ssreflect_plugin::ssrapply"):
            # 6. Apply uses the intros tactical (look at ssreflect source code)
            #    Connect if intros tactical was not used.
            if not any([tac_p.name == "ml4tp.SI" for tac_p in tac.body]):
                edges = []
                for af_decl in tac.af_decls:
                    edges += self._mk_edge(tac, tac.bf_decl, af_decl)
                self._add_edges(edges)
        elif not (tac.tkind == TacKind.NOTATION or
                  tac.tkind == TacKind.NAME or
                  tac.name.startswith("<ssreflect_plugin::ssrtclseq@0>") or
                  tac.name.startswith("<ssreflect_plugin::ssrtclintros@0>") or
                  tac.name.startswith("<ssreflect_plugin::ssrtcldo@0>") or
                  tac.name.startswith("<ssreflect_plugin::ssrtclby@0>")):
            # 7. Connect me up
            edges = []
            for af_decl in tac.af_decls:
                edges += self._mk_edge(tac, tac.bf_decl, af_decl)
            self._add_edges(edges)

    def build_tacs(self):
        """
        Top-level tactic tree building function.
        """
        # Internal
        it_rawtacs = self.it_rawtacs

        while it_rawtacs.has_next():
            _ = it_rawtacs.peek()
            self.build_nested()

    def get_tactree(self, f_verbose=False):
        """
        Get tactic tree after building it.
        """
        tactr = TacTree(self.name, self.edges, self.graph, self.tacst_info, self.gid_tactic,
                        self.decoder, self.mid_decoder)

        # Yay, dynamic-typing is great ... (Goes up in flames.)
        for _, gid, _, _, ctx, (concl_kdx, concl_mdx), tacs in tactr.bfs_traverse():
            assert isinstance(gid, int)
            assert isinstance(concl_kdx, int)
            assert isinstance(concl_mdx, int)
            for ident, ty_kdx, ty_mdx in ctx:
                assert isinstance(ident, str)
                assert isinstance(ty_kdx, int)
                assert isinstance(ty_mdx, int)
            for tac in tacs:
                assert isinstance(tac, TacEdge)

        if f_verbose:
            tactr.dump()

        return tactr
