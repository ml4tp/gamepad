import json
import matplotlib.pyplot as plt
import networkx as nx
import plotly
from plotly.graph_objs import *

from recon.parse_tacst import *
from recon.tactr import TacTree
from recon.tactics import TACTICS, Conn, Type

"""
[Note]

Goal: [TacStDecl] -> [Tac]

Works (L means long time):
BGappendix AB, C
BGsection 1, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14[L], 15, 16
PFsection 1, 2, 3, 4, 6[L], 7, 8, 9[L], 10[L], 11[L], 12, 13[L], 14[L]

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
"""


def is_err(gid):
    return isinstance(gid, str) and gid.startswith("e")


def is_term(gid):
    return isinstance(gid, str) and gid.startswith("t")


# -------------------------------------------------
# Data structures

TACST_LIVE = 0
TACST_TERM = 1
TACST_DEAD = 2


class TacStId(object):
    def __init__(self, gid, kind, order=None):
        self.gid = gid
        self.kind = kind
        self.order = order
        self._uid()

    def _uid(self):
        if self.order != None:
            x = "{}-{}".format(self.gid, self.order)
        else:
            x = str(self.gid)

        if self.kind == TACST_TERM:
            self.uid = "T{}".format(x)
        elif self.kind == TACST_DEAD:
            self.uid = "E{}".format(x)
        else:
            self.uid = "L{}".format(x)

    def __eq__(self, other):
        return (isinstance(other, TacStId) and self.gid == other.gid and
                self.kind == other.kind and self.order == other.order)

    def __hash__(self):
        return hash(self.uid)

    def __str__(self):
        return self.uid


class TacStIdEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance(obj, complex):
            return obj.uid
        # Let the base class default method raise the TypeError
        return json.JSONEncoder.default(self, obj)


class TacEdge(object):
    def __init__(self, eid, tid, name, tkind, ftac, src, tgt, isbod=False):
        """
        An edge identifier uniquely identifies the edge. A single tactic
        invocation can emit multiple tactic edges, which corresponds to
        creating multiple sub-goals.
        """
        assert isinstance(src, TacStId)
        assert isinstance(tgt, TacStId)

        # Internal
        self.eid = eid         # Edge identifier
        self.tid = tid         # Tactic identifier

        # Information
        self.name = name       # Name of tactic
        self.tkind = tkind     # Tactic kind
        self.ftac = ftac       # Full tactic
        self.src = src         # Source goal id
        self.tgt = tgt         # Target goal id
        self.isbod = isbod     # Is the connection to a body?

    def conn2err(self):
        return self.tgt.kind == TACST_DEAD
        # return is_err(self.tgt)

    def conn2term(self):
        return self.tgt.kind == TACST_TERM
        # return is_term(self.tgt)

    def unpack(self):
        return (self.eid, self.tid, self.name, str(self.tkind), self.ftac,
                self.src, self.tgt, self.isbod)

    def __str__(self):
        x = str(self.src), str(self.tgt), self.eid, self.tid, self.name, self.isbod
        return "({} -> {}, eid={}, tid={}, name={}, isbod={})".format(*x)


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
        return TacStId(self.gensym_errid.gensym(), TACST_DEAD)

    def _fresh_termid(self):
        return TacStId(self.gensym_termid.gensym(), TACST_TERM)

    def _add_edges(self, edges):
        self.edges += edges
        for edge in edges:
            self.graph.add_edge(edge.src, edge.tgt, key=edge.eid)

    def _live_tacst_id(self, decl):
        gid = decl.hdr.gid
        if gid in self.gid2tid:
            return self.gid2tid[gid]
        else:
            tid = TacStId(gid, TACST_LIVE)
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
            edge = TacEdge(self._fresh_edgeid(), tac.uid, tac.name, tac.kind,
                           ftac, bf_tid, self._fresh_termid())
        elif af_decl.hdr.mode == TOK_AFTER_ERR:
            bf_tid = self._live_tacst_id(bf_decl)
            edge = TacEdge(self._fresh_edgeid(), tac.uid, tac.name, tac.kind,
                           ftac, bf_tid, self._fresh_errid())
        # elif bf_decl.hdr.gid == af_decl.hdr.gid:
        #     # Take care of self-loops
        #     bf_tid = self._live_tacst_id(bf_decl)
        #     if bf_tid in self.tid_gensyms:
        #         gensym = self.tid_gensyms[bf_tid]
        #     else:
        #         gensym = GenSym()
        #         self.tid_gensyms[bf_tid] = gensym
        #     af_tid = TacStId(af_decl.hdr.gid, TACST_LIVE, order=gensym.gensym())
        #     self.gid2tid[af_decl.hdr.gid] = af_tid
        #     # self.tacst_info2[bf_tid] = self.tacst_info[af_tid.gid]
        #     edge = TacEdge(self._fresh_edgeid(), tac.uid, tac.name, tac.kind,
        #                    ftac, bf_tid, af_tid)
        else:
            bf_tid = self._live_tacst_id(bf_decl)
            af_tid = self._live_tacst_id(af_decl)
            edge = TacEdge(self._fresh_edgeid(), tac.uid, tac.name, tac.kind,
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

        edge = TacEdge(self._fresh_edgeid(), tac.uid, tac.name, tac.kind,
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

    def build_atomic(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_atomic:before<{}>".format(it_tacs.peek()))
        self.numtacs += 1

        tac = next(it_tacs)
        nbf = len(tac.bf_decls)
        naf = len(tac.af_decls)

        if nbf == naf:
            # 1. 1-1 connection
            edges = []
            for bf_decl, af_decl in zip(tac.bf_decls, tac.af_decls):
                edges += self._mk_edge(tac, bf_decl, af_decl)

            # Accumulate changes
            self._add_edges(edges)
        elif naf % nbf == 0:
            # Compute branching ratio
            af2bf = int(naf / nbf)

            # 1. 1-many connection
            edges = []
            for i in range(0, nbf):
                start = i * af2bf
                end = i * af2bf + af2bf
                bf_decl = tac.bf_decls[i]
                for af_decl in tac.af_decls[start:end]:
                    edges += self._mk_edge(tac, bf_decl, af_decl)

            # Accumulate changes
            self._add_edges(edges)
        else:
            self.notok += [tac]

    def build_name(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_name:before<{}>".format(it_tacs.peek()))
        self.numtacs += 1

        tac = next(it_tacs)

        if len(tac.bf_decls) == len(tac.af_decls):
            # 1-1 before/after
            # 1. connect up name tactic
            edges = []
            for bf_decl, af_decl in zip(tac.bf_decls, tac.af_decls):
                # NOTE(deh): this actually skips all name tactics
                # Connect up those name tactics with
                # different before and after goal ids
                if bf_decl.hdr.gid != af_decl.hdr.gid:
                    edges += self._mk_edge(tac, bf_decl, af_decl)

            # Accumulate changes
            self._add_edges(edges)
        else:
            self.notok += [tac]

    def build_notation(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_notation:before<{}>".format(it_tacs.peek()))
        self.numtacs += 1

        tac = next(it_tacs)

        if len(tac.bf_decls) == len(tac.bods):
            # 1-1 before/body
            for bf_decl, body in zip(tac.bf_decls, tac.bods):
                # 1. connect up body
                edges, _ = self._launch_rec(body, tac.ftac)

                # NOTE(deh): skip notation because it is a wrapper
                # TODO(deh): check for weirdness here

                # Accumulate changes
                self._add_edges(edges)
        else:
            self.notok += [tac]

    def build_ml2(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_ml2:before<{}>".format(it_tacs.peek()))
        self.numtacs += 1

        tac = it_tacs.peek()
        body = tac.bods[0]

        tacname = tac.name[:tac.name.find('>') + 1]
        if TACTICS[tacname][0] == Conn.ONE2ONE:
            next(it_tacs)

            edges = []
            if body:
                body_edges, body_graph = self._launch_rec(body, tac.ftac)
                if body_edges:
                    for bf_decl in tac.bf_decls:
                        # every gid that does not have a parent is
                        # connected to the top
                        seen = set()
                        for edge in body_edges:
                            self_edges = 0
                            for edge_p in body_graph.in_edges(edge.src):
                                if edge_p[0] == edge_p[1]:
                                    self_edges += 1
                            if body_graph.in_degree(edge.src) == self_edges and \
                               not edge.src in seen:
                                edges += [self._mk_body_edge(tac, bf_decl, edge.src)]
                                seen.add(edge.src)
                    self._add_edges(body_edges)

            for bf_decl, af_decl in zip(tac.bf_decls, tac.af_decls):
                edges += self._mk_edge(tac, bf_decl, af_decl)
            self._add_edges(edges)
        elif (TACTICS[tacname][0] == Conn.ONE2MANY and
              TACTICS[tacname][1] == Type.BASE):
            next(it_tacs)

            edges = []
            bf_decl = tac.bf_decls[0]
            for af_decl in tac.af_decls:
                edges += self._mk_edge(tac, bf_decl, af_decl)
            self._add_edges(edges)
        elif (tac.name.startswith("<ssreflect_plugin::ssrtclby@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrtcldo@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrtclseq@0>")):
            # af_decls in body match my af_decls
            self.build_ml()
        elif TACTICS[tacname][0] == Conn.WEIRD:
            self.build_ml()

    def build_ml(self):
        # Internal
        it_tacs = self.it_tacs
        self._mylog("@build_ml:before<{}>".format(it_tacs.peek()))
        self.numtacs += 1

        tac = next(it_tacs)
        body = tac.bods[0]

        tacname = tac.name[:tac.name.find('>') + 1]
        if body:
            # 1. connect up body
            body_edges, body_graph = self._launch_rec(body, tac.ftac)
            ug = nx.Graph(body_graph)
            ccs = list(nx.algorithms.components.connected.connected_components(ug))
            num_cc = len(ccs)
            
            matched = [0 for _ in tac.af_decls]
            for i, af_decl in enumerate(tac.af_decls):
                ls = [decl for rawtac in body for decl in rawtac.af_decls]
                for decl in ls:
                    if af_decl.hdr.gid == decl.hdr.gid and matched[i] == 0:
                        matched[i] = 1
                        break
            num_matched = sum(matched)
        else:
            num_cc = 0
            num_matched = 0

        self.kludge += [(tacname, len(tac.bf_decls), len(tac.af_decls), len(body), num_cc, num_matched)]

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
        elif (tac.name.startswith("<coretactics::constructor@0>") or
              tac.name.startswith("<coretactics::exists@1>") or
              tac.name.startswith("<coretactics::split@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrapply@1>") or
              tac.name.startswith("<ssreflect_plugin::ssrcase@1>")):
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
            # NOTE(deh): kludge??
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
        elif (tac.name.startswith("<g_auto::auto@0>") or
              tac.name.startswith("<g_auto::eauto@0>")):
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
        elif (tac.name.startswith("<coretactics::assumption@0>") or
              tac.name.startswith("<coretactics::clear@0>") or
              tac.name.startswith("<coretactics::clearbody@0>") or
              tac.name.startswith("<coretactics::constructor@1>") or
              tac.name.startswith("<coretactics::exact@0>") or
              tac.name.startswith("<coretactics::left@0>") or
              tac.name.startswith("<coretactics::right@0>") or
              tac.name.startswith("<coretactics::right_with@0>") or
              tac.name.startswith("<coretactics::symmetry@0>") or
              tac.name.startswith("<coretactics::reflexivity@0>") or
              tac.name.startswith("<coretactics::transitivity@0>") or
              tac.name.startswith("<extratactics::contradiction@0>") or
              tac.name.startswith("<extratactics::discriminate@0>") or
              tac.name.startswith("<g_auto::trivial@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrclear@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrcongr@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrmove@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrmove@2>") or
              tac.name.startswith("<ssreflect_plugin::ssrpose@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrpose@2>") or
              tac.name.startswith("<ssreflect_plugin::ssrset@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrwithoutloss@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrwithoutlossss@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrwlogss@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrwlogs@0>")):
            if len(tac.bf_decls) == 1 and len(body) == 0:
                edges = []
                bf_decl = tac.bf_decls[0]
                for af_decl in tac.af_decls:
                    edges += self._mk_edge(tac, bf_decl, af_decl)
                # Accumulate changes
                self._add_edges(edges)
            else:
                self.notok += [tac]
        elif (tac.name.startswith("<ssreflect_plugin::ssrapply@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrcase@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrelim@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrexact@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrexact@1>") or
              tac.name.startswith("<ssreflect_plugin::ssrhave@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrmove@1>") or
              tac.name.startswith("<ssreflect_plugin::ssrrewrite@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrsuff@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrsuffices@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrtclseq@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrwlog@0>")):
            if len(tac.bf_decls) == 1:
                edges = []
                if body:
                    # 1. connect up body
                    # body_edges, body_graph = self._launch_rec(body, tac.ftac)
                    # Accumulate changes
                    self._add_edges(body_edges)

                    # 2. connect up body to top-level
                    if body_edges:
                        for bf_decl in tac.bf_decls:
                            # every gid that does not have a parent is
                            # connected to the top
                            seen = set()
                            for edge in body_edges:
                                self_edges = 0
                                for edge_p in body_graph.in_edges(edge.src):
                                    if edge_p[0] == edge_p[1]:
                                        self_edges += 1
                                if body_graph.in_degree(edge.src) == self_edges and \
                                   not edge.src in seen:
                                    edges += [self._mk_body_edge(tac, bf_decl, edge.src)]
                                    seen.add(edge.src)

                # 3. connect me up
                if not tac.name.startswith("<ssreflect_plugin::ssrtclseq@0>"):
                    bf_decl = tac.bf_decls[0]
                    for af_decl in tac.af_decls:
                        edges += self._mk_edge(tac, bf_decl, af_decl)

                # Accumulate changes
                self._add_edges(edges)
            else:
                self.notok += [tac]
        elif (tac.name.startswith("<ssreflect_plugin::ssrtclby@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrtcldo@0>") or
              tac.name.startswith("<ssreflect_plugin::ssrtclintros@0>")):
            # NOTE(deh): ssrtclby@0 always ends in terminal?
            # 1. connect up body
            # body_edges, body_graph = self._launch_rec(body, tac.ftac)
            # Accumulate changes
            self._add_edges(body_edges)

            # 2. connect up top-level before/after
            edges = []
            has_path = [0 for _ in range(len(tac.bf_decls))]
            for i, bf_decl in enumerate(tac.bf_decls):
                for af_decl in tac.af_decls:
                    try:
                        if nx.has_path(body_graph, self.gid2tid[bf_decl.hdr.gid], self.gid2tid[af_decl.hdr.gid]):
                            edges += self._mk_edge(tac, bf_decl, af_decl)
                            has_path[i] += 1
                            break
                    except:
                        pass
                    # except nx.exception.NodeNotFound:
                    #     pass

            # 3. connect me up
            for bf_decl in tac.bf_decls:
                for af_decl in tac.af_decls:
                    edges += self._mk_edge(tac, bf_decl, af_decl)

            # Accumulate changes
            self._add_edges(edges)

            # Check for weirdness
            if any(x == 0 for x in has_path):
                self.notok += [tac]
        else:
            raise NameError("ML Tactic {} not supported.".format(tac.name))

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

    def check_success(self, f_verbose=False):
        ug = nx.Graph(self.graph)
        ccs = list(nx.algorithms.components.connected.connected_components(ug))
        n = len(ccs)
        if f_verbose:
            print("notok: {}, total: {}".format(len(self.notok), self.numtacs))
            print("# connected components: {}".format(n))
        return n == 1, n

    def get_tactree(self, f_verbose=False):
        """
        for node in self.graph.nodes:
            print("NODE", node)
        for edge in self.graph.edges:
            print("EDGE", edge[0], edge[1])
        """
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
