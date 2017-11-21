import json
import networkx as nx
import numpy as np

from coq.ast import *
from coq.util import ChkCoqExp, SizeCoqExp, HistCoqExp, COQEXP_HIST
from lib.myutil import dict_ls_app

"""
[Note]

A reconstructed tactic tree. Contains methods for computing statistics.
"""


# -------------------------------------------------
# Tactics

TACTICS = ["<coretactics::intro@0>",
           "<coretactics::assumption@0>",
           "<coretactics::clear@0>",
           "<coretactics::clearbody@0>",
           "<coretactics::constructor@0>",
           "<coretactics::constructor@1>",
           "<coretactics::exact@0>",
           "<coretactics::exists@1>",
           "<coretactics::left@0>",
           "<coretactics::right@0>",
           "<coretactics::split@0>",
           "<coretactics::symmetry@0>",
           "<coretactics::transitivity@0>",
           "<extratactics::contradiction@0>",
           "<extratactics::discriminate@0>",
           "<g_auto::auto@0>",
           "<g_auto::eauto@0>",
           "<g_auto::trivial@0>",
           "<ssreflect_plugin::ssrapply@0>",
           "<ssreflect_plugin::ssrapply@1>",
           "<ssreflect_plugin::ssrcase@0>",
           "<ssreflect_plugin::ssrcase@1>",
           "<ssreflect_plugin::ssrclear@0>",
           "<ssreflect_plugin::ssrcongr@0>",
           "<ssreflect_plugin::ssrelim@0>",
           "<ssreflect_plugin::ssrexact@0>",
           "<ssreflect_plugin::ssrexact@1>",
           "<ssreflect_plugin::ssrhave@0>",
           "<ssreflect_plugin::ssrmove@0>",
           "<ssreflect_plugin::ssrmove@1>",
           "<ssreflect_plugin::ssrmove@2>",
           "<ssreflect_plugin::ssrpose@2>",
           "<ssreflect_plugin::ssrrewrite@0>",
           "<ssreflect_plugin::ssrset@0>",
           "<ssreflect_plugin::ssrsuff@0>",
           "<ssreflect_plugin::ssrsuffices@0>",
           "<ssreflect_plugin::ssrtclby@0>",
           "<ssreflect_plugin::ssrtcldo@0>",
           "<ssreflect_plugin::ssrtclintros@0>",
           "<ssreflect_plugin::ssrtclseq@0>",
           "<ssreflect_plugin::ssrwithoutloss@0>",
           "<ssreflect_plugin::ssrwithoutlossss@0>",
           "<ssreflect_plugin::ssrwlog@0>",
           "<ssreflect_plugin::ssrwlogss@0>",
           "<ssreflect_plugin::ssrwlogs@0>"
           ]


TACTIC_IDS = [i for i, _ in enumerate(TACTICS)]


TACTIC_ID_MAP = {}
for i, tactic in enumerate(TACTICS):
    TACTIC_ID_MAP[tactic] = i


ID_TACTIC_MAP = {}
for i, tactic in enumerate(TACTICS):
    ID_TACTIC_MAP[i] = tactic


# -------------------------------------------------
# Tactic Tree

class TacTree(object):
    def __init__(self, name, edges, graph, tacst_info, decoder):
        # Input
        self.name = name               # Lemma name
        self.edges = edges             # [TacEdge]
        self.graph = graph             # nx.MultDiGraph[Int, Int]
        self.tacst_info = tacst_info   # Dict[gid, (ctx, goal, ctx_e, goal_e)]
        self.decoder = decoder         # Decode asts
        ChkCoqExp(decoder.concr_ast).chk_concr_ast()
        self.dsize = SizeCoqExp(decoder.concr_ast)
        self.dhist = HistCoqExp(decoder.concr_ast)

        self.notok = []

        # Root, error/terminal states, and create flattened view
        self._root()
        assert self.root
        self._goals()
        self._term_goals()
        self._err_goals()
        self._tactics()
        self._flatten_view()

    def _root(self):
        self.root = None
        for node in self.graph.nodes():
            self_edges = 0
            for edge in self.graph.in_edges(node):
                if edge[0] == edge[1]:
                    self_edges += 1
            if self.graph.in_degree(node) == self_edges:
                self.root = node
                break

    def _goals(self):
        self.goals = self.graph.nodes()

    def _err_goals(self):
        self.err_goals = []
        for edge in self.edges:
            if edge.conn2err():
                self.err_goals += [edge.tgt]

    def _term_goals(self):
        self.term_goals = []
        for edge in self.edges:
            if edge.conn2term():
                self.term_goals += [edge.tgt]

    def _tactics(self):
        self.tactics = {}
        for edge in self.edges:
            if edge.tid in self.tactics:
                self.tactics[edge.tid] += [edge]
            else:
                self.tactics[edge.tid] = [edge]

    def _flatten_view(self):
        self.flatview = []
        seen = set()
        for edge in self.edges:
            try:
                depth = len(nx.algorithms.shortest_path(self.graph, self.root, edge.tgt))
                if edge.tid not in seen:
                    if edge.tgt in self.tacst_info:
                        ctx, goal, ctx_e, goal_e = self.tacst_info[edge.tgt]
                        self.flatview += [(depth, edge.tgt, ctx, goal, ctx_e, goal_e, edge)]
                    elif edge.conn2err() or edge.conn2term():
                        ctx, goal, ctx_e, goal_e = self.tacst_info[edge.src]
                        self.flatview += [(depth, edge.tgt, ctx, goal, ctx_e, goal_e, edge)]
            except nx.exception.NetworkXNoPath:
                pass
            seen.add(edge.tid)

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

    def view_err_paths(self):
        acc = []
        for egid in self.err_goals:
            try:
                acc += [nx.algorithms.shortest_path(self.graph, self.root, egid)]
            except nx.exception.NetworkXNoPath:
                self.notok += [egid]
        return acc

    def view_term_paths(self):
        acc = []
        for tgid in self.term_goals:
            try:
                acc += [nx.algorithms.shortest_path(self.graph, self.root, tgid)]
            except nx.exception.NetworkXNoPath:
                self.notok += [tgid]
        return acc

    def view_have_info(self):
        acc = []
        for edge in self.edges:
            if edge.name.startswith("<ssreflect_plugin::ssrhave@0>") and \
               edge.isbod:
                path = []
                for tgid in self.term_goals:
                    try:
                        path = nx.algorithms.shortest_path(self.graph, edge.src, tgid)
                        break
                    except nx.exception.NetworkXNoPath:
                        pass
                acc += [(edge.ftac, len(edge.ftac), path)]
        return acc

    def view_tactic_hist(self, f_compress=False):
        hist = [0 for _ in TACTIC_IDS]
        for k, tacs in self.tactics.items():
            tac = tacs[0]
            for idx, tactic in enumerate(TACTICS):
                if tac.name.startswith(tactic):
                    hist[idx] += 1
                    break

        if f_compress:
            return hist
        else:
            return [(tactic, cnt) for tactic, cnt in zip(TACTICS, hist)]

    def view_depth_ctx_items(self):
        hist = {}
        for depth, gid, ctx, goal, ctx_e, goal_e, tac in self.flatview:
            if ctx:
                v = len(ctx_e)
            else:
                v = 0
            dict_ls_app(hist, depth, v)
        return hist

    def view_depth_ctx_size(self):
        """Returns Dict[depth, [total string typ size]]"""
        hist = {}
        for depth, gid, ctx, goal, ctx_e, goal_e, tac in self.flatview:
            if ctx:
                v = np.sum([len(ty) for _, ty in ctx.items()])
            else:
                v = 0
            dict_ls_app(hist, depth, v)
        return hist

    def view_depth_goal_size(self):
        """Returns Dict[depth, [string typ size]]"""
        hist = {}
        for depth, gid, ctx, goal, ctx_e, goal_e, tac in self.flatview:
            dict_ls_app(hist, depth, len(goal))
        return hist

    def view_depth_astctx_size(self):
        """Returns Dict[depth, [total ast typ size]]"""
        hist = {}
        for depth, gid, ctx, goal, ctx_e, goal_e, tac in self.flatview:
            if ctx_e:
                ls = []
                for ident in ctx_e:
                    key = self.decoder.typs_table[ident]
                    size = self.dsize.decode_size(key)
                    ls += [size]
                v = np.sum(ls)
            else:
                v = 0
            dict_ls_app(hist, depth, v)
        return hist

    def view_depth_astgoal_size(self):
        """Returns Dict[depth, [total ast typ size]]"""
        hist = {}
        for depth, gid, ctx, goal, ctx_e, goal_e, tac in self.flatview:
            dict_ls_app(hist, depth, self.dsize.decode_size(goal_e))
        return hist

    def view_depth_tactic_hist(self):
        max_depth = max([depth for depth, _, _, _, _, _, _ in self.flatview])
        hist = {}
        for depth in range(max_depth + 1):
            hist[depth] = [0 for _ in TACTIC_IDS]

        for depth, gid, ctx, goal, ctx_e, goal_e, tac in self.flatview:
            for idx, tactic in enumerate(TACTICS):
                if tac.name.startswith(tactic):
                    hist[depth][idx] += 1
                    break
        return hist

    def hist_coqexp(self):
        hists = [self.dhist.decode_hist(edx) for ident, edx in self.decoder.typs_table.items()]
        return COQEXP_HIST.merges(hists)

    def stats(self):
        term_path_lens = [len(path) for path in self.view_term_paths()]
        err_path_lens = [len(path) for path in self.view_err_paths()]
        avg_depth_ctx_items = [(k, np.mean(v)) for k, v in self.view_depth_ctx_items().items()]
        avg_depth_ctx_size = [(k, np.mean(v)) for k, v in self.view_depth_ctx_size().items()]
        avg_depth_goal_size = [(k, np.mean(tysz)) for k, tysz in self.view_depth_goal_size().items()]
        avg_depth_astctx_size = [(k, np.mean(v)) for k, v in self.view_depth_astctx_size().items()]
        avg_depth_astgoal_size = [(k, np.mean(tysz)) for k, tysz in self.view_depth_astgoal_size().items()]
        info = {'hist': self.view_tactic_hist(f_compress=True),
                'num_tacs': len(self.tactics),
                'num_goals': len(self.goals),
                'num_term': len(self.term_goals),
                'num_err': len(self.err_goals),
                'term_path_lens': term_path_lens,
                'err_path_lens': err_path_lens,
                'have_info': self.view_have_info(),
                'avg_depth_ctx_items': avg_depth_ctx_items,
                'avg_depth_ctx_size': avg_depth_ctx_size,
                'avg_depth_goal_size': avg_depth_goal_size,
                'avg_depth_astctx_size': avg_depth_astctx_size,
                'avg_depth_astgoal_size': avg_depth_astgoal_size,
                'hist_coqexp': self.hist_coqexp(),
                'notok': self.notok}
        return info

    def log_stats(self, h_file):
        info = self.stats()
        msg = json.dumps({"lemma": self.name, "info": info})
        h_file.write(msg)
        h_file.write("\n")
        return info

    def dump(self):
        print(">>>>>>>>>>>>>>>>>>>>")
        print("Root:", self.root)
        print("Goals:", self.goals)
        print("Tactics:", self.tactics)
        for gid in self.goals:
            s1 = ", ".join([str(x) for x in self.in_edge(gid)])
            print("In edge for {}:".format(gid), s1)
            s2 = ", ".join([str(x) for x in self.out_edges(gid)])
            print("Out edges for {}:".format(gid), s2)
        print("Terminal states:", self.term_goals)
        print("Error states:", self.err_goals)
        print("Terminal path lengths:", self.view_term_paths())
        print("Error path lengths:", self.view_err_paths())
        print("<<<<<<<<<<<<<<<<<<<<")
