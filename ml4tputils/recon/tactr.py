from enum import Enum
import json
import networkx as nx
import numpy as np
import plotly
from plotly.graph_objs import *

from coq.ast import Name
from coq.interp import InterpCBName, SizeCoqVal
from coq.tactics import TacKind, TACTIC_HIST
from coq.util import ChkCoqExp, SizeCoqExp, HistCoqExp, COQEXP_HIST
from lib.myenv import MyEnv
from lib.myutil import dict_ls_app


"""
[Note]

A reconstructed tactic tree. Contains methods for computing statistics.

Right now, we do not distinguish the same goal identifier that has
multiple tactics applied to it. For example,
14 -[tac1] -> 14 -[tac2] -> 14
is represented as
14 [tac1, tac2]
"""


# -------------------------------------------------
# Data structures

class TacStKind(Enum):
    LIVE = 0
    TERM = 1
    DEAD = 2


class TacTrNode(object):
    def __init__(self, gid, kind, order=None):
        assert isinstance(kind, TacStKind)
        self.gid = gid        # Goal identifier
        self.kind = kind      # live/dead/terminal
        self.order = order    # TODO(deh): use to disambiguate self-edges?
        self._uid()           # Tactic state identifier

    def _uid(self):
        if self.order != None:
            x = "{}-{}".format(self.gid, self.order)
        else:
            x = str(self.gid)

        if self.kind == TacStKind.TERM:
            self.uid = "T{}".format(x)
        elif self.kind == TacStKind.DEAD:
            self.uid = "E{}".format(x)
        else:
            self.uid = x

    def __eq__(self, other):
        return (isinstance(other, TacTrNode) and self.gid == other.gid and
                self.kind == other.kind and self.order == other.order)

    def __hash__(self):
        return self.gid
        # return hash(self.uid)

    def __str__(self):
        return self.uid


class TacEdge(object):
    def __init__(self, eid, tid, name, tkind, ftac, src, tgt, isbod=False):
        """
        An edge identifier uniquely identifies the edge. A single tactic
        invocation can emit multiple tactic edges, which corresponds to
        creating multiple sub-goals.
        """
        assert isinstance(src, TacTrNode)
        assert isinstance(tgt, TacTrNode)

        # Internal
        self.eid = eid         # Edge identifier
        self.tid = tid         # Tactic identifier

        # Information
        self.name = name       # Name of tactic
        self.tkind = tkind     # Kind of tactic
        self.ftac = ftac       # Full tactic (contains arguments)
        self.src = src         # Source tactic state
        self.tgt = tgt         # Target tactic state
        self.isbod = isbod     # Is the connection to a body?

    def conn_to_dead(self):
        return self.tgt.kind == TacStKind.DEAD

    def conn_to_live(self):
        return self.tgt.kind == TacStKind.LIVE

    def conn_to_term(self):
        return self.tgt.kind == TacStKind.TERM

    def __str__(self):
        x = str(self.src), str(self.tgt), self.eid, self.tid, self.name, self.isbod
        return "({} -> {}, eid={}, tid={}, name={}, isbod={})".format(*x)


# -------------------------------------------------
# Tactic Tree

class TacTree(object):
    def __init__(self, name, edges, graph, tacst_info, gid_tactic, decoder):
        # Input
        self.name = name               # Lemma name
        self.edges = edges             # [TacEdge]
        self.graph = graph             # nx.MultDiGraph[TacStId, TacStId]
        self.tacst_info = tacst_info   # Dict[gid, (ctx, goal, ctx_e, goal_e)]
        self.gid_tactic = gid_tactic   # Dict[int, TacEdge]
        self.decoder = decoder         # Decode asts
        self.chk = ChkCoqExp(decoder.decoded)
        self.chk.chk_decoded()
        self.sce_full = SizeCoqExp(decoder.decoded, f_shared=False)
        self.sce_sh = SizeCoqExp(decoder.decoded, f_shared=True)
        self.hce = HistCoqExp(decoder.decoded)

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
            if edge.conn_to_dead():
                self.err_goals += [edge.tgt]

    def _term_goals(self):
        self.term_goals = []
        for edge in self.edges:
            if edge.conn_to_term():
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
                    if edge.tgt.gid in self.tacst_info:
                        ctx, goal, ctx_e, goal_e = self.tacst_info[edge.tgt.gid]
                        self.flatview += [(depth, edge.tgt, ctx, goal, ctx_e, goal_e, edge)]
                    elif edge.conn_to_dead() or edge.conn_to_term():
                        ctx, goal, ctx_e, goal_e = self.tacst_info[edge.src.gid]
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

    def unique_sort(self):
        return self.hce.unique_sort

    def unique_const(self):
        return self.hce.unique_const

    def unique_ind(self):
        return self.hce.unique_ind

    def unique_conid(self):
        return self.hce.unique_conid

    def unique_evar(self):
        return self.hce.unique_evar

    def unique_fix(self):
        return self.hce.unique_fix

    def _traverse_info(self, ordered_gids):
        acc = []
        for src_gid, tgt_gid in ordered_gids:
            if src_gid.gid in self.tacst_info:
                pp_ctx, pp_goal, ctx_ids, goal_idx = self.tacst_info[src_gid.gid]
                acc += [('OPEN', src_gid.gid, pp_ctx, pp_goal, ctx_ids,
                         goal_idx, self.gid_tactic[src_gid])]
            # elif (tgt_gid.kind == TacStKind.DEAD or
            #       tgt_gid.kind == TacStKind.TERM):
            #     acc += [('STOP', tgt_gid, self.gid_tactic[src_gid.gid])]
        return acc

    def bfs_traverse(self):
        bfs = list(nx.bfs_edges(self.graph, self.root))
        return self._traverse_info(bfs)

    def dfs_traverse(self):
        dfs = list(nx.dfs_edges(self.graph, source=self.root))
        return self._traverse_info(dfs)

    def view_err_paths(self):
        acc = []
        for egid in self.err_goals:
            try:
                acc += [nx.algorithms.shortest_path(self.graph, self.root, egid)]
            except nx.exception.NetworkXNoPath:
                self.notok += [str(egid)]
        return acc

    def view_term_paths(self):
        acc = []
        for tgid in self.term_goals:
            try:
                acc += [nx.algorithms.shortest_path(self.graph, self.root, tgid)]
            except nx.exception.NetworkXNoPath:
                self.notok += [str(tgid)]
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
                acc += [(edge.ftac, len(edge.ftac), [str(node) for node in path])]
        return acc

    def view_tactic_hist(self, f_compress=False):
        hist = TACTIC_HIST.empty()
        for k, tacs in self.tactics.items():
            tac = tacs[0]
            if tac.tkind == TacKind.ML:
                tac_name = tac.name.split()[0]
                hist = TACTIC_HIST.inc_insert(hist, tac_name, 1)
        if f_compress:
            return [v for _, v in TACTIC_HIST.view(hist)]
        else:
            return TACTIC_HIST.view(hist)

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
                    # print(ctx_e, self.decoder.ctx_typs)
                    key = self.decoder.ctx_typs[ident]
                    size = self.sce_full.decode_size(key)
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
            dict_ls_app(hist, depth, self.sce_full.decode_size(goal_e))
        return hist

    def view_depth_tactic_hist(self):
        max_depth = max([depth for depth, _, _, _, _, _, _ in self.flatview])
        hist = {}
        for depth in range(max_depth + 1):
            hist[depth] = TACTIC_HIST.empty()

        for depth, gid, ctx, goal, ctx_e, goal_e, tac in self.flatview:
            TACTIC_HIST.inc_insert(hist[depth], tac.name, 1)
        return hist

    def hist_coqexp(self):
        hists = [self.hce.decode_hist(edx) for ident, edx in
                 self.decoder.ctx_typs.items()]

        acc = []
        seen = set()
        for depth, gid, ctx, goal, ctx_e, goal_e, tac in self.flatview:
            if goal_e not in seen:
                acc += [self.hce.decode_hist(goal_e)]
                seen.add(goal_e)
        return COQEXP_HIST.merges(hists + acc)

    def view_comp(self):
        vals = {}
        static_full_comp = {}
        static_sh_comp = {}
        cbname_comp = {}
        scv = SizeCoqVal(self.decoder.decoded)
        for depth, gid, ctx, goal, ctx_e, goal_e, tac in self.flatview:
            env = MyEnv()
            for ident in ctx_e:
                if ident in vals:
                    v = vals[ident]
                else:
                    edx = self.decoder.ctx_typs[ident]
                    c = self.decoder.decode_exp_by_key(edx)
                    cbname = InterpCBName()
                    v = cbname.interp(env, c)
                    vals[ident] = v
                    edx = self.decoder.ctx_typs[ident]
                    static_full_comp[ident] = self.sce_full.decode_size(edx)
                    static_sh_comp[ident] = self.sce_sh.decode_size(edx)
                    cbname_comp[ident] = scv.size(v)
                env = env.extend(Name(ident), v)
        return static_full_comp, static_sh_comp, cbname_comp

    def stats(self):
        term_path_lens = [len(path) for path in self.view_term_paths()]
        err_path_lens = [len(path) for path in self.view_err_paths()]
        avg_depth_ctx_items = [(k, np.mean(v)) for k, v in
                               self.view_depth_ctx_items().items()]
        avg_depth_ctx_size = [(k, np.mean(v)) for k, v in
                              self.view_depth_ctx_size().items()]
        avg_depth_goal_size = [(k, np.mean(tysz)) for k, tysz in
                               self.view_depth_goal_size().items()]
        avg_depth_astctx_size = [(k, np.mean(v)) for k, v in
                                 self.view_depth_astctx_size().items()]
        avg_depth_astgoal_size = [(k, np.mean(tysz)) for k, tysz in
                                  self.view_depth_astgoal_size().items()]
        static_full_comp, static_sh_comp, cbname_comp = self.view_comp()
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
                'static_full_comp': [v for _, v in static_full_comp.items()],
                'static_sh_comp': [v for _, v in static_sh_comp.items()],
                'cbname_comp': [v for _, v in cbname_comp.items()],
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
        print("Goals: ", "[{}]".format(",".join([str(g) for g in self.goals])))
        print("Tactics:", self.tactics)
        for gid in self.goals:
            s1 = ", ".join([str(x) for x in self.in_edge(gid)])
            print("In edge for {}:".format(gid), s1)
            s2 = ", ".join([str(x) for x in self.out_edges(gid)])
            print("Out edges for {}:".format(gid), s2)
        print("Terminal states:", "[{}]".format(",".join([str(g) for g in self.term_goals])))
        print("Error states:", "[{}]".format(",".join([str(g) for g in self.err_goals])))
        print("Terminal path lengths:", self.view_term_paths())
        print("Error path lengths:", self.view_err_paths())
        print("<<<<<<<<<<<<<<<<<<<<")

    def check_success(self, f_verbose=False):
        ug = nx.Graph(self.graph)
        ccs = list(nx.algorithms.components.connected.connected_components(ug))
        n = len(ccs)
        if f_verbose:
            print("notok: {}, total: {}".format(len(self.notok), self.numtacs))
            print("# connected components: {}".format(n))
        return n == 1, n

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
