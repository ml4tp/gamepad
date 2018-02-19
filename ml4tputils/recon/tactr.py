from enum import IntEnum
import json
import networkx as nx
import numpy as np
import plotly
from plotly.graph_objs import *

from coq.ast import Name
from coq.decode import DecodeCoqExp
from coq.interp import InterpCBName, SizeCoqVal
from coq.tactics import TacKind, TACTIC_HIST
from coq.util import SizeCoqExp, HistCoqExp, TokenCoqExp, VisualizeCoqExp, COQEXP_HIST
from lib.myenv import MyEnv
from lib.myutil import dict_ls_app
from recon.parse_raw import FullTac 


"""
[Note]

Contains data-structures of tactic trees.
A reconstructed tactic tree. Contains methods for computing statistics.

Right now, we do not distinguish the same goal identifier that has
multiple tactics applied to it. For example,
14 -[tac1] -> 14 -[tac2] -> 14
is represented as
14 [tac1, tac2]
"""


# -------------------------------------------------
# Data structures

class TacStKind(IntEnum):
    LIVE = 0    # Live proof state (i.e., in-progress)
    TERM = 1    # Terminal proof state
    DEAD = 2    # Dead proof state (i.e., cannot progress)


class TacTrNode(object):
    """
    The node of a tactic tree. It contains the Coq goal identifier and the kind
    of node it is.
    """
    def __init__(self, uid, gid, kind, order=None):
        assert isinstance(kind, TacStKind)
        self.uid = uid        # Unique identifier
        self.gid = gid        # Goal identifier
        self.kind = kind      # live/dead/terminal
        self.order = order    # TODO(deh): deprecate me?
        # self._uid()           # Tactic state identifier

    # def _uid(self):
    #     if self.order is not None:
    #         x = "{}-{}".format(self.gid, self.order)
    #     else:
    #         x = str(self.gid)
    #
    #     if self.kind == TacStKind.TERM:
    #         self.uid = "T{}".format(x)
    #     elif self.kind == TacStKind.DEAD:
    #         self.uid = "E{}".format(x)
    #     else:
    #         self.uid = x

    def __eq__(self, other):
        return (isinstance(other, TacTrNode) and
                self.gid == other.gid and
                self.kind == other.kind)

    def __hash__(self):
        return self.gid

    def __str__(self):
        if self.order is not None:
            x = "{}-{}".format(self.gid, self.order)
        else:
            x = "{}(uid={})".format(self.gid, self.uid)

        if self.kind == TacStKind.TERM:
            s = "T{}".format(x)
        elif self.kind == TacStKind.DEAD:
            s = "E{}".format(x)
        else:
            s = x
        return s


class TacEdge(object):
    """
    An edge identifier uniquely identifies the edge. A single tactic
    invocation can emit multiple tactic edges, which corresponds to
    creating multiple sub-goals.
    """
    def __init__(self, eid, tid, name, tkind, ftac, src, tgt, isbod=False):
        assert isinstance(src, TacTrNode)
        assert isinstance(tgt, TacTrNode)
        assert isinstance(ftac, FullTac)

        # Internal
        self.eid = eid         # Edge identifier
        self.tid = tid         # Tactic identifier

        # Information
        self.name = name       # Name of tactic
        self.tkind = tkind     # Kind of tactic
        self.ftac = ftac       # Full tactic
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
    """
    A reconstructed tactic tree. Also contains methods for computing statistics.

    Right now, we do not distinguish the same goal identifier that has
    multiple tactics applied to it. For example,
    14 -[tac1] -> 14 -[tac2] -> 14
    is represented as
    14 [tac1, tac2]
    """
    def __init__(self, name, edges, graph, tacst_info, gid_tactic, decoder):
        assert isinstance(decoder, DecodeCoqExp)

        # Internal state
        self.name = name               # Lemma name
        self.edges = edges             # [TacEdge]
        self.graph = graph             # nx.MultDiGraph[TacStId, TacStId]
        self.tacst_info = tacst_info   # Dict[gid, (ctx, goal, ctx_e, goal_e)]
        self.gid_tactic = gid_tactic   # Dict[int, TacEdge]
        self.decoder = decoder         # Decode asts

        self.notok = []

        # Root and create flattened view
        self._root()
        assert self.root, "Reconstructed tactic tree has no root."
        self._flatten_view()

    # -------------------------------------------
    # Initialization methods

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

    def _flatten_view(self):
        self.flatview = []
        seen = set()
        for edge in self.edges:
            try:
                depth = len(nx.algorithms.shortest_path(self.graph, self.root, edge.tgt))
                if edge.tid not in seen:
                    if edge.tgt.gid in self.tacst_info:
                        pp_ctx, pp_concl, ctx, concl_idx = self.tacst_info[edge.tgt.gid]
                        self.flatview += [(depth, edge.tgt, pp_ctx, pp_concl, ctx, concl_idx, edge)]
                    elif edge.conn_to_dead() or edge.conn_to_term():
                        pp_ctx, pp_concl, ctx, concl_idx = self.tacst_info[edge.src.gid]
                        self.flatview += [(depth, edge.tgt, pp_ctx, pp_concl, ctx, concl_idx, edge)]
            except nx.exception.NetworkXNoPath:
                pass
            seen.add(edge.tid)

    # -------------------------------------------
    # Tactic tree API

    def goals(self):
        return self.graph.nodes()

    def dead_goals(self):
        acc = []
        for edge in self.edges:
            if edge.conn_to_dead():
                acc += [edge.tgt]
        return acc

    def term_goals(self):
        acc = []
        for edge in self.edges:
            if edge.conn_to_term():
                acc += [edge.tgt]
        return acc

    def tactics(self):
        acc = {}
        for edge in self.edges:
            if edge.tid in acc:
                acc[edge.tid] += [edge]
            else:
                acc[edge.tid] = [edge]
        return acc

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

    def _traverse_info(self, ordered_gids):
        acc = []
        seen = set()
        for src_gid, tgt_gid in ordered_gids:
            if src_gid.gid in self.tacst_info and src_gid.gid not in seen:
                pp_ctx, pp_goal, ctx, concl_idx = self.tacst_info[src_gid.gid]
                acc += [('OPEN', src_gid.gid, pp_ctx, pp_goal, ctx,
                         concl_idx, self.gid_tactic[src_gid])]
                seen.add(src_gid.gid)
        return acc

    def bfs_traverse(self):
        bfs = list(nx.bfs_edges(self.graph, self.root))
        return self._traverse_info(bfs)

    def dfs_traverse(self):
        dfs = list(nx.dfs_edges(self.graph, source=self.root))
        return self._traverse_info(dfs)

    def view_err_paths(self):
        acc = []
        for egid in self.dead_goals():
            try:
                acc += [nx.algorithms.shortest_path(self.graph, self.root, egid)]
            except nx.exception.NetworkXNoPath:
                self.notok += [str(egid)]
        return acc

    def view_term_paths(self):
        acc = []
        for tgid in self.term_goals():
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
                for tgid in self.term_goals():
                    try:
                        path = nx.algorithms.shortest_path(self.graph, edge.src, tgid)
                        break
                    except nx.exception.NetworkXNoPath:
                        pass
                acc += [(str(edge.ftac), len(edge.ftac.pp_tac), [str(node) for node in path])]
        return acc

    def view_tactic_hist(self, f_compress=False):
        hist = TACTIC_HIST.empty()
        for k, tacs in self.tactics().items():
            # TODO(deh): Also need atomic tactics for non-ssreflect developments
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
        for depth, _, _, _, ctx, _, _ in self.flatview:
            if ctx:
                v = len(ctx)
            else:
                v = 0
            dict_ls_app(hist, depth, v)
        return hist

    def view_depth_ctx_size(self):
        """Returns Dict[depth, [total string typ size]]"""
        hist = {}
        for depth, _, pp_ctx, _, _, _, _ in self.flatview:
            if pp_ctx:
                v = np.sum([len(ty) for _, ty in pp_ctx.items()])
            else:
                v = 0
            dict_ls_app(hist, depth, v)
        return hist

    def view_depth_goal_size(self):
        """Returns Dict[depth, [string typ size]]"""
        hist = {}
        for depth, _, _, pp_goal, _, _, _ in self.flatview:
            dict_ls_app(hist, depth, len(pp_goal))
        return hist

    def view_depth_astctx_size(self, sce_full):
        """Returns Dict[depth, [total ast typ size]]"""
        hist = {}
        for depth, _, _, _, ctx, _, _ in self.flatview:
            if ctx:
                ls = []
                for ident, typ_idx in ctx:
                    size = sce_full.decode_size(typ_idx)
                    ls += [size]
                v = np.sum(ls)
            else:
                v = 0
            dict_ls_app(hist, depth, v)
        return hist

    def view_depth_astgoal_size(self, sce_full):
        """Returns Dict[depth, [total ast typ size]]"""
        hist = {}
        for depth, _, _, _, _, concl_idx, _ in self.flatview:
            dict_ls_app(hist, depth, sce_full.decode_size(concl_idx))
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
        hce = HistCoqExp(self.decoder.decoded)
        acc = []
        seen = set()
        for _, _, _, _, ctx, concl_idx, _ in self.flatview:
            for ldecl in ctx:
                typ_idx = ldecl[1]
                if typ_idx not in seen:
                    acc += [hce.decode_hist(typ_idx)]
                    seen.add(typ_idx)
            if concl_idx not in seen:
                acc += [hce.decode_hist(concl_idx)]
                seen.add(concl_idx)

        return COQEXP_HIST.merges(acc)

    def tokenize(self):
        tce = TokenCoqExp(self.decoder.decoded)
        return tce.tokenize()

    def view_comp(self, sce_full, sce_sh):
        vals = {}
        static_full_comp = {}
        static_sh_comp = {}
        cbname_comp = {}
        scv = SizeCoqVal(self.decoder.decoded)
        for _, _, _, _, ctx, concl_idx, _ in self.flatview:
            env = MyEnv({}, [])
            for ident, typ_idx in ctx:
                if ident in vals:
                    v = vals[ident]
                else:
                    c = self.decoder.decode_exp_by_key(typ_idx)
                    cbname = InterpCBName()
                    v = cbname.interp(env, c)
                    vals[ident] = v
                    static_full_comp[ident] = sce_full.decode_size(typ_idx)
                    static_sh_comp[ident] = sce_sh.decode_size(typ_idx)
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
        sce_full = SizeCoqExp(self.decoder.decoded, f_shared=False)
        sce_sh = SizeCoqExp(self.decoder.decoded, f_shared=True)
        avg_depth_astctx_size = [(k, np.mean(v)) for k, v in
                                 self.view_depth_astctx_size(sce_full).items()]
        avg_depth_astgoal_size = [(k, np.mean(tysz)) for k, tysz in
                                  self.view_depth_astgoal_size(sce_full).items()]
        static_full_comp, static_sh_comp, cbname_comp = self.view_comp(sce_full, sce_sh)
        info = {'hist': self.view_tactic_hist(f_compress=True),
                'num_tacs': len(self.tactics()),
                'num_goals': len(self.goals()),
                'num_term': len(self.term_goals()),
                'num_err': len(self.dead_goals()),
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
        print("Goals: ", "[{}]".format(",".join([str(g) for g in self.goals()])))
        print("Tactics:", self.tactics())
        for gid in self.goals():
            s1 = ", ".join([str(x) for x in self.in_edge(gid)])
            print("In edge for {}:".format(gid), s1)
            s2 = ", ".join([str(x) for x in self.out_edges(gid)])
            print("Out edges for {}:".format(gid), s2)
        print("Terminal states:", "[{}]".format(",".join([str(g) for g in self.term_goals()])))
        print("Error states:", "[{}]".format(",".join([str(g) for g in self.dead_goals()])))
        print("Terminal path lengths:", self.view_term_paths())
        print("Error path lengths:", self.view_err_paths())
        print("<<<<<<<<<<<<<<<<<<<<")

    def check_success(self, f_verbose=False):
        ug = nx.Graph(self.graph)
        ccs = list(nx.algorithms.components.connected.connected_components(ug))
        n = len(ccs)
        if f_verbose:
            print("notok: {}, total: {}".format(len(self.notok), len(self.tactics())))
            print("# connected components: {}".format(n))
        return n == 1, n

    # def show(self):
    #     if self.graph.edges:
    #         nx.drawing.nx_pylab.draw_kamada_kawai(self.graph, with_labels=True)
    #         plt.show()

    def show_jupyter(self):
        """
        Draws the tactic tree in a Jupyter notebook. (This is required for plotly to work.)
        """
        g = self.graph
        pos = nx.drawing.layout.kamada_kawai_layout(g)

        # Edges
        edge_trace = Scatter(x=[], y=[], line=Line(width=0.5, color='#888'), hoverinfo=None, mode='lines')
        for edge in g.edges():
            x0, y0 = pos[edge[0]]
            x1, y1 = pos[edge[1]]
            edge_trace['x'] += [x0, x1, None]
            edge_trace['y'] += [y0, y1, None]

        # Edge info
        marker = Marker(showscale=True, colorscale='YIGnBu', reversescale=True, color=[], size=5, line=dict(width=2))
        einfo_trace = Scatter(x=[], y=[], text=[], mode='markers', hoverinfo='text', marker=marker)
        for edge in self.edges:
            x0, y0 = pos[edge.src]
            x1, y1 = pos[edge.tgt]
            einfo_trace['x'].append((x0 + x1) / 2)
            einfo_trace['y'].append((y0 + y1) / 2)
            einfo = "ftac: {}".format(edge.ftac)
            einfo_trace['text'].append(einfo)

        # Nodes
        marker = Marker(showscale=True, colorscale='YIGnBu', reversescale=True, color=[], size=10, line=dict(width=2))
        node_trace = Scatter(x=[], y=[], text=[], mode='markers', hoverinfo='text', marker=marker)
        for node in g.nodes():
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
                        xaxis=XAxis(showgrid=False, zeroline=False, showticklabels=False),
                        yaxis=YAxis(showgrid=False, zeroline=False, showticklabels=False))
        fig = Figure(data=Data([edge_trace, node_trace, einfo_trace]),
                     layout=layout)
        plotly.offline.init_notebook_mode(connected=True)
        plotly.offline.iplot(fig, filename='networkx')

    def visualize_exp_by_key(self, key):
        """
        Draws an ast in a Jupyter notebook. (This is required for plotly to work.)
        """
        vis = VisualizeCoqExp(self.decoder.decoded)
        vis.visualize_by_key(key)
