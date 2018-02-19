import networkx as nx
import plotly
from plotly.graph_objs import *

from coq.constr import *
from lib.gensym import GenSym


"""
[Note]

Utility functions on Coq expressions.
1. Check that Coq expressions are well-formed.
2. Compute size of Coq expressions.
3. Get tokens seen in a Coq expression.
4. Visualize a Coq expression.
5. Alpha-convert
"""


# -------------------------------------------------
# Check the decoded representation

class ChkConstr(object):
    def __init__(self, decoded):
        self.decoded = decoded   # Dict[int, Exp]

    def chk_decoded(self):
        for k, c in self.decoded.items():
            self.chk_ast(c)

    def chk_ast(self, c):
        return self._chk_ast(True, c)

    def _occurs_ast(self, tag, c):
        if tag == c.tag:
            raise NameError("Recursive mention of {} in {}".format(tag, c))

    def _occurs_asts(self, tag, cs):
        for c in cs:
            self._occurs_ast(tag, c)

    def _chk_ast(self, f_chk, c):
        c_p = self.decoded[c.tag]
        if c_p.tag != c.tag:
            raise NameError("Tags {} and {} do not match {} {}".
                            format(c.tag, c_p.tag, type(c.tag), type(c_p.tag)))

        if isinstance(c, RelExp):
            pass
        elif isinstance(c, VarExp):
            pass
        elif isinstance(c, MetaExp):
            pass
        elif isinstance(c, EvarExp):
            self._occurs_asts(c.tag, c.cs)
            if f_chk:
                self._chk_asts(False, c.cs)
        elif isinstance(c, SortExp):
            pass
        elif isinstance(c, CastExp):
            self._occurs_ast(c.tag, c.c)
            self._occurs_ast(c.tag, c.ty)
            if f_chk:
                self._chk_ast(False, c.c)
                self._chk_ast(False, c.ty)
        elif isinstance(c, ProdExp):
            self._occurs_ast(c.tag, c.ty1)
            self._occurs_ast(c.tag, c.ty2)
            if f_chk:
                self._chk_ast(False, c.ty1)
                self._chk_ast(False, c.ty2)
        elif isinstance(c, LambdaExp):
            self._occurs_ast(c.tag, c.ty)
            self._occurs_ast(c.tag, c.c)
            if f_chk:
                self._chk_ast(False, c.ty)
                self._chk_ast(False, c.c)
        elif isinstance(c, LetInExp):
            self._occurs_ast(c.tag, c.c1)
            self._occurs_ast(c.tag, c.ty)
            self._occurs_ast(c.tag, c.c2)
            if f_chk:
                self._chk_ast(False, c.c1)
                self._chk_ast(False, c.ty)
                self._chk_ast(False, c.c2)
        elif isinstance(c, AppExp):
            self._occurs_ast(c.tag, c.c)
            self._occurs_asts(c.tag, c.cs)
            if f_chk:
                self._chk_ast(False, c.c)
                self._chk_asts(False, c.cs)
        elif isinstance(c, ConstExp):
            pass
        elif isinstance(c, IndExp):
            pass
        elif isinstance(c, ConstructExp):
            pass
        elif isinstance(c, CaseExp):
            self._occurs_ast(c.tag, c.ret)
            self._occurs_ast(c.tag, c.match)
            self._occurs_asts(c.tag, c.cases)
            if f_chk:
                self._chk_ast(False, c.ret)
                self._chk_ast(False, c.match)
                self._chk_asts(False, c.cases)
        elif isinstance(c, FixExp):
            self._occurs_asts(c.tag, c.tys)
            self._occurs_asts(c.tag, c.cs)
            if f_chk:
                self._chk_asts(False, c.tys)
                self._chk_asts(False, c.cs)
        elif isinstance(c, CoFixExp):
            self._occurs_asts(c.tag, c.tys)
            self._occurs_asts(c.tag, c.cs)
            if f_chk:
                self._chk_asts(False, c.tys)
                self._chk_asts(False, c.cs)
        elif isinstance(c, ProjExp):
            self._occurs_ast(c.tag, c.c)
            if f_chk:
                self._chk_ast(False, c.c)
        else:
            raise NameError("Kind {} not supported".format(c))

    def _chk_asts(self, f_chk, cs):
        for c in cs:
            self._chk_ast(False, c)


# -------------------------------------------------
# Computing sizes of coq-expressions efficiently

class SizeConstr(object):
    def __init__(self, decoded, f_shared=False):
        self.decoded = decoded
        # ChkCoqExp(decoded).chk_decoded()
        self.size_ast = {}
        self.f_shared = f_shared

    def _sizecon(self, key, size):
        self.size_ast[key] = size
        return size

    def decode_size(self, key):
        return self.size(self.decoded[key])

    def size(self, c):
        key = c.tag
        if key in self.size_ast:
            sz = self.size_ast[key]
            if self.f_shared:
                self.size_ast[key] = 0
            return sz

        if isinstance(c, RelExp):
            return self._sizecon(key, 1)
        elif isinstance(c, VarExp):
            return self._sizecon(key, 1)
        elif isinstance(c, MetaExp):
            return self._sizecon(key, 1)
        elif isinstance(c, EvarExp):
            sz = 1 + self.sizes(c.cs)
            return self._sizecon(key, sz)
        elif isinstance(c, SortExp):
            return self._sizecon(key, 1)
        elif isinstance(c, CastExp):
            sz = 1 + self.size(c.c) + self.size(c.ty)
            return self._sizecon(key, sz)
        elif isinstance(c, ProdExp):
            sz = 1 + self.size(c.ty1) + self.size(c.ty2)
            return self._sizecon(key, sz)
        elif isinstance(c, LambdaExp):
            sz = 1 + self.size(c.ty) + self.size(c.c)
            return self._sizecon(key, sz)
        elif isinstance(c, LetInExp):
            sz = 1 + self.size(c.c1) + self.size(c.ty) + self.size(c.c2)
            return self._sizecon(key, sz)
        elif isinstance(c, AppExp):
            sz = 1 + self.size(c.c) + self.sizes(c.cs)
            return self._sizecon(key, sz)
        elif isinstance(c, ConstExp):
            return self._sizecon(key, 1)
        elif isinstance(c, IndExp):
            return self._sizecon(key, 1)
        elif isinstance(c, ConstructExp):
            return self._sizecon(key, 1)
        elif isinstance(c, CaseExp):
            sz = (1 + self.size(c.ret) + self.size(c.match) +
                  self.sizes(c.cases))
            return self._sizecon(key, sz)
        elif isinstance(c, FixExp):
            sz = 1 + self.sizes(c.tys) + self.sizes(c.cs)
            return self._sizecon(key, sz)
        elif isinstance(c, CoFixExp):
            sz = 1 + self.sizes(c.tys) + self.sizes(c.cs)
            return self._sizecon(key, sz)
        elif isinstance(c, ProjExp):
            sz = 1 + self.size(c.c)
            return self._sizecon(key, sz)
        else:
            raise NameError("Kind {} not supported".format(c))

    def sizes(self, cs):
        return sum([self.size(c) for c in cs])


# -------------------------------------------------
# Computing histogram of Coq Constr

class HistConstr(object):
    def __init__(self, decoded):
        # Dict[int, Exp]
        self.decoded = decoded
        # ChkCoqExp(decoded).chk_decoded()

        # Histogram
        self.hist_ast = {}

    def _histcon(self, key, hist):
        self.hist_ast[key] = hist
        return hist

    def decode_hist(self, key):
        return self.hist(self.decoded[key])

    def hist(self, c):
        key = c.tag
        if key in self.hist_ast:
            hist = self.hist_ast[key]
            return hist

        if isinstance(c, RelExp):
            return self._histcon(key, COQEXP_HIST.delta('RelExp'))
        elif isinstance(c, VarExp):
            return self._histcon(key, COQEXP_HIST.delta('VarExp'))
        elif isinstance(c, MetaExp):
            return self._histcon(key, COQEXP_HIST.delta('MetaExp'))
        elif isinstance(c, EvarExp):
            hist = COQEXP_HIST.merge(self.hists(c.cs),
                                     COQEXP_HIST.delta('EvarExp'))
            return self._histcon(key, hist)
        elif isinstance(c, SortExp):
            return self._histcon(key, COQEXP_HIST.delta('SortExp'))
        elif isinstance(c, CastExp):
            hist = COQEXP_HIST.merges([self.hist(c.c),
                                       self.hist(c.ty),
                                       COQEXP_HIST.delta('CastExp')])
            return self._histcon(key, hist)
        elif isinstance(c, ProdExp):
            hist = COQEXP_HIST.merges([self.hist(c.ty1),
                                       self.hist(c.ty2),
                                       COQEXP_HIST.delta('ProdExp')])
            return self._histcon(key, hist)
        elif isinstance(c, LambdaExp):
            hist = COQEXP_HIST.merges([self.hist(c.ty),
                                       self.hist(c.c),
                                       COQEXP_HIST.delta('LambdaExp')])
            return self._histcon(key, hist)
        elif isinstance(c, LetInExp):
            hist = COQEXP_HIST.merges([self.hist(c.c1),
                                       self.hist(c.ty),
                                       self.hist(c.c2),
                                       COQEXP_HIST.delta('LetInExp')])
            return self._histcon(key, hist)
        elif isinstance(c, AppExp):
            hist = COQEXP_HIST.merges([self.hist(c.c),
                                       self.hists(c.cs),
                                       COQEXP_HIST.delta('AppExp')])
            return self._histcon(key, hist)
        elif isinstance(c, ConstExp):
            return self._histcon(key, COQEXP_HIST.delta('ConstExp'))
        elif isinstance(c, IndExp):
            return self._histcon(key, COQEXP_HIST.delta('IndExp'))
        elif isinstance(c, ConstructExp):
            return self._histcon(key, COQEXP_HIST.delta('ConstructExp'))
        elif isinstance(c, CaseExp):
            hist = COQEXP_HIST.merges([self.hist(c.ret),
                                       self.hist(c.match),
                                       self.hists(c.cases),
                                       COQEXP_HIST.delta('CaseExp')])
            return self._histcon(key, hist)
        elif isinstance(c, FixExp):
            hist = COQEXP_HIST.merges([self.hists(c.tys),
                                       self.hists(c.cs),
                                       COQEXP_HIST.delta('FixExp')])
            return self._histcon(key, hist)
        elif isinstance(c, CoFixExp):
            hist = COQEXP_HIST.merges([self.hists(c.tys),
                                       self.hists(c.cs),
                                       COQEXP_HIST.delta('CoFixExp')])
            return self._histcon(key, hist)
        elif isinstance(c, ProjExp):
            hist = COQEXP_HIST.merges([self.hist(c.c),
                                       COQEXP_HIST.delta('ProjExp')])
            return self._histcon(key, hist)
        else:
            raise NameError("Kind {} not supported".format(c))

    def hists(self, cs):
        return COQEXP_HIST.merges([self.hist(c) for c in cs])


# -------------------------------------------------
# Computing tokens in Coq Constr

class TokenConstr(object):
    def __init__(self, decoded):
        # Dict[int, Exp]
        self.decoded = decoded
        # ChkCoqExp(decoded).chk_decoded()

        self.seen = set()

        # Unique
        self.unique_sort = set()
        self.unique_const = set()
        self.unique_ind = set()
        self.unique_conid = set()
        self.unique_evar = set()
        self.unique_fix = set()

    def tokenize(self):
        for idx, c in self.decoded.items():
            self.token(c)
        return (self.unique_sort, self.unique_const, self.unique_ind,
                self.unique_conid, self.unique_evar, self.unique_fix)

    def _seen(self, c):
        self.seen.add(c.tag)

    def token(self, c):
        if c.tag in self.seen:
            return

        if isinstance(c, RelExp):
            return self._seen(c)
        elif isinstance(c, VarExp):
            return self._seen(c)
        elif isinstance(c, MetaExp):
            return self._seen(c)
        elif isinstance(c, EvarExp):
            self.unique_evar.add(c.exk)
            self.tokens(c.cs)
            return self._seen(c)
        elif isinstance(c, SortExp):
            self.unique_sort.add(c.sort)
            return self._seen(c)
        elif isinstance(c, CastExp):
            self.token(c.c)
            self.token(c.ty)
            return self._seen(c)
        elif isinstance(c, ProdExp):
            self.token(c.ty1)
            self.token(c.ty2)
            return self._seen(c)
        elif isinstance(c, LambdaExp):
            self.token(c.ty)
            self.token(c.c)
            return self._seen(c)
        elif isinstance(c, LetInExp):
            self.token(c.c1)
            self.token(c.ty)
            self.token(c.c2)
            return self._seen(c)
        elif isinstance(c, AppExp):
            self.token(c.c)
            self.tokens(c.cs)
            return self._seen(c)
        elif isinstance(c, ConstExp):
            self.unique_const.add(c.const)
            return self._seen(c)
        elif isinstance(c, IndExp):
            self.unique_ind.add(c.ind.mutind)
            return self._seen(c)
        elif isinstance(c, ConstructExp):
            self.unique_ind.add(c.ind.mutind)
            self.unique_conid.add((c.ind.mutind, c.conid))
            return self._seen(c)
        elif isinstance(c, CaseExp):
            self.token(c.ret)
            self.token(c.match)
            self.tokens(c.cases)
            return self._seen(c)
        elif isinstance(c, FixExp):
            for name in c.names:
                self.unique_fix.add(name)
            self.tokens(c.tys)
            self.tokens(c.cs)
            return self._seen(c)
        elif isinstance(c, CoFixExp):
            # TODO(deh): do cofix?
            self.tokens(c.tys)
            self.tokens(c.cs)
            return self._seen(c)
        elif isinstance(c, ProjExp):
            self.token(c.c)
            return self._seen(c)
        else:
            raise NameError("Kind {} not supported".format(c))

    def tokens(self, cs):
        for c in cs:
            self.token(c)


# -------------------------------------------------
# Visualize Coq expression

class VisAstNode(object):
    def __init__(self, uid, msg):
        self.uid = uid
        self.msg = msg

    def __hash__(self):
        return self.uid

    def __str__(self):
        return self.msg


class VisualizeConstr(object):
    def __init__(self, decoded):
        # Dict[int, Exp]
        self.decoded = decoded

        self.graph = None
        self.gs = None

    def visualize_by_key(self, key):
        return self.visualize(self.decoded[key])

    def visualize(self, c):
        self.graph = nx.DiGraph()
        self.gs = GenSym()
        self.mkgraph(c)
        g = self.graph
        pos = nx.drawing.layout.kamada_kawai_layout(g)

        # Edges
        edge_trace = Scatter(x=[], y=[], line=Line(width=0.5, color='#888'),
                             hoverinfo=None, mode='lines')
        for edge in g.edges():
            x0, y0 = pos[edge[0]]
            x1, y1 = pos[edge[1]]
            edge_trace['x'] += [x0, x1, None]
            edge_trace['y'] += [y0, y1, None]

        # Nodes
        marker = Marker(showscale=True, colorscale='YIGnBu', reversescale=True,
                        color=[], size=10, line=dict(width=2))
        node_trace = Scatter(x=[], y=[], text=[], mode='markers',
                             hoverinfo='text', marker=marker)
        for node in g.nodes():
            x, y = pos[node]
            node_trace['x'].append(x)
            node_trace['y'].append(y)

        # Node info
        for node in pos.keys():
            node_trace['text'].append(str(node))

        # Display
        s = str(c)
        s = s[:min(50, len(s))]
        layout = Layout(title="<br>Reconstruction of AST {} ...".format(s),
                        titlefont=dict(size=16),
                        showlegend=False,
                        hovermode='closest',
                        margin=dict(b=20, l=5, r=5, t=40),
                        xaxis=XAxis(showgrid=False, zeroline=False,
                                    showticklabels=False),
                        yaxis=YAxis(showgrid=False, zeroline=False,
                                    showticklabels=False))
        fig = Figure(data=Data([edge_trace, node_trace]),
                     layout=layout)
        plotly.offline.init_notebook_mode(connected=True)
        plotly.offline.iplot(fig, filename='coq-ast')

    def _add_node(self, node):
        node = VisAstNode(self.gs.gensym(), node)
        self.graph.add_node(node)
        return node

    def _add_edge(self, src, tgt):
        self.graph.add_edge(src, tgt)

    def _add_edges(self, src, tgts):
        for tgt in tgts:
            self.graph.add_edge(src, tgt)

    def mkgraph(self, c):
        if isinstance(c, RelExp):
            return self._add_node("Rel({})".format(c.idx))
        elif isinstance(c, VarExp):
            return self._add_node("Var({})".format(c.x))
        elif isinstance(c, MetaExp):
            return self._add_node("Meta({})".format(c.mv))
        elif isinstance(c, EvarExp):
            node = self._add_node("Evar({})".format(c.exk))
            node_cs = self.mkgraphs(c.cs)
            self._add_edges(node, node_cs)
            return node
        elif isinstance(c, SortExp):
            node = self._add_node("Sort({})".format(c.sort))
            return self._add_node(node)
        elif isinstance(c, CastExp):
            node = self._add_node("Cast({})".format(c.tag))
            node_c = self.mkgraph(c.c)
            node_ty = self.mkgraph(c.ty)
            self._add_edge(node, node_c)
            self._add_edge(node, node_ty)
            return node
        elif isinstance(c, ProdExp):
            node = self._add_node("Prod({})".format(c.tag))
            node_ty1 = self.mkgraph(c.ty1)
            node_ty2 = self.mkgraph(c.ty2)
            self._add_edge(node, node_ty1)
            self._add_edge(node, node_ty2)
            return node
        elif isinstance(c, LambdaExp):
            node = self._add_node("Lam({})".format(c.tag))
            node_ty = self.mkgraph(c.ty)
            node_c = self.mkgraph(c.c)
            self._add_edge(node, node_ty)
            self._add_edge(node, node_c)
            return node
        elif isinstance(c, LetInExp):
            node = self._add_node("Let({})".format(c.tag))
            node_c1 = self.mkgraph(c.c1)
            node_ty = self.mkgraph(c.ty)
            node_c2 = self.mkgraph(c.c2)
            self._add_edge(node, node_c1)
            self._add_edge(node, node_ty)
            self._add_edge(node, node_c2)
            return node
        elif isinstance(c, AppExp):
            node = self._add_node("App({})".format(c.tag))
            node_c = self.mkgraph(c.c)
            node_cs = self.mkgraphs(c.cs)
            self._add_edge(node, node_c)
            self._add_edges(node, node_cs)
            return node
        elif isinstance(c, ConstExp):
            return self._add_node("Const({})".format(c.const))
        elif isinstance(c, IndExp):
            return self._add_node("Ind({})".format(c.ind.mutind))
        elif isinstance(c, ConstructExp):
            return self._add_node("Ctor({}, {})".format(c.conid, c.ind.mutind))
        elif isinstance(c, CaseExp):
            node = self._add_node("Case({})".format(c.tag))
            node_ret = self.mkgraph(c.ret)
            node_match = self.mkgraph(c.match)
            node_cases = self.mkgraphs(c.cases)
            self._add_edge(node, node_ret)
            self._add_edge(node, node_match)
            self._add_edge(node, node_cases)
            return node
        elif isinstance(c, FixExp):
            node = self._add_node("Fix({})".format(c.tag))
            node_cs = self.mkgraphs(c.cs)
            node_tys = self.mkgraphs(c.tys)
            for name, node_ty, node_c in zip(c.names, node_tys, node_cs):
                node_nm = str(name)
                self._add_edge(node, node_nm)
                self._add_edge(node_nm, node_ty)
                self._add_edge(node_nm, node_c)
            return node
        elif isinstance(c, CoFixExp):
            # TODO(deh)
            node = self._add_node("CoFix({})".format(c.tag))
            return node
        elif isinstance(c, ProjExp):
            node = self._add_node("Proj({})".format(c.tag))
            node_c = self.mkgraph(c.c)
            self._add_edge(node, str(c.proj))
            self._add_edge(node, node_c)
            return node
        else:
            raise NameError("Kind {} not supported".format(c))

    def mkgraphs(self, cs):
        return [self.mkgraph(c) for c in cs]


# -------------------------------------------------
# Alpha-convert Constr

class AlphaConstr(object):
    def __init__(self, concr_ast):
        self.concr_ast = concr_ast
        self.seen = set()
        self.gs = GenSym(prefix="t")
        self.alpha_ast = {}

    def _alpha_cons(self, c):
        if c.tag in self.alpha_ast:
            return self.alpha_ast[c.tag]
        else:
            self.alpha_ast[c.tag] = c
            return c

    def _alpha_var(self, env, x):
        if x in env.env:
            return env.lookup_id(x)
        else:
            return x

    def _fresh(self, name):
        self.seen.add(name)
        while True:
            t = gs.gensym()
            if t not in self.seen:
                return t

    def alpha(self, env, c):
        if c.tag in self.alpha_ast:
            return c

        if isinstance(c, RelExp):
            return self._alpha_cons(c)
        elif isinstance(c, VarExp):
            return self._alpha_cons(VarExp(self._alpha_var(c.x)))
        elif isinstance(c, MetaExp):
            return self._alpha_cons(c)
        elif isinstance(c, EvarExp):
            cs_p = self.alphas(env, self.cs)
            return self._alpha_cons(EVarExp(c.exk, cs_p))
        elif isinstance(c, SortExp):
            return self._alpha_cons(c)
        elif isinstance(c, CastExp):
            c_p = self.alpha(env, c.c)
            ty_p = self.alpha(env, c.ty)
            return self._alpha_cons(CastExp(c_p, c.ck, ty_p))
        elif isinstance(c, ProdExp):
            ty1_p = self.alpha(env, c.ty1)
            ty2_p = self.alpha(env, c.ty2)
            return self._alpha_cons(ProdExp(self._alpha_var(c.name), ty1_p, ty2_p))
        elif isinstance(c, LambdaExp):
            name_p = self._fresh()
            ty_p = self.alpha(env, c.ty)
            c_p = self.alpha(env.insert(c.name, name_p), c.c)
            return self._alpha_cons(LambdaExp(name_p, ty_p, c_p))
        elif isinstance(c, LetInExp):
            c1_p = self.alpha(env, c.c1)
            ty_p = self.alpha(env, c.ty)
            name_p = self._fresh()
            c2_p = self.alpha(env.insert(c.name, name_p), c.c2)
            return self._alpha_cons(LetInExp(name_p, c1_p, ty_p, c2_p))
        elif isinstance(c, AppExp):
            c_p = self.alpha(env, c.c)
            cs_p = self.alphas(env, c.cs)
            return self._alpha_cons(AppExp(c_p, cs_p))
        elif isinstance(c, ConstExp):
            return self._alpha_cons(c)
        elif isinstance(c, IndExp):
            return self._alpha_cons(c)
        elif isinstance(c, ConstructExp):
            return self._alpha_cons(c)
        elif isinstance(c, CaseExp):
            ret_p = self.alpha(env, c.ret)
            match_p = self.alpha(env, c.match)
            cases_p = self.alphas(env, c.cases)
            return self._alpha_cons(CaseExp(c.ci, ret_p, match_p, cases_p))
        elif isinstance(c, FixExp):
            tys_p = self.alphas(c.tag, c.tys)
            cs_p = self.alphas(c.tag, c.cs)
            return self._alpha_cons(FixExp(c.iarr, c.idx, c.names, tys_p, cs_p))
        elif isinstance(c, CoFixExp):
            tys_p = self.alphas(c.tag, c.tys)
            cs_p = self.alphas(c.tag, c.cs)
            return self._alpha_cons(CoFixExp(c.idx, c.names, tys_p, cs_p))
        elif isinstance(c, ProjExp):
            c_p = self.alpha(env, c.c)
            return self._alpha_cons(ProjExp(c.proj, c_p))
        else:
            raise NameError("Kind {} not supported".format(c))

    def alphas(self, env, cs):
        return [self.alpha(env, c) for c in cs]
