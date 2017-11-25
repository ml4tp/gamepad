from coq.ast import *
from lib.myhist import MyHist
from lib.myutil import merge_hist, merge_hists

"""
[Note]

Utility functions on Coq expressions
"""


# -------------------------------------------------
# Check the decoded representation 

class ChkCoqExp(object):
    def __init__(self, concr_ast):
        self.concr_ast = concr_ast
        
        # Compute number of times an expression is used
        self.sharing = {}

        # Unique
        self.unique_const = set()
        self.unique_ind = set()
        self.unique_conid = set()

    def chk_concr_ast(self):
        for k, c in self.concr_ast.items():
            self.chk_ast(c)

    def chk_ast(self, c):
        return self._chk_ast(True, c)

    def _occurs_ast(self, tag, c):
        if tag == c.tag:
            raise NameError("Recursive mention of {} in {}".format(tag, c))

    def _occurs_asts(self, tag, cs):
        for c in cs:
            self._occurs_ast(tag, c)

    def _sharing(self, c):
        if c.tag in self.sharing:
            self.sharing[c.tag] += 1
        else:
            self.sharing[c.tag] = 1

    def _chk_ast(self, f_chk, c):
        c_p = self.concr_ast[c.tag]
        self._sharing(c)
        if c_p.tag != c.tag:
            raise NameError("Tags {} and {} do not match {} {}".format(c.tag, c_p.tag, type(c.tag), type(c_p.tag)))

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
            self.unique_const.add(c.const)
        elif isinstance(c, IndExp):
            self.unique_ind.add(c.ind.mutind)
        elif isinstance(c, ConstructExp):
            self.unique_conid.add((c.ind.mutind, c.conid))
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

class SizeCoqExp(object):
    def __init__(self, concr_ast):
        self.concr_ast = concr_ast
        ChkCoqExp(concr_ast).chk_concr_ast()
        self.size_ast = {}

    def _sizecon(self, key, size):
        self.size_ast[key] = size
        return size

    def decode_size(self, key):
        return self.size(self.concr_ast[key])

    def size(self, c):
        key = c.tag
        if key in self.size_ast:
            sz = self.size_ast[key]
            # self.size_ast[key] = 0
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
            # TODO(deh): HMM?
            return self._sizecon(key, 1) 
        elif isinstance(c, IndExp):
            # TODO(deh): HMM?
            return self._sizecon(key, 1)
        elif isinstance(c, ConstructExp):
            # TODO(deh): HMM?
            return self._sizecon(key, 1)
        elif isinstance(c, CaseExp):
            sz = 1 + self.size(c.ret) + self.size(c.match) + self.sizes(c.cases)
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
# Computing histogram of coq-expressions efficiently

COQEXP = ['RelExp', 'VarExp', 'MetaExp', 'EvarExp', 'SortExp', 'CastExp',
          'ProdExp', 'LambdaExp', 'LetInExp', 'AppExp', 'ConstExp',
          'IndExp', 'ConstructExp', 'CaseExp', 'FixExp', 'CoFixExp', 'ProjExp']


COQEXP_HIST = MyHist(COQEXP)


class HistCoqExp(object):
    def __init__(self, concr_ast):
        self.concr_ast = concr_ast
        ChkCoqExp(concr_ast).chk_concr_ast()
        self.hist_ast = {}

    def _histcon(self, key, hist):
        self.hist_ast[key] = hist
        return hist

    def decode_hist(self, key):
        return self.hist(self.concr_ast[key])

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
            hist = self.hists(c.cs)
            return self._histcon(key, COQEXP_HIST.merge(hist, COQEXP_HIST.delta('EvarExp')))
        elif isinstance(c, SortExp):
            return self._histcon(key, COQEXP_HIST.delta('SortExp'))
        elif isinstance(c, CastExp):
            hist = COQEXP_HIST.merge(self.hist(c.c), self.hist(c.ty))
            return self._histcon(key, COQEXP_HIST.merge(hist, COQEXP_HIST.delta('CastExp')))
        elif isinstance(c, ProdExp):
            hist = COQEXP_HIST.merge(self.hist(c.ty1), self.hist(c.ty2))
            return self._histcon(key, COQEXP_HIST.merge(hist, COQEXP_HIST.delta('ProdExp')))
        elif isinstance(c, LambdaExp):
            hist = COQEXP_HIST.merge(self.hist(c.ty), self.hist(c.c))
            return self._histcon(key, COQEXP_HIST.merge(hist, COQEXP_HIST.delta('LambdaExp')))
        elif isinstance(c, LetInExp):
            hist = COQEXP_HIST.merges([self.hist(c.c1), self.hist(c.ty), self.hist(c.c2)])
            return self._histcon(key, COQEXP_HIST.merge(hist, COQEXP_HIST.delta('LetInExp')))
        elif isinstance(c, AppExp):
            hist = COQEXP_HIST.merge(self.hist(c.c), self.hists(c.cs))
            return self._histcon(key, COQEXP_HIST.merge(hist, COQEXP_HIST.delta('AppExp')))
        elif isinstance(c, ConstExp):
            return self._histcon(key, COQEXP_HIST.delta('ConstExp')) 
        elif isinstance(c, IndExp):
            return self._histcon(key, COQEXP_HIST.delta('IndExp'))
        elif isinstance(c, ConstructExp):
            return self._histcon(key, COQEXP_HIST.delta('ConstructExp'))
        elif isinstance(c, CaseExp):
            hist = COQEXP_HIST.merges([self.hist(c.ret), self.hist(c.match), self.hists(c.cases)])
            return self._histcon(key, COQEXP_HIST.merge(hist, COQEXP_HIST.delta('CaseExp')))
        elif isinstance(c, FixExp):
            hist = COQEXP_HIST.merge(self.hists(c.tys), self.hists(c.cs))
            return self._histcon(key, COQEXP_HIST.merge(hist, COQEXP_HIST.delta('FixExp')))
        elif isinstance(c, CoFixExp):
            hist = COQEXP_HIST.merge(self.hists(c.tys), self.hists(c.cs))
            return self._histcon(key, COQEXP_HIST.merge(hist, COQEXP_HIST.delta('CoFixExp')))
        elif isinstance(c, ProjExp):
            hist = self.hist(c.c)
            return self._histcon(key, COQEXP_HIST.merge(hist, COQEXP_HIST.delta('ProjExp')))
        else:
            raise NameError("Kind {} not supported".format(c))

    def hists(self, cs):
        return COQEXP_HIST.merges([self.hist(c) for c in cs])


# -------------------------------------------------
# Compute sharing in Coq expression

"""
1. unique const exp's (size of the embedding matrix)
2. A(e, e) sharing (for each ast, computation as distribution, unshared, vs size)
3. let x = 5 in let x = x + x in x (show that this thing blows the fuck up)
"""

class ShareCoqExp(object):
    def __init__(self, concr_ast):
        self.concr_ast = concr_ast
        ChkCoqExp(concr_ast).chk_concr_ast()
        self.seen = set()
        
        self.unique_const = set()
        self.unique_sort = set()
        self.unique_prod = set()
        self.usage_ast = {}

    def decode_share(self, key):
        return self.share(self.concr_ast[key])

    def share(self, env, c):
        key = c.tag
        if key in self.seen:
            return

        self.seen.add(c.tag)
        if isinstance(c, RelExp):
            env.lookup_rel(c.idx)
        elif isinstance(c, VarExp):
            env.lookup_id(c.x)
        elif isinstance(c, MetaExp):
            pass
        elif isinstance(c, EvarExp):
            pass
        elif isinstance(c, SortExp):
            self.unique_sort.add(c.sort)
        elif isinstance(c, CastExp):
            self.share(env, c.c)
            self.share(env, c.ty)
        elif isinstance(c, ProdExp):
            self.unique_prod.add(c.name)
            self.share(env, c.ty1)
            self.share(env, c.ty2)
        elif isinstance(c, LambdaExp):
            c.name
            self.share(env, c.ty)
            self.share(env, c.c)
        elif isinstance(c, LetInExp):
            self.share(env, c.c1)
            self.share(env, c.ty)
            self.share(env.extend(c.name, ), c.c2)
        elif isinstance(c, AppExp):
            self.share(c.c)
            self.shares(c.cs)
        elif isinstance(c, ConstExp):
            self.unique_const.add(c.const)

            return self._sharecon(key, 1) 
        elif isinstance(c, IndExp):
            return self._sharecon(key, 1)
        elif isinstance(c, ConstructExp):
            return self._sharecon(key, 1)
        elif isinstance(c, CaseExp):
            sz = 1 + self.share(c.ret) + self.share(c.match) + self.shares(c.cases)
            return self._sharecon(key, sz)
        elif isinstance(c, FixExp):
            sz = 1 + self.shares(c.tys) + self.shares(c.cs)
            return self._sharecon(key, sz)
        elif isinstance(c, CoFixExp):
            sz = 1 + self.shares(c.tys) + self.shares(c.cs)
            return self._sharecon(key, sz)
        elif isinstance(c, ProjExp):
            sz = 1 + self.share(c.c)
            return self._sharecon(key, sz)
        else:
            raise NameError("Kind {} not supported".format(c))

    def shares(self, cs):
        return sum([self.share(c) for c in cs])


"""
class UniqueCoqExp(object):
    def __init__(self, concr_ast):
        self.concr_ast = concr_ast
        ChkCoqExp(concr_ast).chk_concr_ast()
        self.seen = set()
        
        self.unique_rel = set()
        self.unique_var = set()

    def decode_unique(self, key):
        return self.unique(self.concr_ast[key])

    def unique(self, c):
        key = c.tag
        if key in self.seen:
            return

        self.seen.add(c.tag)
        if isinstance(c, RelExp):
            if c.idx in self.unique_rel:
                self.unique_rel.add(c.idx)
        elif isinstance(c, VarExp):
            if c.x in self.unique_var:
                self.unique_var.add(c.x)
        elif isinstance(c, MetaExp):
            if c.mv in self.unique_mv:
                self.unique_mv.add(c.mv)
        elif isinstance(c, EvarExp):
            if c.exk in self.unique_ev:
                self.unique_ev.add(c.exk)
        elif isinstance(c, SortExp):
            if c.sort in self.unique_sort:
                self.unique_sort.add(c.sort)
        elif isinstance(c, CastExp):
            self.unique(c.c)
            self.unique(c.ty)
        elif isinstance(c, ProdExp):
            self.unique(c.ty1)
            self.unique(c.ty2)
        elif isinstance(c, LambdaExp):
            c.name
            self.unique(c.ty)
            self.unique(c.c)
        elif isinstance(c, LetInExp):
            self.unique(c.c1)
            self.unique(c.ty)
            self.unique(c.c2)
        elif isinstance(c, AppExp):
            self.unique(c.c)
            self.uniques(c.cs)
        elif isinstance(c, ConstExp):
            # TODO(deh): HMM?
            self.unique
            return self._uniquecon(key, 1) 
        elif isinstance(c, IndExp):
            # TODO(deh): HMM?
            return self._uniquecon(key, 1)
        elif isinstance(c, ConstructExp):
            # TODO(deh): HMM?
            return self._uniquecon(key, 1)
        elif isinstance(c, CaseExp):
            sz = 1 + self.unique(c.ret) + self.unique(c.match) + self.uniques(c.cases)
            return self._uniquecon(key, sz)
        elif isinstance(c, FixExp):
            sz = 1 + self.uniques(c.tys) + self.uniques(c.cs)
            return self._uniquecon(key, sz)
        elif isinstance(c, CoFixExp):
            sz = 1 + self.uniques(c.tys) + self.uniques(c.cs)
            return self._uniquecon(key, sz)
        elif isinstance(c, ProjExp):
            sz = 1 + self.unique(c.c)
            return self._uniquecon(key, sz)
        else:
            raise NameError("Kind {} not supported".format(c))

    def uniques(self, cs):
        return sum([self.unique(c) for c in cs])
"""
