from coq.ast import *
from lib.myhist import MyHist

"""
[Note]

Utility functions on Coq expressions

1: Base
2: A 1 1
3: A 2 2
4: A 3 1

2: (1, 2x)
3: (2, 2x)
4: (1, 1x), (3, 1x)

2: (1, 2x)
3: (1, 4x), (2, 2x)
4: (1, 5x), (2, 2x), (3, 1x)

"""


# -------------------------------------------------
# Check the decoded representation

class ChkCoqExp(object):
    def __init__(self, concr_ast):
        self.concr_ast = concr_ast

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

    def _chk_ast(self, f_chk, c):
        c_p = self.concr_ast[c.tag]
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
    def __init__(self, concr_ast, f_shared=False):
        self.concr_ast = concr_ast
        ChkCoqExp(concr_ast).chk_concr_ast()
        self.size_ast = {}
        self.f_shared = f_shared

    def _sizecon(self, key, size):
        self.size_ast[key] = size
        return size

    def decode_size(self, key):
        return self.size(self.concr_ast[key])

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
