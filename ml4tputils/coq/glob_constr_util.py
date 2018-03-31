from coq.glob_constr import *


# -------------------------------------------------
# Computing histogram of Coq glob_constr

class HistGlobConstr(object):
    def __init__(self, decoded):
        self.decoded = decoded
        self.hist_ast = {}

    def _histcon(self, key, hist):
        self.hist_ast[key] = hist
        return hist

    def decode_hist(self, key):
        return self.hist(self.decoded[key])

    def hist(self, gc):
        key = gc.tag
        if key in self.hist_ast:
            hist = self.hist_ast[key]
            return hist

        ty = type(gc)
        if ty is GRef:
            return self._histcon(key, COQGC_HIST.delta('GRef'))
        elif ty is GVar:
            return self._histcon(key, COQGC_HIST.delta('GVar'))
        elif ty is GEvar:
            return self._histcon(key, COQGC_HIST.delta('GEvar'))
        elif ty is GPatVar:
            return self._histcon(key, COQGC_HIST.delta('GPatVar'))
        elif ty is GApp:
            hist = COQGC_HIST.merges([self.hist(gc.g), self.hists(gc.gs),
                                      COQGC_HIST.delta('GApp')])
            return self._histcon(key, hist)
        elif ty is GLambda:
            hist = COQGC_HIST.merges([self.hist(gc.g_ty), self.hist(gc.g_bod),
                                      COQGC_HIST.delta('GLambda')])
            return self._histcon(key, hist)
        elif ty is GProd:
            hist = COQGC_HIST.merges([self.hist(gc.g_ty), self.hist(gc.g_bod),
                                      COQGC_HIST.delta('GProd')])
            return self._histcon(key, hist)
        elif ty is GLetIn:
            hist = COQGC_HIST.merges([self.hist(gc.g1), self.hist(gc.g2),
                                      COQGC_HIST.delta('GLetIn')])
            return self._histcon(key, hist)
        elif ty is GCases:
            pass
        elif ty is GLetTuple:
            hist = COQGC_HIST.merges([self.hist(gc.g1), self.hist(gc.g2),
                                      COQGC_HIST.delta('GLetTuple')])
            return self._histcon(key, hist)
        elif ty is GIf:
            hist = COQGC_HIST.merges([self.hist(gc.g1), self.hist(gc.g2), self.hist(gc.g3),
                                      COQGC_HIST.delta('GIf')])
            return self._histcon(key, hist)
        elif ty is GRec:
            hist = COQGC_HIST.merges([self.hists(gc.gc_tys), self.hist(gc.gc_bods),
                                      COQGC_HIST.delta('GRec')])
            return self._histcon(key, hist)
        elif ty is GSort:
            return self._histcon(key, COQGC_HIST.delta('GSort'))
        elif ty is GHole:
            return self._histcon(key, COQGC_HIST.delta('GHole'))
        elif ty is GCast:
            hist = COQGC_HIST.merges([self.hist(gc.g), COQGC_HIST.delta('GCast')])
            return self._histcon(key, hist)
        else:
            raise NameError("Kind {} not supported".format(gc))

    def hists(self, cs):
        return COQGC_HIST.merges([self.hist(c) for c in cs])


# -------------------------------------------------
# Computing tokens in Coq glob_constr

class TokenGlobConstr(object):
    def __init__(self, decoded):
        self.decoded = decoded       # Dict[int, GExp]

        self.seen = set()

        # Unique
        self.unique_sort = set()
        self.unique_const = set()
        self.unique_ind = set()
        self.unique_conid = set()
        self.unique_evar = set()
        self.unique_fix = set()

    def tokenize(self):
        for idx, gc in self.decoded.items():
            self.token(gc)
        return (self.unique_sort, self.unique_const, self.unique_ind,
                self.unique_conid, self.unique_evar, self.unique_fix)

    def decode_hist(self, key):
        return self.hist(self.decoded[key])

    def _seen(self, gc):
        self.seen.add(gc.tag)

    def token(self, gc):
        if gc.tag in self.seen:
            return

        ty = type(gc)
        if ty is GRef:
            gref = gc.gref
            ty2 = type(gref)
            if ty2 is VarRef:
                # TODO(deh): should we add it here?
                self.unique_const.add(gref.x)
            elif ty2 is ConstRef:
                self.unique_const.add(gref.const)
            elif ty2 is IndRef:
                self.unique_ind.add(gref.ind.mutind)
            elif ty2 is ConstructRef:
                self.unique_ind.add(gref.ind.mutind)
                self.unique_conid.add((gref.ind.mutind, gref.conid))
            else:
                raise NameError("Not supported", gref)
            return self._seen(gc)
        elif ty is GVar:
            return self._seen(gc)
        elif ty is GEvar:
            self.unique_evar.add(gc.ek)
            return self._seen(gc)
        elif ty is GPatVar:
            return self._seen(gc)
        elif ty is GApp:
            self.token(gc.g)
            self.tokens(gc.gs)
            return self._seen(gc)
        elif ty is GLambda:
            self.token(gc.g_ty)
            self.token(gc.g_bod)
            return self._seen(gc)
        elif ty is GProd:
            self.token(gc.g_ty)
            self.token(gc.g_bod)
            return self._seen(gc)
        elif ty is GLetIn:
            self.token(gc.g1)
            self.token(gc.g2)
            return self._seen(gc)
        elif ty is GCases:
            for cc in gc.ccs:
                self.token(cc.g)
            return self._seen(gc)
        elif ty is GLetTuple:
            self.token(gc.m_name_and_ty[1])
            self.token(gc.g1)
            self.token(gc.g2)
        elif ty is GIf:
            self.token(gc.g1)
            self.token(gc.m_name_and_ty[1])
            self.token(gc.g2)
            self.token(gc.g3)
            return self._seen(gc)
        elif ty is GRec:
            self.tokens(gc.gc_tys)
            self.tokens(gc.gc_bods)
            return self._seen(gc)
        elif ty is GSort:
            self.unique_sort.add(gc.gsort)
            return self._seen(gc)
        elif ty is GHole:
            return self._seen(gc)
        elif ty is GCast:
            self.token(gc.g)
            if gc.g_cty:
                self.token(gc.g_cty)
            return self._seen(gc)
        else:
            raise NameError("Kind {} not supported".format(gc))

    def tokens(self, gcs):
        for gc in gcs:
            self.token(gc)
