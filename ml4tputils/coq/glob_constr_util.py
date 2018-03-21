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
