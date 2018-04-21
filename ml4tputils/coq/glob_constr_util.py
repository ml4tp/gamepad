from coq.glob_constr import *
# from lib.mysexpr import sexpr_unpack, sexpr_strify


# -------------------------------------------------
# Computing size of Coq glob_constr

class SizeGlobConstr(object):
    def __init__(self, decoded, f_cntiarg=True):
        self.decoded = decoded
        self.size_ast = {}
        self.cnt_iarg = f_cntiarg

    def _sizecon(self, key, size):
        self.size_ast[key] = hist
        return size

    def decode_size(self, key):
        return self.size(self.decoded[key])

    def size(self, gc):
        key = gc.tag
        if key in self.hist_ast:
            hist = self.hist_ast[key]
            return hist

        ty = type(gc)
        if ty is GRef:
            return self._sizecon(key, 1)
        elif ty is GVar:
            return self._sizecon(key, 1)
        elif ty is GEvar:
            return self._sizecon(key, 1)
        elif ty is GPatVar:
            return self._sizecon(key, 1)
        elif ty is GApp:
            sz = 1 + self.size(gc.g)
            if self.f_cntiarg:
                for gc_p, iarg in zip(gc.gs, gc.iargs):
                    sz += self.size(gc_p)
            else:
                for gc_p, iarg in zip(gc.gs, gc.iargs):
                    if iarg is None:
                        sz += self.size(gc_p)
            return self._sizecon(key, sz)
        elif ty is GLambda:
            sz = 1 + self.size(gc.g_ty) + self.size(gc.g_bod)
            return self._sizecon(key, sz)
        elif ty is GProd:
            sz = 1 + self.size(gc.g_ty) + self.size(gc.g_bod)
            return self._sizecon(key, sz)
        elif ty is GLetIn:
            sz = 1 + self.size(gc.g1) + self.size(gc.g2)
            return self._sizecon(key, sz)
        elif ty is GCases:
            gs = [cc.g for cc in gc.ccs]
            sz = 1 + self.sizes(gs)
            return self._sizecon(key, sz)
        elif ty is GLetTuple:
            sz = 1 + self.size(gc.g1) + self.size(gc.g2)
            return self._sizecon(key, sz)
        elif ty is GIf:
            sz = 1 + self.size(gc.g1) + self.size(gc.g2) + self.size(gc.g3)
            return self._sizecon(key, sz)
        elif ty is GRec:
            sz = 1 + self.sizes(gc.gc_tys) + self.sizes(gc.gc_bods)
            return self._sizecon(key, sz)
        elif ty is GSort:
            return self._sizecon(key, 1)
        elif ty is GHole:
            return self._sizecon(key, 1)
        elif ty is GCast:
            sz = 1 + self.size(gc.g)
            return self._sizecon(key, sz)
        else:
            raise NameError("Kind {} not supported".format(gc))

    def sizes(self, cs):
        return sum([self.size(c) for c in cs])


# -------------------------------------------------
# Computing histogram of Coq glob_constr

class HistGlobConstr(object):
    def __init__(self, decoded):
        self.decoded = decoded
        self.hist_ast = {}
        self.num_iargs = 0
        self.num_args = 0

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
            # Compute proportion of implicit arguments
            for arg in gc.iargs:
                if arg is not None:
                    self.num_iargs += 1
            self.num_args += len(gc.iargs)
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
            gs = [cc.g for cc in gc.ccs]
            hist = COQGC_HIST.merges([self.hists(gs), COQGC_HIST.delta('GCases')])
            return self._histcon(key, hist)
        elif ty is GLetTuple:
            hist = COQGC_HIST.merges([self.hist(gc.g1), self.hist(gc.g2),
                                      COQGC_HIST.delta('GLetTuple')])
            return self._histcon(key, hist)
        elif ty is GIf:
            hist = COQGC_HIST.merges([self.hist(gc.g1), self.hist(gc.g2), self.hist(gc.g3),
                                      COQGC_HIST.delta('GIf')])
            return self._histcon(key, hist)
        elif ty is GRec:
            hist = COQGC_HIST.merges([self.hists(gc.gc_tys), self.hists(gc.gc_bods),
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
            self.unique_evar.add(gc.ev)
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
            self.unique_const.add(Name("Coq.Init.Datatypes.fst"))
            self.unique_const.add(Name("Coq.Init.Datatypes.snd"))
            if gc.m_name_and_ty[1]:
                self.token(gc.m_name_and_ty[1])
            self.token(gc.g1)
            self.token(gc.g2)
        elif ty is GIf:
            self.token(gc.g1)
            if gc.m_name_and_ty[1]:
                self.token(gc.m_name_and_ty[1])
            self.token(gc.g2)
            self.token(gc.g3)
            return self._seen(gc)
        elif ty is GRec:
            self.tokens(gc.gc_tys)
            self.tokens(gc.gc_bods)
            return self._seen(gc)
        elif ty is GSort:
            # [x] TODO(deh): Fix parsing to stirfy
            # tag, body = sexpr_unpack(gc.gsort)
            # if tag == "P":
            #     self.unique_sort.add("P")
            # elif tag == "S":
            #     self.unique_sort.add("S")
            # elif tag == "T":
            #     self.unique_sort.add("T")
            # else:
            #     raise NameError("Tag {} not supported".format(tag))
            self.unique_sort.add(gc.gsort)
            return self._seen(gc)
        elif ty is GHole:
            return self._seen(gc)
        elif ty is GCast:
            self.token(gc.g)
            if gc.g_cty.m_gc:
                self.token(gc.g_cty.m_gc)
            return self._seen(gc)
        else:
            raise NameError("Kind {} not supported".format(gc))

    def tokens(self, gcs):
        for gc in gcs:
            self.token(gc)
