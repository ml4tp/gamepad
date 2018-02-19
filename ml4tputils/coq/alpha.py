from coq.ast import *


"""
[Note]

Alpha-convert a Coq expression.
I don't think this is currently used?
"""


class AlphaCoqExp(object):
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
