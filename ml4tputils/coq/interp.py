from coq.ast import *
from coq.util import SizeCoqExp
from lib.myenv import MyEnv
from lib.myutil import NotFound

"""
[Note]

4 levels of `compression`

Ex:
let x = 2 + 2 in
let x = x + x in
(fun y -> y) (x + x)

1. Static and shared (input)
    $8
    where
        $0: y
        $1: fun y -> $0
        $2: x
        $3: $2 + $2
        $4: $1 $3
        $5: let x = $3 in $4
        $6: 2
        $7: $6 + $6
        $8: let x = $7 in $5

    hist:
        Const: 1
        Var: 3
        App: 3
        Let: 2
        Lam: 1

2. Static and un-shared (unshare the input)
    let x = 2 + 2 in
    let x = x + x in
    (fun y -> y) (x + x)

    hist:
        Const: 2
        Var: 4
        App: 4
        Let: 2
        Lam: 1

3. Dynamic and shared ("call-by-need")
    let t1 = 2 + 2 in
    let t2 = t1 + t1 in
    let t3 = t2 + t2 in
    t3

    hist:
        Const: 2
        Var: 4
        App: 3
        Let: 3
        Lam: 0

4. Dynamic and un-shared ("call-by-name")
    2 + 2 + 2 + 2 + 2 + 2 + 2 + 2

    hist:
        Const: 8
        Var: 0
        App: 7
        Let: 0
        Lam: 0
"""


# -------------------------------------------------
# Values

class Val(object):
    pass


class BaseVal(Val):
    def __init__(self, c):
        assert isinstance(c, Exp)
        self.c = c

    def __str__(self):
        return str(self.c)


class EvarVal(Val):
    def __init__(self, exk, vs):
        assert isinstance(exk, Name)
        for v in vs:
            assert isinstance(v, Val)
        self.exk = exk
        self.vs = vs

    def __str__(self):
        return "EV({}, {})".format(self.exk,
                                   ",".join([str(v) for v in self.vs]))


class CastVal(Val):
    def __init__(self, v_c, ck, v_ty):
        assert isinstance(v_c, Val)
        assert isinstance(v_ty, Val)
        self.v_c = v_c
        self.ck = ck
        self.v_ty = v_ty

    def __str__(self):
        return "CAV({}, {}, {})".format(str(self.v_c), self.ck, str(self.v_ty))


class CloVal(Val):
    def __init__(self, env, c):
        assert isinstance(env, MyEnv)
        assert isinstance(c, Exp)
        self.env = env
        self.c = c

    def __str__(self):
        return "CLO({}, {})".format(self.env.dump(), str(self.c))


class AppVal(Val):
    def __init__(self, v_c, v_cs):
        assert isinstance(v_c, Val)
        for v_p in v_cs:
            assert isinstance(v_p, Val)
        self.v_c = v_c
        self.v_cs = v_cs

    def __str__(self):
        return "AV({}, {})".format(str(self.v_c),
                                   ",".join([str(v_p) for v_p in self.v_cs]))


class CaseVal(Val):
    def __init__(self, ci, ret, match, cases):
        assert isinstance(ci, CaseInfo)
        assert isinstance(ret, Val)
        assert isinstance(match, Val)
        for c_p in cases:
            assert isinstance(c_p, Val)
        self.ci = ci
        self.ret = ret
        self.match = match
        self.cases = cases

    def __str__(self):
        x = (self.ci, str(self.ret), str(self.match),
             ",".join([str(v_p) for v_p in self.cases]))
        return "CSV({}, {}, {}, {})".format(*x)


class ProjVal(Val):
    def __init__(self, proj, v):
        assert isinstance(proj, Name)
        assert isinstance(v, Val)
        self.proj = proj
        self.v = v

    def __str__(self):
        return "PJV({}, {})".format(self.proj, str(self.v))


# -------------------------------------------------
# Interpreter

class InterpCBName(object):
    def __init__(self):
        self.steps = 0

    def interp(self, env, c):
        if self.steps > 10000:
            return BaseVal(c)
        self.steps += 1
        if isinstance(c, RelExp):
            try:
                v = env.lookup_rel(c.idx)
                return v
            except NotFound:
                return BaseVal(c)
        elif isinstance(c, VarExp):
            try:
                v = env.lookup_id(Name(c.x))
                return v
            except NotFound:
                return BaseVal(c)
        elif isinstance(c, MetaExp):
            assert False
        elif isinstance(c, EvarExp):
            vs = self.interp(env, c.cs)
            return EvarVal(c.exk, vs)
        elif isinstance(c, SortExp):
            return BaseVal(c)
        elif isinstance(c, CastExp):
            v_c = self.interp(env, c.c)
            v_ty = self.interp(env, c.ty)
            return CastVal(v_c, c.ck, v_ty)
        elif isinstance(c, ProdExp):
            return CloVal(env, c)
        elif isinstance(c, LambdaExp):
            return CloVal(env, c)
        elif isinstance(c, LetInExp):
            v_c1 = self.interp(env, c.c1)
            v_ty = self.interp(env, c.ty)
            v_c2 = self.interp(env.extend(c.name, v_c1), c.c2)
            return v_c2
        elif isinstance(c, AppExp):
            v_c = self.interp(env, c.c)
            v_cs = self.interps(env, c.cs)
            if isinstance(v_c, CloVal) and (isinstance(v_c.c, LambdaExp) or isinstance(v_c.c, LambdaExp)):
                for v in v_cs:
                    env_p = v_c.env
                    env_p = env_p.extend(v_c.c.name, v)
                return self.interp(env_p, v_c.c.c)
            else:
                return AppVal(v_c, v_cs)
        elif isinstance(c, ConstExp):
            return BaseVal(c)
        elif isinstance(c, IndExp):
            return BaseVal(c)
        elif isinstance(c, ConstructExp):
            return BaseVal(c)
        elif isinstance(c, CaseExp):
            v_ret = self.interp(env, c.ret)
            v_match = self.interp(env, c.match)
            # TODO(deh): env?
            v_cases = self.interps(env, c.cases)
            return CaseVal(c.ci, v_ret, v_match, v_cases)
        elif isinstance(c, FixExp):
            return CloVal(env, c)
        elif isinstance(c, CoFixExp):
            return CloVal(env, c)
        elif isinstance(c, ProjExp):
            v_c = self.interp(env, c.c)
            return ProjVal(c.proj, v_c)
        else:
            raise NameError("Kind {} not supported".format(c))

    def interps(self, env, cs):
        return [self.interp(env, c) for c in cs]


# -------------------------------------------------
# Size

class SizeCoqVal(object):
    def __init__(self, concr_ast):
        self.concr_ast = concr_ast
        self.sce = SizeCoqExp(self.concr_ast)

    def size(self, v):
        if isinstance(v, BaseVal):
            return self.sce.size(v.c)
        elif isinstance(v, EvarVal):
            return 1 + self.sizes(v.v_cs)
        elif isinstance(v, CastVal):
            return 1 + self.size(v.v_c) + self.size(v.v_ty)
        elif isinstance(v, CloVal):
            return self.sce.size(v.c)
        elif isinstance(v, AppVal):
            return 1 + self.size(v.v_c) + self.sizes(v.v_cs)
        elif isinstance(v, CaseVal):
            return (1 + self.size(v.ret) + self.size(v.match) +
                    self.sizes(v.cases))
        elif isinstance(v, ProjVal):
            return 1 + self.size(v.v_c)
        else:
            raise NameError("Kind {} not supported".format(v))

    def sizes(self, vs):
        return sum([self.size(v) for v in vs])
