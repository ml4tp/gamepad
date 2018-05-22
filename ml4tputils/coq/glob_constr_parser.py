from coq.glob_constr import *
from coq.constr import Name, Inductive
from lib.mysexpr import *


"""
[Note]

Parse/Decode glob_constr (mid-level) AST.
"""


# -------------------------------------------------
# Parsing glob_constr

class GlobConstrParser(object):
    def __init__(self):
        pass

    def parse_maybe(self, parse, sexpr):
        tag, body = sexpr_unpack(sexpr)
        if tag == "N":
            return None
        elif tag == "S":
            return parse(body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def parse_ls(self, parse, ls):
        return [parse(x) for x in ls]

    def parse_global_reference(self, gr):
        tag, body = sexpr_unpack(gr)
        if tag == "VR":
            return VarRef(sexpr_strify(body[0]))
        elif tag == "CR":
            const = Name(sexpr_strify(body[0]))
            return ConstRef(const)
        elif tag == "IR":
            mutind = Name(sexpr_strify(body[0]))
            pos = int(body[1])
            return IndRef(Inductive(mutind, pos))
        elif tag == "TR":
            mutind = Name(sexpr_strify(body[0]))
            pos = int(body[1])
            return ConstructRef(Inductive(mutind, pos), int(body[2]))
        else:
            raise NameError("Tag {} not supported.".format(tag))

    def parse_glob_sort(self, gsort):
        tag, body = sexpr_unpack(gsort)
        return tag

    def parse_cast_type(self, parse, cty):
        tag, body = sexpr_unpack(cty)
        if tag == "C":
            return CastType("C", parse(body[0]))
        elif tag == "VM":
            return CastType("VM", parse(body[0]))
        elif tag == "O":
            return CastType("O", None)
        elif tag == "N":
            return CastType("N", parse(body[0]))
        else:
            raise NameError("Tag {} not supported.".format(tag))

    def parse_predicate_pattern(self, pp):
        name = sexpr_strify(pp[0])

        def f(x):
            ind = Inductive(Name(sexpr_strify(x[0])), int(x[1]))
            names = self.parse_ls(sexpr_strify, x[2])
            return ind, names

        m_ind_and_names = self.parse_maybe(f, pp[1])
        return PredicatePattern(name, m_ind_and_names)

    def parse_tomatch_tuple(self, parse_gc, tmt):
        gc = parse_gc(tmt[0])
        pp = self.parse_predicate_pattern(tmt[1])
        return TomatchTuple(gc, pp)

    def parse_tomatch_tuples(self, parse_gc, tmts):
        return [self.parse_tomatch_tuple(parse_gc, tmt) for tmt in tmts]

    def parse_cases_pattern(self, cp):
        tag, body = sexpr_unpack(cp)
        if tag == "V":
            return PatVar(Name(sexpr_strify(body[0])))
        elif tag == "C":
            ind = Inductive(Name(sexpr_strify(body[0])), int(body[1]))
            j = int(body[2])
            cps = self.parse_ls(self.parse_cases_pattern, body[3])
            name = Name(sexpr_strify(body[4]))
            return PatCstr(ind, j, cps, name)
        else:
            raise NameError("Tag {} not supported.".format(tag))

    def parse_case_clause(self, parse_gc, cc):
        ids = self.parse_ls(lambda x: x, cc[0])
        cps = self.parse_ls(self.parse_cases_pattern, cc[1])
        gc = parse_gc(cc[2])
        return CasesClause(ids, cps, gc)

    def parse_case_clauses(self, parse_gc, ccs):
        return [self.parse_case_clause(parse_gc, cc) for cc in ccs]

    def parse_imp_arg(self, iarg):
        return self.parse_maybe(lambda x: x[0], iarg)

    def parse_imp_args(self, iargs):
        # NOTE(deh): list of lists? take first one ...
        if iargs:
            return [self.parse_imp_arg(iarg) for iarg in iargs[0]]
        else:
            return []

    def parse_glob_decl(self, parse_gc, gdecl):
        name = Name(sexpr_strify(gdecl[0]))
        bk = gdecl[1]
        m_gc = self.parse_maybe(parse_gc, gdecl[2])
        gc = parse_gc(gdecl[3])
        return GlobDecl(name, bk, m_gc, gc)

    def parse_glob_declss(self, parse_gc, gdecl_argss):
        return self.parse_ls(lambda ls: self.parse_ls(lambda gdecl: self.parse_glob_decl(parse_gc, gdecl), ls), gdecl_argss)

    def parse_glob_constr(self, c):
        tag, body = sexpr_unpack(c)
        if tag == "!":
            return GRef(self.parse_global_reference(body[0]), [])
        elif tag == "V":
            return GVar(sexpr_strify(body[0]))
        elif tag == "E":
            return GEvar(sexpr_strify(body[0]), body[1])
        elif tag == "PV":
            return GPatVar(bool(body[0]), sexpr_strify(body[1]))
        elif tag == "A":
            gc = self.parse_glob_constr(body[0])
            gcs = self.parse_glob_constrs(body[1])
            iargs = self.parse_imp_args(body[2])
            return GApp(gc, gcs, iargs)
        elif tag == "L":
            name = Name(sexpr_strify(body[0]))
            bk = sexpr_strify(body[1])
            g_ty = self.parse_glob_constr(body[2])
            g_bod = self.parse_glob_constr(body[3])
            return GLambda(name, bk, g_ty, g_bod)
        elif tag == "P":
            name = Name(sexpr_strify(body[0]))
            bk = sexpr_strify(body[1])
            g_ty = self.parse_glob_constr(body[2])
            g_bod = self.parse_glob_constr(body[3])
            return GProd(name, bk, g_ty, g_bod)
        elif tag == "LI":
            name = Name(sexpr_strify(body[0]))
            gc1 = self.parse_glob_constr(body[1])
            gc2 = self.parse_glob_constr(body[2])
            return GLetIn(name, gc1, gc2)
        elif tag == "C":
            csty = sexpr_strify(body[0])
            m_gc = self.parse_maybe(self.parse_glob_constr, body[1])
            tmts = self.parse_tomatch_tuples(self.parse_glob_constr, body[2])
            ccs = self.parse_case_clauses(self.parse_glob_constr, body[3])
            return GCases(csty, m_gc, tmts, ccs)
        elif tag == "LT":
            names = [Name(sexpr_strify(x)) for x in body[0]]
            name = Name(sexpr_strify(body[1][0]))
            m_gc = self.parse_maybe(self.parse_glob_constr, body[1][1])
            gc1 = self.parse_glob_constr(body[2])
            gc2 = self.parse_glob_constr(body[3])
            return GLetTuple(names, (name, m_gc), gc1, gc2)
        elif tag == "I":
            return GIf(self.parse_glob_constr(body[0]), None, self.parse_glob_constr(body[1]),
                       self.parse_glob_constr(body[2]))
        elif tag == "R":
            ids = [sexpr_strify(x) for x in body[1]]
            gdecl_args = self.parse_glob_declss(self.parse_glob_constr, body[2])
            return GRec(body[0], ids, gdecl_args, self.parse_glob_constrs(body[3]), self.parse_glob_constrs(body[4]))
        elif tag == "S":
            return GSort(self.parse_glob_sort(body[0]))
        elif tag == "H":
            ek = body[0]
            ipne = body[1]
            m_ga = body[2]
            return GHole(ek, ipne, m_ga)
        elif tag == "T":
            gc = self.parse_glob_constr(body[0])
            g_cty = self.parse_cast_type(self.parse_glob_constr, body[1])
            return GCast(gc, g_cty)
        else:
            raise NameError("Tag {} not supported.".format(tag))

    def parse_glob_constrs(self, gcs):
        return [self.parse_glob_constr(gc) for gc in gcs]


# -------------------------------------------------
# Decoding ASTs

class GlobConstrDecoder(object):
    def __init__(self, mid_share):
        # Internal state
        self.mid_share = mid_share           # Dict[int, str]
        self.parser = GlobConstrParser()

        # Shared representation
        self.decoded = {}                    # Dict[int, GExp]
        for key, entry in self.mid_share.items():
            self.decode_glob_constr(key)

    def decode_exp_by_key(self, key):
        return self.decoded[key]

    def _mkcon(self, key, gc):
        if key in self.decoded:
            return self.decoded[key]
        else:
            gc.tag = key
            self.decoded[key] = gc
            return gc

    def decode_glob_constr(self, key):
        if key in self.decoded:
            return self.decoded[key]

        tag, body = sexpr_unpack(self.mid_share[key])
        if tag == "!":
            gref = self.parser.parse_global_reference(body[0])
            return self._mkcon(key, GRef(gref, []))
        elif tag == "V":
            v = sexpr_strify(body[0])
            return self._mkcon(key, GVar(v))
        elif tag == "E":
            ev = sexpr_strify(body[0])
            id_and_globs = body[1]
            return self._mkcon(key, GEvar(ev, id_and_globs))
        elif tag == "PV":
            b = bool(body[0])
            pv = sexpr_strify(body[1])
            return self._mkcon(key, GPatVar(b, pv))
        elif tag == "A":
            gc = self.decode_glob_constr(body[0])
            gcs = self.decode_glob_constrs(body[1])
            iargs = self.parser.parse_imp_args(body[2])
            return self._mkcon(key, GApp(gc, gcs, iargs))
        elif tag == "L":
            name = Name(sexpr_strify(body[0]))
            bk = sexpr_strify(body[1])
            gc_ty = self.decode_glob_constr(body[2])
            gc_bod = self.decode_glob_constr(body[3])
            return self._mkcon(key, GLambda(name, bk, gc_ty, gc_bod))
        elif tag == "P":
            name = Name(sexpr_strify(body[0]))
            bk = sexpr_strify(body[1])
            gc_ty = self.decode_glob_constr(body[2])
            gc_bod = self.decode_glob_constr(body[3])
            return self._mkcon(key, GProd(name, bk, gc_ty, gc_bod))
        elif tag == "LI":
            name = Name(sexpr_strify(body[0]))
            gc_ty = self.decode_glob_constr(body[1])
            gc_bod = self.decode_glob_constr(body[2])
            return self._mkcon(key, GLetIn(name, gc_ty, gc_bod))
        elif tag == "C":
            csty = sexpr_strify(body[0])
            m_gc = self.parser.parse_maybe(self.decode_glob_constr, body[1])
            tmts = self.parser.parse_tomatch_tuples(self.decode_glob_constr, body[2])
            ccs = self.parser.parse_case_clauses(self.decode_glob_constr, body[3])
            return self._mkcon(key, GCases(csty, m_gc, tmts, ccs))
        elif tag == "LT":
            names = [Name(sexpr_strify(x)) for x in body[0]]
            name = Name(sexpr_strify(body[1][0]))
            m_gc = self.parser.parse_maybe(self.decode_glob_constr, body[1][1])
            gc1 = self.decode_glob_constr(body[2])
            gc2 = self.decode_glob_constr(body[3])
            return self._mkcon(key, GLetTuple(names, (name, m_gc), gc1, gc2))
        elif tag == "I":
            gc1 = self.decode_glob_constr(body[0])
            name = Name(sexpr_strify(body[1][0]))
            m_ty = self.parser.parse_maybe(self.decode_glob_constr, body[1][1])
            gc2 = self.decode_glob_constr(body[2])
            gc3 = self.decode_glob_constr(body[3])
            return self._mkcon(key, GIf(gc1, (name, m_ty), gc2, gc3))
        elif tag == "R":
            fix_kind = body[0]
            ids = [sexpr_strify(x) for x in body[1]]
            gdecl_args = self.parser.parse_glob_declss(self.decode_glob_constr, body[2])
            gc_tys = self.decode_glob_constrs(body[3])
            gc_bods = self.decode_glob_constrs(body[4])
            return self._mkcon(key, GRec(fix_kind, ids, gdecl_args, gc_tys, gc_bods))
        elif tag == "S":
            gsort = self.parser.parse_glob_sort(body[0])
            return self._mkcon(key, GSort(gsort))
        elif tag == "H":
            ek = body[0]
            ipne = body[1]
            m_ga = body[2]
            return self._mkcon(key, GHole(ek, ipne, m_ga))
        elif tag == "T":
            gc = self.decode_glob_constr(body[0])
            ty_gc = self.parser.parse_cast_type(self.decode_glob_constr, body[1])
            return self._mkcon(key, GCast(gc, ty_gc))
        else:
            raise NameError("Tag {} not supported.".format(tag))

    def decode_glob_constrs(self, gcs):
        return [self.decode_glob_constr(gc) for gc in gcs]
