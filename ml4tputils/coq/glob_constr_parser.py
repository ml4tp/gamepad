import sexpdata

from coq.glob_constr import *


"""
[Note]

Ideally have ctx/conclusion in GAst (TODO later)
Hmm, train on kernel or GAST???
"""


# -------------------------------------------------
# TODO(deh): MOVE ME

def sexpr_strify(sexpr):
    if isinstance(sexpr, sexpdata.Symbol):
        return sexpr._val
    elif isinstance(sexpr, float):
        # NOTE(deh): wtf, inF -> inf as a floating point ...
        return str(sexpr)
    else:
        raise NameError("Cannot strify {}".format(sexpr))


def sexpr_unpack(sexpr):
    try:
        tag = sexpr[0]
        body = sexpr[1:]
        return tag._val, body
    except:
        return sexpr._val, None


# -------------------------------------------------
# Parsing Full Asts?

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

    def parse_global_reference(self, gr):
        tag, body = sexpr_unpack(gr)
        if tag == "VR":
            return VarRef(sexpr_strify(body[0]))
        elif tag == "CR":
            return ConstRef(sexpr_strify(body[0]))
        elif tag == "IR":
            return IndRef(sexpr_strify(body[0]), int(body[1]))
        elif tag == "TR":
            return ConstructRef(sexpr_strify(body[0]), int(body[1]), int(body[2]))
        else:
            raise NameError("Tag {} not supported.".format(tag))

    def parse_glob_sort(self, gsort):
        # tag, body = self._unpack(gsort)
        # if tag == "P":
        #     pass
        # elif tag == "S":
        #     pass
        # elif tag == "T":
        #     pass
        # else:
        #     raise NameError("Tag {} not supported.".format(tag))
        return gsort

    def parse_cast_type(self, cty):
        # TODO(deh): change me
        return cty

    def parse_glob_constr(self, c):
        tag, body = sexpr_unpack(c)
        if tag == "!":
            return GRef(self.parse_global_reference(body[0]), [])
        elif tag == "V":
            return GVar(sexpr_strify(body[0]))
        elif tag == "E":
            # TODO(deh): sigh* strify 4tw
            return GEvar(sexpr_strify(body[0]), body[1])
        elif tag == "PV":
            return GPatVar(bool(body[0]), sexpr_strify(body[1]))
        elif tag == "A":
            return GApp(self.parse_glob_constr(body[0]), self.parse_glob_constrs(body[1]))
        elif tag == "L":
            return GLambda(sexpr_strify(body[0]), sexpr_strify(body[1]),
                           self.parse_glob_constr(body[2]), self.parse_glob_constr(body[3]))
        elif tag == "P":
            return GProd(sexpr_strify(body[0]), sexpr_strify(body[1]),
                         self.parse_glob_constr(body[2]), self.parse_glob_constr(body[3]))
        elif tag == "LI":
            return GLetIn(sexpr_strify(body[0]), self.parse_glob_constr(body[1]), self.parse_glob_constr(body[2]))
        elif tag == "C":
            # TODO(deh): sigh* strify 4tw
            return GCases(body[0], body[1], body[2], body[3])
        elif tag == "LT":
            n = sexpr_strify(body[1][0])
            m_gc = self.parse_maybe(self.parse_glob_constr, body[1][1])
            return GLetTuple([sexpr_strify(x) for x in body[0]], (n, m_gc),
                             self.parse_glob_constr(body[2]), self.parse_glob_constr(body[3]))
        elif tag == "I":
            return GIf(self.parse_glob_constr(body[0]), None, self.parse_glob_constr(body[1]),
                       self.parse_glob_constr(body[2]))
        elif tag == "R":
            ids = [sexpr_strify(x) for x in body[1]]
            # gdecl_args = [[sexpr_strify(x) for x in xs] for xs in body[2]]   # TODO(deh): sigh* strify 4tw
            return GRec(body[0], ids, body[2],
                        self.parse_glob_constrs(body[3]), self.parse_glob_constrs(body[4]))
            # raise NameError("TODO")
        elif tag == "S":
            return GSort(self.parse_glob_sort(body[0]))
        elif tag == "T":
            return GCast(self.parse_glob_constr(body[0]), self.parse_cast_type(body[1]))
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
            return self._mkcon(key, GApp(gc, gcs))
        elif tag == "L":
            name = sexpr_strify(body[0])
            bk = sexpr_strify(body[1])
            gc_ty = self.decode_glob_constr(body[2])
            gc_bod = self.decode_glob_constr(body[3])
            return self._mkcon(key, GLambda(name, bk, gc_ty, gc_bod))
        elif tag == "P":
            name = sexpr_strify(body[0])
            bk = sexpr_strify(body[1])
            gc_ty = self.decode_glob_constr(body[2])
            gc_bod = self.decode_glob_constr(body[3])
            return self._mkcon(key, GProd(name, bk, gc_ty, gc_bod))
        elif tag == "LI":
            name = sexpr_strify(body[0])
            gc_ty = self.decode_glob_constr(body[1])
            gc_bod = self.decode_glob_constr(body[2])
            return self._mkcon(key, GLetIn(name, gc_ty, gc_bod))
        elif tag == "C":
            csty = body[0]
            m_gc = body[1]
            tmts = body[2]
            ccs = body[3]    # TODO(deh): this is where the cases are
            return self._mkcon(key, GCases(csty, m_gc, tmts, ccs))
        elif tag == "LT":
            names = [sexpr_strify(x) for x in body[0]]
            n = sexpr_strify(body[1][0])
            m_gc = self.parser.parse_maybe(self.decode_glob_constr, body[1][1])
            gc1 = self.decode_glob_constr(body[2])
            gc2 = self.decode_glob_constr(body[3])
            return self._mkcon(key, GLetTuple(names, (n, m_gc), gc1, gc2))
        elif tag == "I":
            gc1 = self.decode_glob_constr(body[0])
            name = sexpr_strify(body[1][0])
            m_ty = self.parser.parse_maybe(self.decode_glob_constr, body[1][1])
            gc2 = self.decode_glob_constr(body[2])
            gc3 = self.decode_glob_constr(body[3])
            return self._mkcon(key, GIf(gc1, (name, m_ty), gc2, gc3))
        elif tag == "R":
            fix_kind = body[0]
            ids = [sexpr_strify(x) for x in body[1]]
            gdecl_args = body[2]
            # gdecl_args = [[sexpr_strify(x) for x in xs] for xs in body[2]]
            gc_tys = self.decode_glob_constrs(body[3])
            gc_bods = self.decode_glob_constrs(body[4])
            return self._mkcon(key, GRec(fix_kind, ids, gdecl_args, gc_tys, gc_bods))
        elif tag == "S":
            gsort = self.parser.parse_glob_sort(body[0])
            return self._mkcon(key, GSort(gsort))
        elif tag == "T":
            gc = self.decode_glob_constr(body[0])
            ty_gc = self.parser.parse_cast_type(body[1])
            return self._mkcon(key, GCast(gc, ty_gc))
        else:
            raise NameError("Tag {} not supported.".format(tag))

    def decode_glob_constrs(self, gcs):
        return [self.decode_glob_constr(gc) for gc in gcs]
