from coq.glob_constr import *


"""
[Note]

Ideally have ctx/conclusion in GAst (TODO later)
Hmm, train on kernel or GAST???
"""


class GlobConstrParser(object):
    def __init__(self):
        pass

    def _unpack(self, sexpr):
        try:
            tag = sexpr[0]
            body = sexpr[1:]
            return tag._val, body
        except:
            return sexpr._val, None

    def _strify(self, sexpr):
        return sexpr._val

    def parse_global_reference(self, gr):
        tag, body = self._unpack(gr)
        if tag == "VR":
            return VarRef(self._strify(body[0]))
        elif tag == "CR":
            return ConstRef(self._strify(body[0]))
        elif tag == "IR":
            return IndRef(self._strify(body[0]), int(body[1]))
        elif tag == "TR":
            return ConstructRef(self._strify(body[0]), int(body[1]), int(body[2]))
        else:
            raise NameError("Tag {} not supported.".format(tag))

    def parse_glob_constr(self, c):
        tag, body = self._unpack(c)
        if tag == "!":
            return GRef(self.parse_global_reference(body[0]), [])
        elif tag == "V":
            return GVar(self._strify(body[0]))
        elif tag == "E":
            # TODO(deh): sigh* strify 4tw
            return GEvar(self._strify(body[0]), self._strify(body[1]))
        elif tag == "PV":
            return GPatVar(bool(body[0]), self._strify(body[1]))
        elif tag == "A":
            return GApp(self.parse_glob_constr(body[0]), self.parse_glob_constrs(body[1]))
        elif tag == "L":
            return GLambda(self._strify(body[0]), self.parse_glob_constr(body[1]), self.parse_glob_constr(body[2]))
        elif tag == "P":
            return GProd(self._strify(body[0]), self.parse_glob_constr(body[1]), self.parse_glob_constr(body[2]))
        elif tag == "LI":
            return GLetIn(self._strify(body[0]), self.parse_glob_constr(body[1]), self.parse_glob_constr(body[2]))
        elif tag == "C":
            # TODO(deh): sigh* strify 4tw
            return GCases(self._strify(body[0]), self._strify(body[1]), self._strify(body[2]), self._strify(body[3]))
        elif tag == "LT":
            return GLetTuple(self._strify(body[0]), self._strify(body[1]), self.parse_glob_constr(body[2]),
                             self.parse_glob_constr(body[3]))
        elif tag == "I":
            return GIf(self.parse_glob_constr(body[0]), None, self.parse_glob_constr(body[1]),
                       self.parse_glob_constr(body[2]))
        elif tag == "R":
            raise NameError("TODO")
        elif tag == "S":
            return GSort(self._strify(body[0]))
        elif tag == "T":
            return GCast(self.parse_glob_constr(body[0]), self.parse_cast_type(body[1]))
        else:
            raise NameError("Tag {} not supported.".format(tag))

    def parse_glob_constrs(self, gcs):
        return [self.parse_glob_constr(gc) for gc in gcs]

    def parse_cast_type(self, cty):
        # TODO(deh): change me
        return cty
