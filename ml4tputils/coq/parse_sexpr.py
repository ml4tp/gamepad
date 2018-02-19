from coq.glob_ast import *


"""
[Note]

Ideally have ctx/conclusion in GAst (TODO later)
Hmm, train on kernel or GAST???
"""


class ParseSexpr(object):
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
            # Printf.sprintf "(VR %s)" (show_id v)
            return VarRef(self._strify(body[0]))
        elif tag == "CR":
            # Printf.sprintf "(CR %s)" (Names.Constant.to_string v)
            return ConstRef(self._strify(body[0]))
        elif tag == "IR":
            # Printf.sprintf "(IR %s %d)" (Names.MutInd.to_string mi) i
            return IndRef(self._strify(body[0]), int(body[1]))
        elif tag == "TR":
            # Printf.sprintf "(TR %s %d %d)" (Names.MutInd.to_string mi) i j
            return ConstructRef(self._strify(body[0]), int(body[1]), int(body[2]))
        else:
            raise NameError("Tag {} not supported.".format(tag))

    def parse_glob_constr(self, c):
        tag, body = self._unpack(c)
        if tag == "!":
            # Printf.sprintf "(! %s)" (show_global_reference gr)
            # TODO(deh): coq printing error
            return GRef(self.parse_global_reference(body[0]), [])
        elif tag == "V":
            # Printf.sprintf "(V %s)" (show_id id)
            return GVar(self._strify(body[0]))
        elif tag == "E":
            # let f (id, gc) = Printf.sprintf "(%s, %s)" (show_id id) (show_glob_constr gc) in
            # Printf.sprintf "(E %s %s)" (show_id en) (show_sexpr_ls f args)
            # TODO(deh): sigh*
            return GEvar(self._strify(body[0]), self._strify(body[1]))
        elif tag == "PV":
            # Printf.sprintf "(PV %b %s)" b (show_id pv)
            return GPatVar(bool(body[0]), self._strify(body[1]))
        elif tag == "A":
            # Printf.sprintf "(A %s %s)" (show_glob_constr gc) (show_glob_constrs gcs)
            return GApp(self.parse_glob_constr(body[0]), self.parse_glob_constrs(body[1]))
        elif tag == "L":
            # Printf.sprintf "(L %s %s %s)" (show_name n) (show_glob_constr gc1) (show_glob_constr gc2)
            return GLambda(self._strify(body[0]), self.parse_glob_constr(body[1]), self.parse_glob_constr(body[2]))
        elif tag == "P":
            # Printf.sprintf "(P %s %s %s)" (show_name n) (show_glob_constr gc1) (show_glob_constr gc2)
            return GProd(self._strify(body[0]), self.parse_glob_constr(body[1]), self.parse_glob_constr(body[2]))
        elif tag == "LI":
            # Printf.sprintf "(LI %s %s %s)" (show_name n) (show_glob_constr gc1) (show_glob_constr gc2)
            return GLetIn(self._strify(body[0]), self.parse_glob_constr(body[1]), self.parse_glob_constr(body[2]))
        elif tag == "C":
            # Printf.sprintf "(C %s %s %s %s)" "TODO" (show_maybe show_glob_constr m_gc) (show_tomatch_tuples tups) (show_case_clauses ccs)
            # TODO(deh): sigh*
            return GCases(self._strify(body[0]), self._strify(body[1]), self._strify(body[2]), self._strify(body[3]))
        elif tag == "LT":
            # let f (name, m_gc) = Printf.sprintf "(%s %s)" (show_name name) (show_maybe show_glob_constr m_gc) in
            # Printf.sprintf "(LT %s %s %s %s)" (show_sexpr_ls show_name ns) (f arg) (show_glob_constr gc1) (show_glob_constr gc2)
            return GLetTuple(self._strify(body[0]), self._strify(body[1]), self.parse_glob_constr(body[2]), self.parse_glob_constr(body[3]))
        elif tag == "I":
            # Printf.sprintf "(I %s %s %s)" (show_glob_constr gc) (show_glob_constr gc2) (show_glob_constr gc3)
            # TODO(deh): coq printing wrong?
            return GIf(self.parse_glob_constr(body[0]), None, self.parse_glob_constr(body[1]), self.parse_glob_constr(body[2]))
        elif tag == "R":
            # Printf.sprintf "(R %s %s %s %s %s)" "TODO" (show_sexpr_arr show_id ids) "TODO" (show_glob_constr_arr gcs1) (show_glob_constr_arr gcs2)
            raise NameError("TODO")
        elif tag == "S":
            # Printf.sprintf "(S %s)" (show_glob_sort gsort)
            return GSort(self._strify(body[0]))
        elif tag == "T":
            # Printf.sprintf "(T %s %s)" (show_glob_constr gc) (show_cast_type show_glob_constr gc_ty)
            return GCast(self.parse_glob_constr(body[0]), self.parse_cast_type(body[1]))
        else:
            raise NameError("Tag {} not supported.".format(tag))

    def parse_glob_constrs(self, gcs):
        return [self.parse_glob_constr(gc) for gc in gcs]

    def parse_cast_type(self, cty):
        # TODO(deh): change me
        return cty
