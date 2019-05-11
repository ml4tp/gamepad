# Copyright 2018 The GamePad Authors. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
# ==============================================================================

from lib.mysexpr import *
from lib.sexpdata import Bracket


"""
[Note]

Get the free variables in a tactic.

WARNING(deh): experimental
"""


class FvsTactic(object):
    def __init__(self):
        self.globs = set()

    def _log(self, msg):
        pass

    # -------------------------------------------------
    # utility

    def fvs_maybe(self, fvs, sexpr):
        tag, body = sexpr_unpack(sexpr)
        if tag == "N":
            return set()
        elif tag == "S":
            return fvs(body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_ls(self, fvs, ls):
        acc = set()
        for x in ls:
            acc = acc.union(fvs(x))
        return acc

    # -------------------------------------------------
    # glob_constr

    def fvs_or_var(self, fvs, ov):
        tag, body = sexpr_unpack(ov)
        if tag == "A":
            return fvs(body[0])
        elif tag == "V":
            return {sexpr_strify(body[0])}
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_g_reference(self, gref):
        return self.fvs_or_var(lambda x: {sexpr_strify(x)}, gref)

    def fvs_gname(self, gnm):
        return {sexpr_strify(gnm)}

    def fvs_intro_pattern_expr(self, fvs, ipe):
        tag, body = sexpr_unpack(ipe)
        self._log("@fvs_intro_pattern_expr | tag={}; raw={}".format(tag, body))

        if not body:
            return set()

        if tag == "F":
            return set()
        elif tag == "N":
            return self.fvs_intro_pattern_naming_expr(body[0])
        elif tag == "A":
            return self.fvs_intro_pattern_action_expr(fvs, body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_intro_pattern_naming_expr(self, ipne):
        tag, body = sexpr_unpack(ipne)
        self._log("@fvs_intro_pattern_naming_expr | tag={}; raw={}".format(tag, body))
        if tag == "I":
            return self.fvs_id(body[0])
        elif tag == "F":
            return self.fvs_id(body[0])
        elif tag == "A":
            return set()
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_intro_pattern_action_expr(self, fvs, ipae):
        tag, body = sexpr_unpack(ipae)
        self._log("@fvs_intro_pattern_action_expr | tag={}; raw={}".format(tag, body))
        if tag == "W":
            return set()
        elif tag == "O":
            return self.fvs_or_and_intro_pattern_expr(fvs, body[0])
        elif tag == "I":
            return self.fvs_ls(lambda x: self.fvs_intro_pattern_expr(fvs, x), body[0])
            # return self.fvs_or_and_intro_pattern_expr(fvs, body[0])
        elif tag == "A":
            fvs0 = fvs(body[0])
            fvs1 = self.fvs_intro_pattern_expr(fvs, body[1])
            return fvs0.union(fvs1)
        elif tag == "R":
            return set()
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_or_and_intro_pattern_expr(self, fvs, oaipe):
        tag, body = sexpr_unpack(oaipe)
        self._log("@fvs_or_and_intro_pattern_expr | tag={}; raw={}".format(tag, body))
        if tag == "I":
            return self.fvs_ls(lambda y: self.fvs_ls(lambda x: self.fvs_intro_pattern_expr(fvs, x), y), body[0])
            # return self.fvs_ls(lambda x: self.fvs_intro_pattern_expr(self.fvs_gtrm, x), body[0])
        elif tag == "A":
            # return self.fvs_ls(lambda y: self.fvs_ls(lambda x: self.fvs_intro_pattern_expr(fvs, x), y), body[0])
            return self.fvs_ls(lambda x: self.fvs_intro_pattern_expr(self.fvs_gtrm, x), body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_cases_pattern(self, cp):
        tag, body = sexpr_unpack(cp)
        if tag == "V":
            return self.fvs_name(body[0])
        elif tag == "C":
            self.globs.add(sexpr_strify(body[0]))
            fvs3 = self.fvs_ls(self.fvs_cases_pattern, body[3])
            fvs4 = self.fvs_name(body[4])
            return fvs3.union(fvs4)
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_cast_type(self, ct):
        tag, body = sexpr_unpack(ct)
        if tag == "C":
            return self.fvs_glob_constr(body[0])
        elif tag == "VM":
            return self.fvs_glob_constr(body[0])
        elif tag == "O":
            return set()
        elif tag == "N":
            return self.fvs_glob_constr(body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_glob_constr(self, gc):
        tag, body = sexpr_unpack(gc)
        self._log("@fvs_glob_constr | tag={}; raw={}".format(tag, gc))
        if tag == "!":
            return self.fvs_global_reference(body[0])
        elif tag == "V":
            return self.fvs_id(body[0])
        elif tag == "E":
            fvs0 = self.fvs_id(body[0])
            fvs1 = self.fvs_glob_constrs(body[1])
            return fvs0.union(fvs1)
        elif tag == "PV":
            return self.fvs_id(body[1])
        elif tag == "A":
            fvs0 = self.fvs_glob_constr(body[0])
            fvs1 = self.fvs_glob_constrs(body[1])
            return fvs0.union(fvs1)
        elif tag == "L":
            fvs1 = self.fvs_glob_constr(body[2])
            fvs2 = self.fvs_glob_constr(body[3])
            return fvs1.union(fvs2).difference(self.fvs_name(body[0]))
        elif tag == "P":
            fvs1 = self.fvs_glob_constr(body[2])
            fvs2 = self.fvs_glob_constr(body[3])
            return fvs1.union(fvs2).difference(self.fvs_name(body[0]))
        elif tag == "LI":
            fvs1 = self.fvs_glob_constr(body[1])
            fvs2 = self.fvs_glob_constr(body[2])
            return fvs1.union(fvs2).difference(self.fvs_name(body[0]))
        elif tag == "C":
            fvs0 = self.fvs_maybe(self.fvs_glob_constr, body[1])
            fvs1 = self.fvs_tomatch_tuples(body[2])
            fvs2 = self.fvs_case_clauses(body[3])
            return fvs0.union(fvs2).difference(fvs1)
        elif tag == "LT":
            bnd0 = self.fvs_ls(lambda x: sexpr_strify(x), body[0])
            fvs2 = self.fvs_glob_constr(body[2])
            fvs3 = self.fvs_glob_constr(body[3])
            return fvs2.union(fvs3.difference(bnd0))
        elif tag == "I":
            fvs0 = self.fvs_glob_constr(body[0])
            fvs2 = self.fvs_glob_constr(body[2])
            fvs3 = self.fvs_glob_constr(body[3])
            return fvs0.union(fvs2).union(fvs3)
        elif tag == "R":
            bnd = self.fvs_ls(self.fvs_id, body[1])
            fvs3 = self.fvs_glob_constrs(body[3])
            fvs4 = self.fvs_glob_constrs(body[4])
            return fvs3.union(fvs4).difference(bnd)
        elif tag == "S":
            return set()
        elif tag == "H":
            return self.fvs_intro_pattern_naming_expr(body[1])
        elif tag == "T":
            fvs0 = self.fvs_glob_constr(body[0])
            fvs1 = self.fvs_cast_type(body[1])
            return fvs0.union(fvs1)
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_glob_constrs(self, gcs):
        return self.fvs_ls(self.fvs_glob_constr, gcs)

    def fvs_gtrm(self, gtrm):
        return self.fvs_glob_constr(gtrm)

    def fvs_id(self, x):
        return {sexpr_strify(x)}

    def fvs_predicate_pattern(self, parg):
        fvs0 = {sexpr_strify(parg[0])}
        tag, body = sexpr_unpack(parg[1])
        if tag == "N":
            fvs1 = set()
        elif tag == "S":
            body = body[0]
            self.globs.add(sexpr_strify(body[0]))
            fvs1 = set(self.fvs_ls(self.fvs_id, body[2]))
        else:
            raise NameError("Tag {} not supported".format(tag))
        return fvs0.union(fvs1)

    def fvs_tomatch_tuple(self, tmt):
        fvs0 = self.fvs_glob_constr(tmt[0])
        fvs1 = self.fvs_predicate_pattern(tmt[1])
        return fvs0.union(fvs1)

    def fvs_tomatch_tuples(self, tmts):
        return self.fvs_ls(self.fvs_tomatch_tuple, tmts)

    def fvs_case_clause(self, cc):
        body = cc
        fvs0 = self.fvs_ls(self.fvs_id, body[0])
        fvs1 = self.fvs_ls(self.fvs_cases_pattern, body[1])
        fvs2 = self.fvs_glob_constr(body[2])
        return fvs0.union(fvs1).union(fvs2)

    def fvs_case_clauses(self, ccs):
        return self.fvs_ls(self.fvs_case_clause, ccs)

    # -------------------------------------------------
    # Tactics

    def fvs_occurrences_gen(self, fvs, og):
        tag, body = sexpr_unpack(og)
        if tag == "A":
            return set()
        elif tag == "B":
            return self.fvs_ls(fvs, body[0])
        elif tag == "N":
            return set()
        elif tag == "O":
            return self.fvs_ls(fvs, body[0])

    def fvs_occurrences_expr(self, oe):
        return set()

    def fvs_with_occurrences(self, fvs, woccs):
        fvs0 = self.fvs_occurrences_expr(woccs[0])
        fvs1 = fvs(woccs[1])
        return fvs0.union(fvs1)

    def fvs_hyp_location_expr(self, hle):
        fvs0 = self.fvs_occurrences_expr(hle[0])
        fvs1 = self.fvs_gname(hle[1])
        return fvs0.union(fvs1)

    def fvs_clause_expr(self, ce):
        fvs0 = self.fvs_maybe(lambda x: self.fvs_ls(self.fvs_hyp_location_expr, x), ce[0])
        fvs1 = self.fvs_occurrences_expr(ce[1])
        return fvs0.union(fvs1)

    def fvs_quantified_hypothesis(self, qhyp):
        return {sexpr_strify(qhyp)}

    def fvs_explicit_binding(self, fvs, eb):
        fvs0 = self.fvs_quantified_hypothesis(eb[0])
        fvs1 = fvs(eb[1])
        return fvs0.union(fvs1)

    def fvs_bindings(self, fvs, b):
        tag, body = sexpr_unpack(b)
        if tag == "I":
            return self.fvs_ls(fvs, body[0])
        elif tag == "E":
            return self.fvs_ls(lambda x: self.fvs_explicit_binding(fvs, x), body[0])
        elif tag == "N":
            return set()
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_with_bindings(self, fvs, b):
        fvs0 = fvs(b[0])
        fvs1 = self.fvs_bindings(fvs, b[1])
        return fvs0.union(fvs1)

    def fvs_with_bindings_arg(self, fvs, ba):
        return self.fvs_with_bindings(fvs, ba[1])

    def fvs_global_reference(self, gref):
        tag, body = sexpr_unpack(gref)
        if tag == "VR":
            self.globs.add(sexpr_strify(body[0]))
        elif tag == "CR":
            self.globs.add(sexpr_strify(body[0]))
        elif tag == "IR":
            self.globs.add(sexpr_strify(body[0]))
        elif tag == "TR":
            self.globs.add(sexpr_strify(body[0]))
        else:
            raise NameError("Tag {} not supported".format(tag))
        return set()

    def fvs_match_rule(self, fvs_pat, fvs_tac, mrule):
        tag, body = sexpr_unpack(mrule)
        if tag == "P":
            fvs0 = self.fvs_ls(lambda x: self.fvs_match_context_hyps(fvs_pat, x), body[0])
            fvs1 = self.fvs_match_pattern(fvs_pat, body[1])
            fvs2 = fvs_tac(body[2])
            return fvs0.union(fvs1).union(fvs2)
        elif tag == "A":
            return fvs_tac(body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_match_rules(self, fvs_pat, fvs_tac, mrules):
        return self.fvs_ls(lambda x: self.fvs_match_rule(fvs_pat, fvs_tac, x), mrules)

    def fvs_match_pattern(self, fvs_pat, mp):
        tag, body = sexpr_unpack(mp)
        if tag == "T":
            return fvs_pat(body[0])
        elif tag == "S":
            fvs1 = self.fvs_maybe(self.fvs_id, body[1])
            fvs2 = fvs_pat(body[2])
            return fvs1.union(fvs2)
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_match_context_hyps(self, fvs_pat, hyps):
        tag, body = sexpr_unpack(hyps)
        if tag == "H":
            fvs0 = {sexpr_strify(body[0])}
            fvs1 = self.fvs_match_pattern(fvs_pat, body[1])
            return fvs0.union(fvs1)
        elif tag == "D":
            fvs0 = {sexpr_strify(body[0])}
            fvs1 = self.fvs_match_pattern(fvs_pat, body[1])
            fvs2 = self.fvs_match_pattern(fvs_pat, body[2])
            return fvs0.union(fvs1).union(fvs2)
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_message_token(self, mtok):
        tag, body = sexpr_unpack(mtok)
        if tag == "S":
            return set()
        elif tag == "I":
            return set()
        elif tag == "D":
            return self.fvs_gname(body[0])

    def fvs_generic_arg(self, garg):
        tag, body = sexpr_unpack(garg)
        self._log("@fvs_generic_arg | tag={}; raw={}".format(tag, garg))
        if tag == "L":
            return self.fvs_ls(self.fvs_generic_arg, body[0])
        elif tag == "O":
            return self.fvs_maybe(self.fvs_generic_arg, body[0])
        elif tag == "P":
            fvs0 = self.fvs_generic_arg(body[0])
            fvs1 = self.fvs_generic_arg(body[1])
            return fvs0.union(fvs1)
        elif tag == "E":
            method = getattr(self, "fvs_{}".format(sexpr_strify(body[0])))
            return method(body[1])
        else:
            return set()
            # if (tag == "auto_using" or
            #     tag == "hintbases" or
            #     tag == "bindings" or
            #     tag == "intropattern" or
            #     tag == "constr" or       # NOTE(deh): huh??
            #     tag == "uconstr" or
            #     tag == "casted_constr" or
            #     tag == "natural" or
            #     tag == "var" or
            #     tag == "int_or_var" or
            #     tag == "ident" or
            #     tag == "preident" or
            #     tag == "clause_dft_concl" or
            #     tag == "by_arg_tac" or
            #     tag == "firstorder_using" or
            #     tag == "tactic" or
            #     tag == "destruction_arg" or
            #     tag == "constr_with_bindings" or
            #     tag == "rename" or
            #     tag == "quant_hyp" or
            #     tag == "orient" or
            #     tag == "glob_constr_with_bindings" or
            #     tag == "in_clause" or
            #     tag == "fun_ind_using" or
            #     tag == "with_names"):
            #     return set()
            # else:
            #     raise NameError("Tag {} not supported".format(tag))

    def fvs_may_eval(self, me):
        tag, body = sexpr_unpack(me)
        self._log("@fvs_may_eval | tag={}; raw={}".format(tag, me))
        if tag == "E":
            return self.fvs_gtrm(body[1])
        elif tag == "C":
            return self.fvs_id(body[0]).union(self.fvs_gtrm(body[1]))
        elif tag == "T":
            return self.fvs_gtrm(body[0])
        elif tag == "M":
            return self.fvs_gtrm(body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_tactic_arg(self, targ):
        tag, body = sexpr_unpack(targ)
        self._log("@fvs_tactic_arg | tag={}; raw={}".format(tag, targ))
        if tag == "G":
            return self.fvs_generic_arg(body[0])
        elif tag == "ME":
            return self.fvs_may_eval(body[0])
        elif tag == "R":
            return self.fvs_g_reference(body[0])
        elif tag == "C":
            fvs0 = self.fvs_g_reference(body[0])
            fvs1 = self.fvs_tactic_args(body[1])
            return fvs0.union(fvs1)
        elif tag == "F":
            return self.fvs_ls(lambda x: self.fvs_or_var(lambda y: {sexpr_strify(y)}, x), body[0])
        elif tag == "E":
            return self.fvs_tac(body[0])
        elif tag == "P":
            return self.fvs_gtrm(body[0])
        elif tag == "N":
            return set()
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_tactic_args(self, targs):
        return self.fvs_ls(self.fvs_tactic_arg, targs)

    def fvs_core_destruction_arg(self, f, cda):
        tag, body = sexpr_unpack(cda)
        if tag == "C":
            return f(body[0])
        elif tag == "I":
            return self.fvs_id(body[0])
        elif tag == "A":
            return set()
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_destruction_arg(self, f, da):
        return self.fvs_core_destruction_arg(f, da[1])

    def fvs_induction_clause(self, ic):
        fvs0 = self.fvs_destruction_arg(lambda x: self.fvs_with_bindings(self.fvs_gtrm, x), ic[0])
        fvs1 = self.fvs_maybe(self.fvs_intro_pattern_naming_expr, ic[1])
        fvs2 = self.fvs_maybe(lambda x: self.fvs_or_var(lambda y: self.fvs_or_and_intro_pattern_expr(self.fvs_gtrm, y), x), ic[2])
        fvs3 = self.fvs_maybe(self.fvs_clause_expr, ic[3])
        return fvs0.union(fvs1).union(fvs2).union(fvs3)

    def fvs_induction_clause_list(self, ics):
        fvs0 = self.fvs_ls(self.fvs_induction_clause, ics[0])
        fvs1 = self.fvs_maybe(lambda x: self.fvs_with_bindings(self.fvs_gtrm, x), ics[1])
        return fvs0.union(fvs1)

    def fvs_atomic_tac(self, atac):
        tag, body = sexpr_unpack(atac)
        self._log("@fvs_atomic_tac | tag={}; raw={}".format(tag, atac))
        if tag == "IntroPattern":
            return self.fvs_ls(lambda x: self.fvs_intro_pattern_expr(self.fvs_gtrm, x), body[1])
        elif tag == "Apply":
            fvs2 = self.fvs_ls(lambda x: self.fvs_with_bindings_arg(self.fvs_gtrm, x), body[2])
            fvs3 = self.fvs_maybe(lambda x: self.fvs_gname(x[0]).union(
                self.fvs_maybe(lambda y: self.fvs_intro_pattern_expr(self.fvs_gtrm, y), x[1])), body[3])
            return fvs2.union(fvs3)
        elif tag == "Elim":
            fvs1 = self.fvs_with_bindings_arg(self.fvs_gtrm, body[1])
            fvs2 = self.fvs_maybe(lambda x: self.fvs_with_bindings(self.fvs_gtrm, x), body[2])
            return fvs1.union(fvs2)
        elif tag == "Case":
            return self.fvs_with_bindings_arg(self.fvs_gtrm, body[1])
        elif tag == "MutualFix":
            fvs1 = set([self.fvs_gtrm(c) for x, i, c in body[1]])
            ids = set([x[0] for x in body[1]])
            return fvs1.difference(ids)
        elif tag == "MutualCofix":
            fvs1 = set([self.fvs_gtrm(c) for x, c in body[1]])
            ids = set([x[0] for x in body[1]])
            return fvs1.difference(ids)
        elif tag == "Assert":
            fvs1 = self.fvs_maybe(lambda x: self.fvs_maybe(self.fvs_tac, x), body[1])
            fvs2 = self.fvs_maybe(lambda x: self.fvs_intro_pattern_expr(self.fvs_gtrm, x), body[2])
            fvs3 = self.fvs_gtrm(body[3])
            return fvs1.union(fvs2).union(fvs3)
        elif tag == "Generalize":
            return self.fvs_ls(lambda x: self.fvs_with_occurrences(
                self.fvs_gtrm, x[0]).union(self.fvs_name(x[1])), body[0])
        elif tag == "LetTac":
            fvs1 = self.fvs_gtrm(body[1])
            fvs2 = self.fvs_clause_expr(body[2])
            fvs3 = self.fvs_maybe(self.fvs_gtrm, body[4])
            return fvs1.union(fvs2).union(fvs3).difference(self.fvs_name(body[0]))
        elif tag == "InductionDestruct":
            return self.fvs_induction_clause_list(body[2])
        elif tag == "Reduce":
            return self.fvs_clause_expr(body[1])
        elif tag == "Change":
            # fvs0 = self.fvs_maybe(self.fvs_pattern, body[0])
            fvs0 = self.fvs_maybe(self.fvs_gtrm, body[0])
            fvs1 = self.fvs_gtrm(body[1])
            fvs2 = self.fvs_clause_expr(body[2])
            return fvs0.union(fvs1).union(fvs2)
        elif tag == "Rewrite":
            fvs1 = self.fvs_ls(lambda x: self.fvs_with_bindings_arg(self.fvs_gtrm, x[2]), body[1])
            fvs2 = self.fvs_clause_expr(body[2])
            fvs3 = self.fvs_maybe(self.fvs_tac, body[3])
            return fvs1.union(fvs2).union(fvs3)
        elif tag == "Inversion":
            return self.fvs_quantified_hypothesis(body[1])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_tac(self, tac):
        if tac is None:
            return set()
        tag, body = sexpr_unpack(tac)
        self._log("@fvs_tac | tag={}; raw={}".format(tag, tac))
        if tag == "Atom":
            return self.fvs_atomic_tac(body[0])
        elif tag == "Then":
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tac(body[1])
            return fvs0.union(fvs1)
        elif tag == "Dispatch":
            return self.fvs_tacs(body[0])
        elif tag == "ExtendTac":
            fvs0 = self.fvs_tacs(body[0])
            fvs1 = self.fvs_tac(body[1])
            fvs2 = self.fvs_tacs(body[0])
            return fvs0.union(fvs1).union(fvs2)
        elif tag == "Thens":
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tacs(body[1])
            return fvs0.union(fvs1)
        elif tag == "Thens3parts":
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tacs(body[1])
            fvs2 = self.fvs_tac(body[2])
            fvs3 = self.fvs_tacs(body[3])
            return fvs0.union(fvs1).union(fvs2).union(fvs3)
        elif tag == "First":
            return self.fvs_tacs(body[0])
        elif tag == "Complete":
            return self.fvs_tac(body[0])
        elif tag == "Solve":
            return self.fvs_tacs(body[0])
        elif tag == "Try":
            return self.fvs_tac(body[0])
        elif tag == "Or":
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tac(body[1])
            return self.fvs_tac(fvs0).union(fvs1)
        elif tag == "Once":
            return self.fvs_tac(body[0])
        elif tag == "ExactlyOnce":
            return self.fvs_tac(body[0])
        elif tag == "IfThenCatch":
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tac(body[1])
            fvs2 = self.fvs_tac(body[2])
            return fvs0.union(fvs1).union(fvs2)
        elif tag == "Orelse":
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tac(body[1])
            return fvs0.union(fvs1)
        elif tag == "Do":
            return self.fvs_tac(body[1])
        elif tag == "Timeout":
            return self.fvs_tac(body[1])
        elif tag == "Time":
            return self.fvs_tac(body[1])
        elif tag == "Repeat":
            return self.fvs_tac(body[0])
        elif tag == "Progress":
            return self.fvs_tac(body[0])
        elif tag == "ShowHyps":
            return self.fvs_tac(body[0])
        elif tag == "Abstract":
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_maybe(self.fvs_id, body[1])
            return fvs0.union(fvs1)
        elif tag == "Id":
            return self.fvs_ls(self.fvs_message_token, body[0])
        elif tag == "Fail":
            return set()
        elif tag == "Info":
            return self.fvs_tac(body[0])
        elif tag == "Let":
            bnd = self.fvs_ls(lambda x: self.fvs_id(x[0]), body[1])
            fvs1 = self.fvs_ls(lambda x: self.fvs_tactic_arg(x[1]), body[1])
            fvs2 = self.fvs_tac(body[2])
            return fvs1.union(fvs2.difference(bnd))
        elif tag == "Match":
            fvs1 = self.fvs_tac(body[1])
            fvs2 = self.fvs_match_rules(lambda x: self.fvs_gtrm(x[1]), self.fvs_tac, body[2])
            return fvs1.union(fvs2)
        elif tag == "MatchGoal":
            return self.fvs_match_rules(lambda x: self.fvs_gtrm(x[1]), self.fvs_tac, body[2])
        elif tag == "Fun":
            bnd0 = self.fvs_ls(lambda x: self.fvs_maybe(self.fvs_id, x), body[0])
            fvs1 = self.fvs_tac(body[1])
            return fvs1.difference(bnd0)
        elif tag == "Arg":
            return self.fvs_tactic_arg(body[0])
        elif tag == "Select":
            fvs2 = self.fvs_tac(body[1])
            return fvs2
        elif tag == "ML":
            return self.fvs_tactic_args(body[1])
        elif tag == "Alias":
            # TODO(deh): should sanitize on TCoq side
            # Some aliases have parentheses in them so it messes up sexpressions
            # Some aliases also have brackets which also messed up sexpression parsing
            if sexpr_strify(body[0]).find(".evar_") == -1 and not isinstance(body[1], Bracket):
                return self.fvs_tactic_args(body[1])
            else:
                return set()
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_tacs(self, tacs):
        return self.fvs_ls(self.fvs_tac, tacs)

    # -------------------------------------------------
    # Ssreflect tactics

    def fvs_cpattern(self, cpat):
        return self.fvs_glob_constr(cpat)

    def fvs_pattern(self, pat):
        tag, body = sexpr_unpack(pat)
        self._log("@fvs_pattern | tag={}; raw={}".format(tag, pat))
        if tag == "T":
            return self.fvs_term(body[0])
        elif tag == "A":
            # TODO(deh): Not sure about this case
            return set()
        elif tag == "IT":
            return self.fvs_term(body[0])
        elif tag == "XT":
            fvs0 = self.fvs_term(body[0])
            fvs1 = self.fvs_term(body[1])
            return fvs0.union(fvs1)
        elif tag == "IXT":
            fvs0 = self.fvs_term(body[0])
            fvs1 = self.fvs_term(body[1])
            return fvs0.union(fvs1)
        elif tag == "EIXT":
            fvs0 = self.fvs_term(body[0])
            fvs1 = self.fvs_term(body[1])
            fvs2 = self.fvs_term(body[2])
            return fvs0.union(fvs1).union(fvs2)
        elif tag == "EAXT":
            fvs0 = self.fvs_term(body[0])
            fvs1 = self.fvs_term(body[1])
            fvs2 = self.fvs_term(body[2])
            return fvs0.union(fvs1).union(fvs2)
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_rpattern(self, rpat):
        return self.fvs_pattern(rpat)

    def fvs_term(self, term):
        return self.fvs_glob_constr(term)

    # -------------------------------------------------
    # Ssreflect tactics

    def fvs_ssrortacs(self, ortacs):
        return self.fvs_ls(lambda x: self.fvs_maybe(self.fvs_tac, x), ortacs)

    def fvs_ssrhintarg(self, ha):
        return self.fvs_ssrortacs(ha[1])

    def fvs_ssrhyp(self, hyp):
        return self.fvs_id(hyp)

    def fvs_ssrhyprep(self, hyp):
        return self.fvs_id(hyp)

    def fvs_ssrhoirep(self, hoirep):
        tag, body = sexpr_unpack(hoirep)
        if tag == "H":
            return self.fvs_ssrhyp(body[0])
        elif tag == "I":
            return self.fvs_ssrhyp(body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_ssrhoi_hyp(self, hoi_hyp):
        return self.fvs_ssrhoirep(hoi_hyp)

    def fvs_ssrhoi_id(self, hoi_id):
        return self.fvs_ssrhoirep(hoi_id)

    def fvs_ssrhyps(self, hyps):
        return self.fvs_ls(self.fvs_ssrhyp, hyps)

    def fvs_ssrclear(self, clr):
        return self.fvs_ssrhyps(clr)

    def fvs_ssrwgen(self, wgen):
        def f(x):
            fvs1_p = self.fvs_ssrhoirep(x[0])
            fvs2_p = self.fvs_maybe(self.fvs_cpattern, x[1])
            return fvs1_p.union(fvs2_p)
        fvs0 = self.fvs_ssrclear(wgen[0])
        fvs1 = self.fvs_maybe(f, wgen[1])
        return fvs0.union(fvs1)

    def fvs_ssrclseq(self, clseq):
        return set()

    def fvs_ssrclausehyps(self, chyps):
        return self.fvs_ls(self.fvs_ssrwgen, chyps)

    def fvs_ssrclauses(self, clauses):
        fvs0 = self.fvs_ssrclausehyps(clauses[0])
        fvs1 = self.fvs_ssrclseq(clauses[1])
        return fvs0.union(fvs1)

    def fvs_ssrsimpl(self, simp):
        return set()

    def fvs_ssrsimplrep(self, simp):
        return self.fvs_ssrsimpl(simp)

    def fvs_ssrsimpl_ne(self, simp):
        return self.fvs_ssrsimpl(simp)        

    def fvs_ssrocc(self, occ):
        return set()

    def fvs_ssrdocc(self, docc):
        tag, body = sexpr_unpack(docc)
        if tag == "N":
            return self.fvs_ssrocc(body[0])
        elif tag == "S":
            return self.fvs_ssrclear(body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_ssrview(self, view):
        return self.fvs_ls(self.fvs_glob_constr, view)

    def fvs_ssripat(self, ipat):
        tag, body = sexpr_unpack(ipat)
        if tag == "I":
            return self.fvs_id(body[0])
        elif tag == "S":
            fvs0 = self.fvs_ssrclear(body[0])
            fvs1 = self.fvs_ssrsimpl(body[1])
            return fvs0.union(fvs1)
        elif tag == "C":
            return self.fvs_ssriorpat(body[0])
        elif tag == "R":
            return self.fvs_ssrocc(body[0])
        elif tag == "A":
            return set()
        elif tag == "W":
            return set()
        elif tag == "AN":
            return set()
        elif tag == "V":
            return set()
        elif tag == "N":
            return set()
        elif tag == "H":
            return set()
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_ssripats(self, ipats):
        return self.fvs_ls(self.fvs_ssripat, ipats)

    def fvs_ssriorpat(self, iorpat):
        return self.fvs_ls(self.fvs_ssripats, iorpat)

    def fvs_ssripatrep(self, ipatrep):
        return self.fvs_ssripat(ipatrep)

    def fvs_ssrhpats(self, hpats):
        fvs0 = self.fvs_ssrclear(hpats[0])
        fvs1 = self.fvs_ssripats(hpats[1])
        fvs2 = self.fvs_ssripats(hpats[2])
        fvs3 = self.fvs_ssripats(hpats[3])
        return fvs0.union(fvs1).union(fvs2).union(fvs3)

    def fvs_ssrintros(self, intros):
        return self.fvs_ssripats(intros)

    def fvs_ssrintros_ne(self, intros):
        return self.fvs_ssrintros(intros)

    def fvs_ssrmmod(self, mmod):
        return set()

    def fvs_ssrgen(self, gen):
        fvs0 = self.fvs_ssrdocc(gen[0])
        fvs1 = self.fvs_cpattern(gen[1])
        return fvs0.union(fvs1)

    def fvs_dgens(self, fvs, dgens):
        fvs0 = self.fvs_ls(fvs, dgens[0])
        fvs1 = self.fvs_ls(fvs, dgens[1])
        fvs2 = self.fvs_ssrclear(dgens[2])
        return fvs0.union(fvs1).union(fvs2)

    def fvs_ssrdgens(self, dgens):
        return self.fvs_dgens(self.fvs_ssrgen, dgens)

    def fvs_ssrdgens_tl(self, fvs, dgens):
        return self.fvs_dgens(self.fvs_ssrgen, dgens)

    def fvs_ssreqid(self, eqid):
        return self.fvs_maybe(self.fvs_ssripat, eqid)

    def fvs_ssrarg(self, arg):
        fvs0 = self.fvs_ssrview(arg[0])
        fvs1 = self.fvs_ssreqid(arg[1])
        fvs2 = self.fvs_ssrdgens(arg[2])
        fvs3 = self.fvs_ssrintros(arg[3])
        return fvs0.union(fvs1).union(fvs2).union(fvs3)

    def fvs_ssrmovearg(self, movearg):
        return self.fvs_ssrarg(movearg)

    def fvs_ssrcasearg(self, casearg):
        return self.fvs_ssrarg(casearg)

    def fvs_ssragen(self, agen):
        fvs0 = self.fvs_ssrdocc(agen[0])
        fvs1 = self.fvs_term(agen[1])
        return fvs0.union(fvs1)

    def fvs_ssragens(self, agens):
        return self.fvs_dgens(self.fvs_ssragen, agens)

    def fvs_ssrapplyarg(self, aa):
        fvs0 = self.fvs_ssrview(aa[0])
        fvs1 = self.fvs_ssreqid(aa[1])
        fvs2 = self.fvs_ssragens(aa[2])
        fvs3 = self.fvs_ssripats(aa[3])
        return fvs0.union(fvs1).union(fvs2).union(fvs3)

    def fvs_ssrmult(self, mult):
        return set()

    def fvs_ssrmult_ne(self, mult):
        return self.fvs_ssrmult(mult)

    def fvs_ssrrwocc(self, rwocc):
        fvs0 = self.fvs_maybe(self.fvs_ssrclear, rwocc[0])
        fvs1 = self.fvs_ssrocc(rwocc[1])
        return fvs0.union(fvs1)

    def fvs_ssrrule(self, rule):
        tag, body = sexpr_unpack(rule)
        if tag == "R":
            return self.fvs_ssrsimpl(body[0])
        elif tag == "D":
            return self.fvs_term(body[0])
        elif tag == "E":
            return self.fvs_term(body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_ssrpattern_squarep(self, pat):
        return self.fvs_maybe(self.fvs_rpattern, pat)

    def fvs_ssrpattern_ne_squarep(self, pat):
        return self.fvs_ssrpattern_squarep(pat)

    def fvs_ssrrwarg(self, rwarg):
        fvs2 = self.fvs_ssrrwocc(rwarg[2])
        fvs3 = self.fvs_ssrpattern_squarep(rwarg[3])
        fvs4 = self.fvs_ssrrule(rwarg[4])
        return fvs2.union(fvs3).union(fvs4)

    def fvs_ssrrwargs(self, rwargs):
        return self.fvs_ls(self.fvs_ssrrwarg, rwargs)

    def fvs_ssrfwdid(self, fwdid):
        return {sexpr_strify(fwdid)}

    def fvs_name(self, name):
        return {sexpr_strify(name)}

    def fvs_binder(self, b):
        tag, body = sexpr_unpack(b)
        if tag == "V":
            return self.fvs_name(body[0])
        elif tag == "DC":
            fvs0 = self.fvs_ls(self.fvs_name, body[0])
            fvs1 = self.fvs_glob_constr(body[1])
            return fvs0.union(fvs1)
        elif tag == "Df":
            fvs0 = self.fvs_name(body[0])
            fvs1 = self.fvs_maybe(self.fvs_glob_constr, body[1])
            fvs2 = self.fvs_glob_constr(body[2])
            return fvs0.union(fvs1).union(fvs2)
        elif tag == "S":
            return self.fvs_name(body[0])
        elif tag == "C":
            return self.fvs_glob_constr(body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_ssrgen_fwd(self, fwd):
        fvs1 = self.fvs_ls(self.fvs_binder, fwd[1])
        fvs2 = self.fvs_glob_constr(fwd[2])
        return fvs1.union(fvs2)

    def fvs_ssrfwd(self, fwd):
        return self.fvs_ssrgen_fwd(fwd[1])

    def fvs_ssrposefwd(self, posefwd):
        return self.fvs_ssrfwd(posefwd)

    def fvs_ssrhavefwd(self, fwd):
        fvs0 = self.fvs_ssrfwd(fwd[0])
        fvs1 = self.fvs_ssrhint(fwd[1])
        return fvs0.union(fvs1)

    def fvs_ssrhavefwdwbinders(self, hfwb):
        fvs0 = self.fvs_ssrhpats(hfwb[0])
        fvs1 = self.fvs_ssrfwd(hfwb[1])
        return fvs0.union(fvs1)

    def fvs_ssrhint(self, hint):
        return self.fvs_ssrhintarg(hint)

    def fvs_ssrexactarg(self, ea):
        return self.fvs_ssrapplyarg(ea)

    def fvs_ssrdoarg(self, da):
        fvs1 = self.fvs_ssrmmod(da[1])
        fvs2 = self.fvs_ssrhintarg(da[2])
        fvs3 = self.fvs_ssrclauses(da[3])
        return fvs1.union(fvs2).union(fvs3)

    def fvs_ssrintrosarg(self, ia):
        fvs0 = self.fvs_tac(ia[0])
        fvs1 = self.fvs_ssripats(ia[1])
        return fvs0.union(fvs1)

    def fvs_ssrcongrarg(self, ca):
        fvs0 = self.fvs_term(ca[1])
        fvs1 = self.fvs_dgens(self.fvs_ssrgen, ca[2])
        return fvs0.union(fvs1)

    def fvs_ssrseqarg(self, sa):
        fvs1 = self.fvs_ssrhintarg(sa[1])
        fvs2 = self.fvs_maybe(self.fvs_tac, sa[2])
        return fvs1.union(fvs2)

    def fvs_ssrtclarg(self, ta):
        return self.fvs_tac(ta)

    def fvs_ssrhpats_nobs(self, hpats):
        return self.fvs_ssrhpats(hpats)

    def fvs_ssrwlogfwd(self, fwd):
        fvs0 = self.fvs_ls(self.fvs_ssrwgen, fwd[0])
        fvs1 = self.fvs_ssrfwd(fwd[1])
        return fvs0.union(fvs1)

    def fvs_ssrsufffwd(self, fwd):
        fvs0 = self.fvs_ssrhpats(fwd[0])
        fvs1 = self.fvs_ssrfwd(fwd[1])
        fvs2 = self.fvs_ssrhint(fwd[2])
        return fvs0.union(fvs1).union(fvs2)

    def fvs_ssrsetfwd(self, fwd):
        fvs1 = self.fvs_cpattern(fwd[1])
        fvs2 = self.fvs_maybe(self.fvs_term, fwd[2])
        fvs3 = self.fvs_ssrdocc(fwd[3])
        return fvs1.union(fvs2).union(fvs3)

    def fvs_ssrseqdir(self, sd):
        return set()

    def fvs_ssrrpat(self, rpat):
        return self.fvs_ssripat(rpat)

    def fvs_ssrfixfwd(self, fwd):
        # NOTE(deh): huh?
        return set()
