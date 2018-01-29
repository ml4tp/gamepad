import sexpdata

class FvsTactic(object):
    def __init__(self):
        self.globs = set()

    def _log(self, msg):
        # print(msg)
        pass

    def _unpack(self, sexpr):
        try:
            tag = sexpr[0]
            body = sexpr[1:]
            return tag._val, body
        except:
            return sexpr._val, None

    def _conv(self, obj):
        if isinstance(obj, sexpdata.Symbol):
            return obj._val
        elif isinstance(obj, float):
            # NOTE(deh): wtf, inF -> inf the floating point ...
            return str(obj)

    # -------------------------------------------------
    # utility

    def fvs_maybe(self, fvs, sexpr):
        tag, body = self._unpack(sexpr)
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
        tag, body = self._unpack(ov)
        if tag == "A":
            return fvs(body[0])
        elif tag == "V":
            return set([self._conv(body[0])])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_g_reference(self, gref):
        return self.fvs_or_var(lambda x: set([self._conv(x)]), gref)

    def fvs_gname(self, gnm):
        return set([self._conv(gnm)])

    def fvs_intro_pattern_expr(self, fvs, ipe):
        tag, body = self._unpack(ipe)
        self._log("@fvs_intro_pattern_expr | tag={}; raw={}".format(tag, ipe))
        if tag == "F":
            # Printf.sprintf "F(%b)" b
            return set()
        elif tag == "N":
            # Printf.sprintf "N(%s)" (show_intro_pattern_naming_expr ipne)
            return self.fvs_intro_pattern_naming_expr(body[0])
        elif tag == "A":
            # Printf.sprintf "A(%s)" (show_intro_pattern_action_expr show ipae)
            return self.fvs_intro_pattern_action_expr(fvs, body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_intro_pattern_naming_expr(self, ipne):
        tag, body = self._unpack(ipne)
        self._log("@fvs_intro_pattern_naming_expr | tag={}; raw={}".format(tag, ipne))
        if tag == "I":
            # Printf.sprintf "I(%s)" (show_id id)
            return set([self._conv(body[0])])
        elif tag == "F":
            # Printf.sprintf "F(%s)" (show_id id)
            return set([self._conv(body[0])])
        elif tag == "A":
            # "A()"
            return set()
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_intro_pattern_action_expr(self, fvs, ipae):
        tag, body = self._unpack(ipae)
        
        if tag == "W":
            # "W()"
            return set()
        elif tag == "O":
            # Printf.sprintf "O(%s)" (show_or_and_intro_pattern_expr show oaipe)
            return self.fvs_or_and_intro_pattern_expr(body[0])
        elif tag == "I":
            # Printf.sprintf "I(%s)" (brackets (show_ls (fun (loc, ipe) -> show_intro_pattern_expr show ipe) ", " ls))
            return self.fvs_or_and_intro_pattern_expr(body[0])
        elif tag == "A":
            # Printf.sprintf "A(%s, %s)" (show a) (show_intro_pattern_expr show ipe)
            fvs0 = fvs(body[0])
            fvs1 = self.fvs_intro_pattern_expr(fvs, body[1])
            return fvs0.union(fvs1)
        elif tag == "R":
            # Printf.sprintf "R(%b)" b
            return set()
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_or_and_intro_pattern_expr(self, fvs, oaipe):
        tag, body = self._unpack(oaipe)
        if tag == "I":
            # Printf.sprintf "I(%s)" (brackets (show_ls (fun ls' -> brackets (show_ls (fun (loc, ipe) -> show_intro_pattern_expr show ipe) ", " ls')) ", " ls))
            return self.fvs_ls(self.fvs_intro_pattern_expr, body[0])
        elif tag == "A":
            # Printf.sprintf "A(%s)" (brackets (show_ls (fun (loc, ipe) -> show_intro_pattern_expr show ipe) ", " ls))
            return self.fvs_ls(show_intro_pattern_expr, body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_cases_pattern(self, cp):
        tag, body = self._unpack(cp)
        if tag == "V":
            # Printf.sprintf "V(%s)" (show_name n)
            return set([self._conv(body[0])])
        elif tag == "C":
            # Printf.sprintf "C(%s, %d, %d, %s, %s)" (Names.MutInd.to_string mutind) i j (brackets (show_ls show_cases_pattern ", " cps)) (show_name n)
            self.globs.add(self._conv(body[0]))
            fvs3 = self.fvs_ls(self.fvs_cases_pattern, body[3])
            fvs4 = set([self._conv(body[4])])
            return fvs3.union(fvs4)
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_cast_type(self, ct):
        tag, body = self._unpack(ct)
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
        tag, body = self._unpack(gc)
        self._log("@fvs_glob_constr | tag={}; raw={}".format(tag, gc))
        if tag == "!":
            # Printf.sprintf "!(%s)" (show_global_reference gr)
            return self.fvs_global_reference(body[0])
        elif tag == "V":
            # Printf.sprintf "V(%s)" (show_id id)
            return set([self._conv(body[0])])
        elif tag == "E":
            # let f (id, gc) = Printf.sprintf "(%s, %s)" (show_id id) (show_glob_constr gc) in
            # Printf.sprintf "E(%s, %s)" (show_id en) (brackets (show_ls f ", " args))
            # return self.fvs_id(body[0]), self.fvs_ls(lambda x, gc: (self.fvs_id(x), self.fvs_glob_constr(gc)), body[1]))
            raise NameError("TODO")
        elif tag == "PV":
            # Printf.sprintf "PV(%b, %s)" b (show_id pv)
            return set([self._conv(body[1])])
        elif tag == "A":
            # Printf.sprintf "A(%s, %s)" (show_glob_constr gc) (show_glob_constrs gcs)
            fvs0 = self.fvs_glob_constr(body[0])
            fvs1 = self.fvs_glob_constrs(body[1])
            return fvs0.union(fvs1)
        elif tag == "L":
            # Printf.sprintf "L(%s, %s, %s)" (show_name n) (show_glob_constr gc1) (show_glob_constr gc2)
            fvs1 = self.fvs_glob_constr(body[1])
            fvs2 = self.fvs_glob_constr(body[2])
            return fvs1.union(fvs2).difference(set([self._conv(body[0])]))
        elif tag == "LI":
            # Printf.sprintf "LI(%s, %s, %s)" (show_name n) (show_glob_constr gc1) (show_glob_constr gc2)
            fvs1 = self.fvs_glob_constr(body[1])
            fvs2 = self.fvs_glob_constr(body[2])
            return fvs1.union(fvs2).difference(set([self._conv(body[0])]))
        elif tag == "C":
            # Printf.sprintf "C(%s, %s, %s, %s)" "TODO" (show_maybe show_glob_constr m_gc) (show_tomatch_tuples tups) (show_case_clauses ccs)
            fvs0 = self.fvs_maybe(self.fvs_glob_constr, body[1])
            fvs1 = self.fvs_tomatch_tuples(body[2])
            fvs2 = self.fvs_case_clauses(body[3])
            return fvs0.union(fvs2).difference(fvs1)
        elif tag == "LT":
            # let f (name, m_gc) = Printf.sprintf "(%s, %s)" (show_name name) (show_maybe show_glob_constr m_gc) in
            # Printf.sprintf "LT(%s, %s, %s, %s)" (show_ls show_name ", " ns) (f arg) (show_glob_constr gc1) (show_glob_constr gc2)
            # return ("C", "TODO", self.fvs_maybe(self.fvs_glob_constr, body[0]), self.fvs_tomatch_tuples(body[1]), self.fvs_case_clauses(body[2]))
            raise NameError("TODO")
        elif tag == "I":
            # Printf.sprintf "I(%s, %s, %s)" (show_glob_constr gc) (show_glob_constr gc2) (show_glob_constr gc3)
            # return ("I", self.fvs_glob_constr(body[0]), self.fvs_glob_constr(body[1]), self.fvs_glob_constr(body[2]))
            raise NameError("TODO")
        elif tag == "R":
            # Printf.sprintf "R(%s, %s, %s, %s, %s)" "TODO" (brackets (show_arr show_id ", " ids)) "TODO" (show_glob_constr_arr gcs1) (show_glob_constr_arr gcs2)
            # return ("R", "TODO", self.fvs_ls(self.fvs_id, body[1]), "TODO", self.fvs_ls(self.fvs_glob_constr, body[3]), self.fvs_ls(self.fvs_glob_constr, body[4]))
            raise NameError("TODO")
        elif tag == "S":
            # Printf.sprintf "S(%s)" (show_glob_sort gsort)
            # return ("S", self.fvs_glob_sort(body[0]))
            raise NameError("TODO")
        elif tag == "H":
            # Printf.sprintf "H(%s, %s, %s)" "TODO" (show_intro_pattern_naming_expr ipne) "TODO"
            return self.fvs_intro_pattern_naming_expr(body[1])
        elif tag == "T":
            # Printf.sprintf "T(%s, %s)" (show_glob_constr gc) (show_cast_type show_glob_constr gc_ty)
            
            # print("HERE", gc)
            # fvs0 = self.fvs_glob_constr(body[0])
            # fvs1 = self.fvs_cast_type(body[1])
            # return fvs0.union(fvs1)
            return set()
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_glob_constrs(self, gcs):
        return self.fvs_ls(self.fvs_glob_constr, gcs)

    def fvs_gtrm(self, gtrm):
        return self.fvs_glob_constr(gtrm)

    def fvs_id(self, id):
        return set([self._conv(x)])

    def fvs_predicate_pattern(self, parg):
        # let f (loc, (mutind, i), ns) = Printf.sprintf "(%s, %d, %s)" (Names.MutInd.to_string mutind) i (brackets (show_ls show_name ", " ns)) in
        # Printf.sprintf "(%s, %s)" (show_name n) (show_maybe f m_args)
        fvs0 = set([self._conv(parg[0])])
        tag, body = self._unpack(parg[1])
        if tag == "N":
            fvs1 = set()
        elif tag == "S":
            body = body[0]
            self.globs.add(self._conv(body[0]))
            fvs1 = set(self.fvs_ls(self.fvs_id, body[2]))
        else:
            raise NameError("Tag {} not supported".format(tag))
        return fvs0.union(fvs1)

    def fvs_tomatch_tuple(self, tmt):
        # Printf.sprintf "(%s, %s)" (show_glob_constr gc) (show_predicate_pattern pp)
        fvs0 = self.fvs_glob_constr(tmt[0])
        fvs1 = self.fvs_predicate_pattern(tmt[1])
        return fvs0.union(fvs1)

    def fvs_tomatch_tuples(self, tmts):
        # brackets (show_ls show_tomatch_tuple ", " tmts)
        return self.fvs_ls(self.fvs_tomatch_tuple, tmts)

    def fvs_case_clause(self, cc):
        body = cc
        # Printf.sprintf "(%s, %s, %s)" (brackets (show_ls show_id ", " ids)) (brackets (show_ls show_cases_pattern ", " cps)) (show_glob_constr gc)
        fvs0 = self.fvs_ls(self.fvs_id, body[0])
        fvs1 = self.fvs_ls(self.fvs_cases_pattern, body[1])
        fvs2 = self.fvs_glob_constr(body[2])
        return fvs0.union(fvs1).union(fvs2)

    def fvs_case_clauses(self, ccs):
        # brackets (show_ls show_case_clause ", " ccs)
        return self.fvs_ls(self.fvs_case_clause, ccs)


    # -------------------------------------------------
    # Tactics

    def fvs_occurrences_gen(self, fvs, og):
        tag, body = self._unpack(og)
        if tag == "A":
            return set()
        elif tag == "B":
            return self.fvs_ls(fvs, body[0])
        elif tag == "N":
            return set()
        elif tag == "O":
            return self.fvs_ls(fvs, body[0])

    def fvs_occurrences_expr(self, oe):
        # return self.fvs_occurrences_gen(lambda x: set(), oe)
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
        return set([self._conv(qhyp)])

    def fvs_explicit_binding(self, fvs, eb):
        fvs0 = self.fvs_quantified_hypothesis(eb[0])
        fvs1 = fvs(eb[1])
        return fvs0.union(fvs1)

    def fvs_bindings(self, fvs, b):
        tag, body = self._unpack(b)
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
        tag, body = self._unpack(gref)
        if tag == "VR":
            self.globs.add(self._conv(body[0]))
        elif tag == "CR":
            self.globs.add(self._conv(body[0]))
        elif tag == "IR":
            self.globs.add(self._conv(body[0]))
        elif tag == "TR":
            self.globs.add(self._conv(body[0]))
        else:
            raise NameError("Tag {} not supported".format(tag))
        return set()

    def fvs_match_rule(self, fvs_pat, fvs_tac, mrule):
        tag, body = self._unpack(mrule)
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
        # TODO(deh): error in coq printing
        self._log("@fvs_match_pattern".format(mp))
        return set()

    def fvs_match_context_hyps(self, fvs_pat, hyps):
        # tag, body = self._unpack(hyps)
        # if tag == "H":
        #     fvs1 = self.fvs_match_pattern(fvs_pat, body[1])
        #     return fvs1.add(self._conv(body[0]))
        # elif tag == "D":
        #     fvs1 = self.fvs_match_pattern(fvs_pat, body[1])
        #     fvs2 = self.fvs_match_pattern(fvs_pat, body[2])
        #     return fvs1.union(fvs2).add(self._conv(body[0]))
        # else:
        #     raise NameError("Tag {} not supported".format(tag))
        return set()

    def fvs_message_token(self, mtok):
        return set()
        # TODO(deh): error in coq printing
        # tag, body = self._unpack(mtok)
        # if tag == "S":
        #     return set()
        # elif tag == "I":
        #     return set()
        # elif tag == "G":
        #     return self.fvs_gname(body[0])

    def fvs_generic_arg(self, garg):
        tag, body = self._unpack(garg)
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
            method = getattr(self, "fvs_{}".format(self._conv(body[0])))
            return method(body[1])
        else:
            if (tag == "auto_using" or
                tag == "hintbases" or
                tag == "bindings" or
                tag == "intropattern" or
                tag == "constr" or       # TODO(deh): huh??
                tag == "casted_constr" or
                tag == "natural" or
                tag == "var" or
                tag == "int_or_var" or
                tag == "ssrhint" or
                tag == "ssrexactarg" or
                tag == "ssrdoarg" or
                tag == "ssrhpats_nobs" or
                tag == "ssrwlogfwd" or
                tag == "ssrsufffwd" or
                tag == "ssrsetfwd" or
                tag == "ssrcongrarg" or
                tag == "ssrfixfwd" or
                tag == "ssrintrosarg" or
                tag == "ssrtclarg" or
                tag == "ssrseqdir" or
                tag == "ssrseqarg" or
                tag == "ssrrpat"):
                return set()
            else:
                raise NameError("Tag {} not supported".format(tag))

    def fvs_tactic_arg(self, targ):
        tag, body = self._unpack(targ)
        self._log("@fvs_tactic_arg | tag={}; raw={}".format(tag, targ))
        if tag == "G":
            # Printf.sprintf "(G %s)" (show_generic_arg ga)
            return self.fvs_generic_arg(body[0])
        elif tag == "ME":
            # Printf.sprintf "(ME %s)" (show_may_eval mev)
            return self.fvs_may_eval(body[0])
        elif tag == "R":
            # Printf.sprintf "(R %s)" (show_g_reference r)
            return self.fvs_g_reference(body[0])
        elif tag == "C":
            # Printf.sprintf "(C %s %s)" (show_g_reference r) (show_tactic_args targs)
            fvs0 = self.fvs_g_reference(body[0])
            fvs1 = self.fvs_tactic_args(body[1])
            return fvs0.union(fvs1)
        elif tag == "FreshId":
            # Printf.sprintf "(F %s)" (show_sexpr_ls (fun x -> show_or_var (fun x -> x) x) sovs)
            return set()
        elif tag == "E":
            # Printf.sprintf "(E %s)" (show_tac tac)
            return self.fvs_tac(body[0])
        elif tag == "P":
            # Printf.sprintf "(P %s)" (show_gtrm c)
            return self.fvs_gtrm(body[0])
        elif tag == "N":
            # "N"
            return set()
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_tactic_args(self, targs):
        return self.fvs_ls(self.fvs_tactic_arg, targs)

    def fvs_atomic_tac(self, atac):
        tag, body = self._unpack(atac)
        self._log("@fvs_atomic_tac | tag={}; raw={}".format(tag, atac))
        if tag == "IntroPattern":
            # let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
            # Printf.sprintf "(IntroPattern %b %s)" ef (show_sexpr_ls f ipes)
            return self.fvs_ls(lambda x: self.fvs_intro_pattern_expr(self.fvs_gtrm, x), body[1])
        elif tag == "Apply":
            # let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
            # let g (gnm, x) = Printf.sprintf "(%s %s)" (show_gname gnm) (show_maybe f x) in
            # Printf.sprintf "(Apply %b %b %s %s)" af ef (show_sexpr_ls (show_with_bindings_arg show_gtrm) bargss) (show_maybe g gnm_and_ipe)
            fvs2 = self.fvs_ls(lambda x: self.fvs_with_bindings_arg(self.fvs_gtrm, x), body[2])
            f = lambda gnm, x: self.fvs_gname(gnm).union(self.fvs_maybe(lambda y: self.fvs_intro_pattern_expr(self.fvs_gtrm, y)), x)
            fvs3 = self.fvs_maybe(f, body[3])
            return fvs2.union(fvs3)
        elif tag == "Elim":
            # Printf.sprintf "(Elim %b %s %s)" ef (show_with_bindings_arg show_gtrm bargs) (show_maybe (show_with_bindings show_gtrm) maybe_wb)
            fvs1 = self.fvs_with_bindings_arg(self.fvs_gtrm, body[1])
            fvs2 = self.fvs_maybe(lambda x: self.fvs_with_bindings(self.fvs_gtrm, x), body[2])
            return fvs1.union(fvs2)
        elif tag == "Case":
            # Printf.sprintf "(Case %b %s)" ef (show_with_bindings_arg show_gtrm bargs)
            return self.fvs_with_bindings_arg(self.fvs_gtrm, body[1])
        elif tag == "MutualFix":
            # let f (id, c) = Printf.sprintf "(%s, %s)" (show_id id) (show_gtrm c) in
            # Printf.sprintf "(MutualCofix %s %s)" (show_id id) (show_sexpr_ls f body)
            f = lambda x, i, c: self.fvs_gtrm(c)
            fvs1 = [f(x) for x in body[2]]
            ids = set([x[0] for x in body[2]])
            return fvs1.difference(ids)
        elif tag == "MutualCofix":
            # let f (id, c) = Printf.sprintf "(%s, %s)" (show_id id) (show_gtrm c) in
            # Printf.sprintf "MutualCofix(%s,  %s)" (show_id id) (brackets (show_ls f ", " body))
            f = lambda x, c: self.fvs_gtrm(c)
            fvs1 = [f(x) for x in body[2]]
            ids = set([x[0] for x in body[2]])
            return fvs1.difference(ids)
        elif tag == "Assert":
            # let f (loc, ipe) = show_intro_pattern_expr show_gtrm ipe in
            # let g = show_maybe f in
            # Printf.sprintf "(Assert %b %s %s %s)" b (show_maybe (show_maybe show_tac) mm_tac) (g ml_ipe) (show_gtrm c)
            raise NameError("TODO")
        elif tag == "Generalize":
            # let f (wo, name) = Printf.sprintf "(%s, %s)" (show_with_occurrences show_gtrm wo) (show_name name) in
            # Printf.sprintf "Generalize(%s)" (brackets (show_ls f ", " ls))
            raise NameError("TODO")
        elif tag == "LetTac":
            # let f (loc, ipne) = show_intro_pattern_naming_expr ipne in
            # Printf.sprintf "LetTac(%s, %s, %s, %b, %s)" (show_name name) (show_gtrm c) (show_clause_expr ce) lf (show_maybe f ml_ipe)
            fvs1 = self.fvs_gtrm(body[1])
            fvs2 = self.fvs_clause_expr(body[2])
            fvs3 = self.fvs_maybe(self.fvs_gtrm(body[4]))
            return fvs1.union(fvs2).union(fvs3).difference(self._conv(body[0]))
        elif tag == "InductionDestruct":
            # Printf.sprintf "InductionDestruct(%b, %b, %s)" rf ef (show_induction_clause_list ics)
            return self.fvs_induction_clause_list(body[2])
        elif tag == "Reduce":
            # Printf.sprintf "Reduce(%s, %s)" "TODO" (show_clause_expr ce)
            # return ("Reduce", "TODO", self.fvs_clause_expr(body[1]))
            return self.fvs_clause_expr(body[1])
        elif tag == "Change":
            # let f (_, gtrm, cpat) = show_gtrm gtrm in
            # Printf.sprintf "MutualFix(%s, %s, %s)" (show_maybe f maybe_pat) (show_gtrm dtrm) (show_clause_expr ce)
            # return ("Change", "TODO", self.fvs_gtrm(body[1]), self.fvs_clause_expr(body[2]))
            raise NameError("TODO")
        elif tag == "Rewrite":
            # let f (b, m, barg) = Printf.sprintf "(%b %s %s)" b (show_multi m) (show_with_bindings_arg show_gtrm barg) in
            # Printf.sprintf "(Rewrite %b %s %s %s)" ef (show_sexpr_ls f rargs) (show_clause_expr ce) (show_maybe show_tac maybe_tac)
            # return self.fvs_clause_expr(body[2]), self.fvs_maybe(self.fvs_tac, body[3])
            raise NameError("TODO")
        elif tag == "Inversion":
            # Printf.sprintf "(Inversion %s %s)" (show_inversion_strength is) (show_quantified_hypothesis qhyp)
            # return self.fvs_quantified_hypothesis(body[1])
            raise NameError("TODO")
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_tac(self, tac):
        if tac == None:
            return set()
        tag, body = self._unpack(tac)
        self._log("@fvs_tac | tag={}; raw={}".format(tag, tac))
        if tag == "Atom":
            # Printf.sprintf "(Atom %s)" (show_atomic_tac atac)
            return self.fvs_atomic_tac(body[0])
        elif tag == "Then":
            # Printf.sprintf "Then(%s, %s)" (show_tac tac1) (show_tac tac2)
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tac(body[1])
            return fvs0.union(fvs1)
        elif tag == "Dispatch":
            # Printf.sprintf "Dispatch(%s)" (show_tacs tacs)
            return self.fvs_tacs(body[0])
        elif tag == "ExtendTac":
            # Printf.sprintf "ExtendTac(%s, %s, %s)" (show_tac_arr tacs1) (show_tac tac) (show_tac_arr tacs2)
            fvs0 = self.fvs_tacs(body[0])
            fvs1 = self.fvs_tac(body[1])
            fvs2 = self.fvs_tacs(body[0])
            return fvs0.union(fvs1).union(fvs2)
        elif tag == "Thens":
            # Printf.sprintf "Thens(%s, %s)" (show_tac tac) (show_tacs tacs)
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tacs(body[1])
            return fvs0.union(fvs1)
        elif tag == "Thens3parts":
            # Printf.sprintf "Thens3parts(%s, %s, %s, %s)" (show_tac tac1) (show_tac_arr tac1s) (show_tac tac2) (show_tac_arr tac2s)
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tacs(body[1])
            fvs2 = self.fvs_tac(body[2])
            fvs3 = self.fvs_tac(body[3])
            return fvs0.union(fvs1).union(fvs2).union(fvs3)
        elif tag == "First":
            # Printf.sprintf "First(%s)" (show_tacs tacs)
            return self.fvs_tacs(body[0])
        elif tag == "Complete":
            # Printf.sprintf "Complete(%s)" (show_tac tac)
            return self.fvs_tac(body[0])
        elif tag == "Solve":
            # Printf.sprintf "Solve(%s)" (show_tacs tacs)
            return self.fvs_tacs(body[0])
        elif tag == "Try":
            # Printf.sprintf "Try(%s)" (show_tac tac)
            return self.fvs_tac(body[0])
        elif tag == "Or":
            # Printf.sprintf "Or(%s, %s)" (show_tac tac1) (show_tac tac2)
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tac(body[1])
            return self.fvs_tac(fvs0).union(fvs1)
        elif tag == "Once":
            # Printf.sprintf "Once(%s)" (show_tac tac)
            return self.fvs_tac(body[0])
        elif tag == "ExactlyOnce":
            # Printf.sprintf "ExactlyOnce(%s)" (show_tac tac)
            return self.fvs_tac(body[0])
        elif tag == "IfThenCatch":
            # Printf.sprintf "IfThenCatch(%s, %s, %s)" (show_tac tac1) (show_tac tac2) (show_tac tac3)
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tac(body[1])
            fvs2 = self.fvs_tac(body[2])
            return fvs0.union(fvs1).union(fvs2)
        elif tag == "Orelse":
            # Printf.sprintf "Orelse(%s, %s)" (show_tac tac1) (show_tac tac2)
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_tac(body[1])
            return fvs0.union(fvs1)
        elif tag == "Do":
            # Printf.sprintf "Do(%s, %s)" (show_or_var string_of_int iov) (show_tac tac)
            return self.fvs_tac(body[1])
        elif tag == "Timeout":
            # Printf.sprintf "Timeout(%s, %s)" (show_or_var string_of_int iov) (show_tac tac)
            return self.fvs_tac(body[1])
        elif tag == "Time":
            # Printf.sprintf "Time(%s, %s)" (show_maybe (fun x -> x) maybe_str) (show_tac tac)
            return self.fvs_tac(body[1])
        elif tag == "Repeat":
            # Printf.sprintf "Repeat(%s)" (show_tac tac)
            return self.fvs_tac(body[0])
        elif tag == "Progress":
            # Printf.sprintf "Progress(%s)" (show_tac tac)
            return self.fvs_tac(body[0])
        elif tag == "ShowHyps":
            # Printf.sprintf "ShowHyps(%s)" (show_tac tac)
            return self.fvs_tac(body[0])
        elif tag == "Abstract":
            # Printf.sprintf "Asbtract(%s, %s)" (show_tac tac) (show_maybe show_id maybe_id)
            fvs0 = self.fvs_tac(body[0])
            fvs1 = self.fvs_maybe(self.fvs_id, body[1])
            return fvs0.union(fvs1)
        elif tag == "Id":
            # Printf.sprintf "Id(%s)" (brackets (show_ls show_message_token ", " msgs))
            return self.fvs_ls(self.fvs_message_token, body[0])
        elif tag == "Fail":
            # Printf.sprintf "Info(%s, %s, %s)" (show_global_flag gf) (show_or_var string_of_int iov) (brackets (show_ls show_message_token ", " msgs))
            raise NameError("TODO")
        elif tag == "Info":
            # Printf.sprintf "Info(%s)" (show_tac tac)
            return self.fvs_tac(body[0])
        elif tag == "LetIn":
            # let f ((loc, id), targ) = Printf.sprintf "(%s, %s)" (show_id id) (show_tactic_arg targ) in
            # Printf.sprintf "Let(%b, %s, %s)" rf (brackets (show_ls f ", " bindings)) (show_tac tac)
            # return ("LetIn", bool(body[0]), self.fvs_ls(lambda x, targ: (self.fvs_id(x), self.fvs_tactic_arg(targ))), self.fvs_tac(body[2]))
            raise NameError("TODO")
        elif tag == "Match":
            # let f (_, gtrm, cpat) = show_gtrm gtrm in
            # Printf.sprintf "Match(%s, %s, %s)" (show_lazy_flag lf) (show_tac tac) (show_match_rules f show_tac mrules)
            # return ("Match", self.fvs_lazy_flag(body[0]), self.fvs_tac(body[1]), "TODO")
            raise NameError("TODO")
        elif tag == "MatchGoal":
            # let f (_, gtrm, cpat) = show_gtrm gtrm in
            # Printf.sprintf "MatchGoal(%s, %b, %s)" (show_lazy_flag lf) df (show_match_rules f show_tac mrules)
            # TODO(deh): error in Coq printing here
            return self.fvs_match_rules(self.fvs_gtrm, self.fvs_tac, body[2])
        elif tag == "Fun":
            # Printf.sprintf "Fun(%s, %s)" (brackets (show_ls (show_maybe show_id) ", " maybe_ids)) (show_tac tac)
            bnd0 = self.fvs_ls(lambda x: self.fvs_maybe(self.fvs_id, x), body[0])
            fvs1 = self.fvs_tac(body[1])
            return fvs1.difference(bnd0)
        elif tag == "Arg":
            # Printf.sprintf "Arg(%s)" (show_tactic_arg targ)
            return self.fvs_tactic_arg(body[0])
        elif tag == "Select":
            # Printf.sprintf "Select(%s, %s)" (show_goal_selector gs) (show_tac tac)
            fvs1 = self.fvs_goal_selector(body[0])
            fvs2 = self.fvs_tac(body[1])
            return fvs1.union(fvs2)
        elif tag == "ML":
            # Printf.sprintf "ML(%s, %s)" (show_ml_tactic_entry mlen) (show_tactic_args targs)
            return self.fvs_tactic_args(body[1])
        elif tag == "Alias":
            # Printf.sprintf "Alias(%s, %s)" (KerName.to_string kername) (show_tactic_args targs)
            return self.fvs_tactic_args(body[1])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_tacs(self, tacs):
        return self.fvs_ls(self.fvs_tac, tacs)

    # -------------------------------------------------
    # Ssreflect tactics

    def fvs_cpattern(self, cpat):
        return self.fvs_glob_constr(cpat)

    def fvs_pattern(self, pat):
        tag, body = self._unpack(pat)
        self._log("@fvs_pattern | tag={}; raw={}".format(tag, pat))
        if tag == "T":
            return self.fvs_term(body[0])
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
        # Pml4tp.show_sexpr_ls (fun m_tac -> Pml4tp.show_maybe Pml4tp.show_tac m_tac) ortacs
        return self.fvs_ls(lambda x: self.fvs_maybe(self.fvs_tac, x), ortacs)

    def fvs_ssrhintarg(self, ha):
        # Printf.sprintf "(%b %s)" b (show_ssrortacs ortacs)
        return self.fvs_ssrortacs(ha[1])

    def fvs_ssrhyp(self, hyp):
        # Pml4tp.show_id id
        return set([self._conv(hyp)])

    def fvs_ssrhyprep(self, hyp):
        # Pml4tp.show_id id
        return set([self._conv(hyp)])

    def fvs_ssrhoirep(self, hoirep):
        tag, body = self._unpack(hoirep)
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
        # let f ((id, k), c_p) = Printf.sprintf "(%s %s %s)" k (show_hoi id) (Pml4tp.show_maybe show_cpattern c_p) in
        # Printf.sprintf "(%s %s)" (show_clear clr) (Pml4tp.show_maybe f x)
        # TODO(deh): fuck printing k, its a space?
        def f(x):
            fvs1 = self.fvs_ssrhoirep(x[0])
            fvs2 = self.fvs_maybe(self.fvs_cpattern, x[1])
            return fvs1.union(fvs2)
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
        # Pml4tp.show_maybe (fun (b, occ) -> Printf.sprintf "(%b %s)" b (Pml4tp.show_sexpr_ls string_of_int occ)) occ
        return set()

    def fvs_ssrdocc(self, docc):
        # | None, occ -> Printf.sprintf "(N %s)" (show_occ occ)
        # | Some clr, _ -> Printf.sprintf "(S %s)" (show_clear clr)
        tag, body = self._unpack(docc)
        if tag == "N":
            return self.fvs_ssrocc(body[0])
        elif tag == "S":
            return self.fvs_ssrclear(body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_ssrview(self, view):
        # Pml4tp.show_sexpr_ls (fun (_, (c, _)) -> Pml4tp.show_glob_constr c) view
        return self.fvs_ls(self.fvs_glob_constr, view)

    def fvs_ssripat(self, ipat):
        tag, body = self._unpack(ipat)
        if tag == "I":
            return set()
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
        # Printf.sprintf "(%s %s %s %s)" (show_clear clr) (show_ipats ipat) (show_ipats binders) (show_ipats simpl)
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
        # Pml4tp.show_maybe show_ipat eqid
        return self.fvs_maybe(self.fvs_ssripat, eqid)

    def fvs_ssrarg(self, arg):
        # Printf.sprintf "(%s %s %s %s)" (show_view view) (show_eqid eqid) (show_dgens show_gen dgens) (show_intros ipats)
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
        # Printf.sprintf "(%s %s)" (show_docc docc) (show_term dt)
        fvs0 = self.fvs_ssrdocc(agen[0])
        fvs1 = self.fvs_term(agen[1])
        return fvs0.union(fvs1)

    def fvs_ssragens(self, agens):
        # show_dgens show_agen
        return self.fvs_dgens(self.fvs_ssragen, agens)

    def fvs_ssrapplyarg(self, aa):
        # Printf.sprintf "(%s %s %s %s)" (show_view view) (show_eqid eqid) (show_agens dgens) (show_ipats ipats)
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
        # Printf.sprintf "(%s %s)" (Pml4tp.show_maybe show_clear m_clr) (show_occ occ)
        fvs0 = self.fvs_maybe(self.fvs_ssrclear, rwocc[0])
        fvs1 = self.fvs_ssrocc(rwocc[1])
        return fvs0.union(fvs1)

    def fvs_ssrrule(self, rule):
        tag, body = self._unpack(rule)
        if tag == "R":
            return self.fvs_ssrsimpl(body[0])
        elif tag == "D":
            return self.fvs_term(body[0])
        elif tag == "E":
            return self.fvs_term(body[0])
        else:
            raise NameError("Tag {} not supported".format(tag))

    def fvs_ssrpattern_squarep(self, pat):
        # Pml4tp.show_maybe show_rpattern rx
        return self.fvs_maybe(self.fvs_rpattern, pat)

    def fvs_ssrpattern_ne_squarep(self, pat):
        return self.fvs_ssrpattern_squarep(pat)

    def fvs_ssrrwarg(self, rwarg):
        # Printf.sprintf "(%s %s %s %s %s)" (show_rwdir d) (show_mult m) (show_rwocc docc) (show_pattern_squarep rx) (show_rule r)
        fvs2 = self.fvs_ssrrwocc(rwarg[2])
        fvs3 = self.fvs_ssrpattern_squarep(rwarg[3])
        fvs4 = self.fvs_ssrrule(rwarg[4])
        return fvs2.union(fvs3).union(fvs4)

    def fvs_ssrrwargs(self, rwargs):
        return self.fvs_ls(self.fvs_ssrrwarg, rwargs)

    def fvs_ssrfwdid(self, fwdid):
        return set([self._conv(fwdid)])

    def fvs_ssrfwd(self, fwd):
        tag, body = self._unpack(fwd)
        if tag == "HT":
            return set()
        elif tag == "HV":
            return set()
        elif tag == "P":
            return set()
        else:
            raise NameError("Tag {} not supported".format(tag)) 

    def fvs_ssrposefwd(self, posefwd):
        return self.fvs_ssrfwd(posefwd)

    def fvs_ssrhavefwd(self, havefwd):
        return self.fvs_ssrfwd(havefwd)

    def fvs_ssrhavefwdwbinders(self, hfwb):
        fvs0 = self.fvs_ssrhpats(hfwb[0])
        fvs1 = self.fvs_ssrfwd(hfwb[1])
        return fvs0.union(fvs1)
