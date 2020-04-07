"""
Find upperbound of polynomials using binary search-CEGIR approach
"""
import math
import pdb
from time import time

import z3
import sage.all

import helpers.vcommon as CM
from helpers.miscs import Miscs
import helpers.miscs

import settings
import data.traces
import data.poly.base
import data.poly.mp
import data.inv.mp
import cegir.base

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class CegirMP(cegir.base.Cegir):
    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)

    def gen(self, traces, inps):
        assert isinstance(traces, data.traces.DTraces) and traces, traces
        assert isinstance(inps, data.traces.Inps), inps

        locs = self.inv_decls.keys()
        tasks = [(loc, term)
                 for loc in locs
                 for term in self.get_terms(self.inv_decls[loc].sageExprs)]
        mlog.debug("infer upperbounds for {} MP terms at {} locs".format(
            len(tasks), len(locs)))

        def to_expr(t):
            return data.inv.mp.MP(t, is_ieq=None).expr(self.symstates.use_reals)

        def f(tasks):
            return [(loc, term,
                     self.symstates.maximize(loc, to_expr(term)))
                    for loc, term in tasks]
        wrs = Miscs.run_mp('optimize upperbound', tasks, f)

        dinvs = data.inv.invs.DInvs()
        for loc, term, v in wrs:
            if v is None:
                continue
            inv = data.inv.mp.MP(term.mk_le(v))
            inv.set_stat(data.inv.base.Inv.PROVED)
            dinvs.setdefault(loc, data.inv.invs.Invs()).add(inv)

        return dinvs, []

    def get_terms(self, symbols):

        terms = []

        terms_u = data.poly.mp.MP.get_terms(symbols)
        terms_u_no_octs = [(a, b) for a, b in terms_u
                           if len(b) >= 2]

        if settings.DO_IEQS:  # ignore oct invs
            terms_u = terms_u_no_octs

        def _get_terms(terms_u, is_max):
            terms_l = [(b, a) for a, b in terms_u]
            terms = terms_u + terms_l
            terms = [data.poly.mp.MP(a, b, is_max) for a, b in terms]
            return terms

        terms_max = _get_terms(terms_u, is_max=True)

        terms_min = _get_terms(terms_u_no_octs, is_max=False)
        terms_mp = terms_min + terms_max
        terms.extend(terms_mp)
        mlog.debug("{} terms for MP".format(len(terms_mp)))

        if settings.DO_TERM_FILTER:
            st = time()
            new_terms = self.filter_terms(
                terms, set(self.symstates.inp_decls.names))
            Miscs.show_removed('term filter',
                               len(terms), len(new_terms), time() - st)
            return new_terms
        else:
            return terms

    @staticmethod
    def filter_terms(terms, inps):
        assert isinstance(inps, set) and \
            all(isinstance(s, str) for s in inps), inps

        if not inps:
            mlog.warning("Have not tested case with no inps")

        excludes = set()
        for term in terms:
            a_symbs = list(map(str, Miscs.get_vars(term.a)))
            b_symbs = list(map(str, Miscs.get_vars(term.b)))
            inp_in_a = any(s in inps for s in a_symbs)
            inp_in_b = any(s in inps for s in b_symbs)

            if ((inp_in_a and inp_in_b) or
                    (not inp_in_a and not inp_in_b)):
                excludes.add(term)
                continue

            t_symbs = set(a_symbs + b_symbs)

            if len(t_symbs) <= 1:  # ok for finding bound of single input val
                continue

            if (inps.issuperset(t_symbs) or
                    all(s not in inps for s in t_symbs)):
                excludes.add(term)

        new_terms = [term for term in terms if term not in excludes]
        return new_terms
