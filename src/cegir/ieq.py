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
import data.inv.oct
import cegir.base

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class CegirIeq(cegir.base.Cegir):
    def __init__(self, symstates, prog):  # TODO: don't need prog
        super().__init__(symstates, prog)

    def gen(self):
        locs = self.inv_decls.keys()
        tasks = [(loc, term)
                 for loc in locs
                 for term in self.get_terms(self.inv_decls[loc].sageExprs)]
        mlog.debug("infer upperbounds for {} terms at {} locs".format(
            len(tasks), len(locs)))

        def f(tasks):
            return [(loc, self.symstates.maximize(loc, term)) for loc, term in tasks]
        wrs = Miscs.run_mp('optimize upperbound', tasks, f)

        dinvs = data.inv.invs.DInvs()
        for loc, inv in wrs:
            if inv is None:
                continue
            dinvs.setdefault(loc, data.inv.invs.Invs()).add(inv)

        return dinvs, []  # no statss

    def get_terms(self, symbols):
        oct_siz = 2
        terms = Miscs.get_terms_fixed_coefs(symbols, oct_siz)
        terms = [data.poly.base.GeneralPoly(t) for t in terms]
        mlog.debug("{} terms for Ieqs".format(len(terms)))

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
            t_symbs = set(map(str, term.symbols))
            if len(t_symbs) <= 1:  # ok for finding bound of single input val
                continue

            if (inps.issuperset(t_symbs) or
                    all(s not in inps for s in t_symbs)):
                excludes.add(term)

        new_terms = [term for term in terms if term not in excludes]
        return new_terms
