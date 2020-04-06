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
    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)

    def gen(self, traces, inps):
        assert isinstance(traces, data.traces.DTraces) and traces, traces
        assert isinstance(inps, data.traces.Inps), inps

        locs = self.inv_decls.keys()
        tasks = [(loc, term)
                 for loc in locs
                 for term in self.get_terms(self.inv_decls[loc].sageExprs)]
        mlog.debug("infer upperbounds for {} terms at {} locs".format(
            len(tasks), len(locs)))

        def f(tasks):
            return [(loc, term, self.find_max(loc, term)) for loc, term in tasks]
        wrs = Miscs.run_mp('optimizer: find upperbound', tasks, f)

        dinvs = data.inv.invs.DInvs()
        for loc, term, v in wrs:
            if v is None:
                continue
            inv = self.mk_le(term, v)
            inv.set_stat(data.inv.base.Inv.PROVED)
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
                terms, set(self.prog.inp_decls.names))
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

    def mk_le(self, term, v):
        assert isinstance(term, data.poly.base.GeneralPoly), term
        return data.inv.oct.Oct(term.mk_le(v))

    def find_max(self, loc, term):
        ss = self.symstates.ss[loc]
        ss = z3.Or([ss[depth].myexpr for depth in ss])
        term = helpers.miscs.Z3.parse(
            str(term.poly), use_reals=self.symstates.use_reals)
        opt = z3.Optimize()
        opt.add(ss)
        h = opt.maximize(term)
        stat = opt.check()

        v = None
        if stat == z3.sat:
            uv = str(opt.upper(h))
            if uv != 'oo':  # no bound
                v = int(uv)
                if v > settings.OCT_MAX_V:
                    v = None
        else:
            mlog.warning("cannot find upperbound for {} {}".format(loc, term))
        return v
