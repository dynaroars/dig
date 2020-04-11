"""
Find upperbound of polynomials using optimizer
"""
from abc import ABCMeta, abstractmethod

import math
import pdb
from time import time

import z3
import sage.all

import helpers.vcommon as CM
import helpers.miscs

import settings
import data.traces
import data.poly.base
import data.inv.oct
import data.poly.mp
import data.inv.mp
import infer.base

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Infer(infer.base.Infer, metaclass=ABCMeta):
    def __init__(self, symstates, prog):
        # need prog because symstates could be None
        super().__init__(symstates, prog)

    def gen(self):
        locs = self.inv_decls.keys()
        tasks = [(loc, term)
                 for loc in locs
                 for term in self.get_terms(self.inv_decls[loc].sageExprs)]
        mlog.debug("infer upperbounds for {} terms at {} locs".format(
            len(tasks), len(locs)))

        def f(tasks):
            return [(loc, term,
                     self.symstates.maximize(loc, self.to_expr(term), do_all=False))
                    for loc, term in tasks]
        wrs = helpers.miscs.Miscs.run_mp('optimize upperbound', tasks, f)

        dinvs = data.inv.invs.DInvs()
        for loc, term, v in wrs:
            if v is None or v > settings.OCT_MAX_V:
                continue
            inv = self.inv_cls(term.mk_le(v))
            inv.set_stat(data.inv.base.Inv.PROVED)
            dinvs.setdefault(loc, data.inv.invs.Invs()).add(inv)

        return dinvs

    def get_terms(self, symbols):
        terms = self.my_get_terms(symbols)
        mlog.debug("{} terms for {}".format(
            len(terms), self.__class__.__name__))

        # filter terms
        st = time()
        new_terms = self.filter_terms(
            terms, set(self.inp_decls.names))
        helpers.miscs.Miscs.show_removed(
            'term filter', len(terms), len(new_terms), time() - st)
        return new_terms

    def filter_terms(self, terms, inps):
        assert isinstance(inps, set) and \
            all(isinstance(s, str) for s in inps), inps

        if not inps:
            mlog.warning("Have not tested case with no inps")

        excludes = self.get_excludes(terms, inps)
        new_terms = [term for term in terms if term not in excludes]
        return new_terms


class Ieq(Infer):
    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)

    def to_expr(self, term):
        return helpers.miscs.Z3.parse(str(term.poly),
                                      use_reals=self.symstates.use_reals)

    def inv_cls(self, term_ub):
        return data.inv.oct.Oct(term_ub)

    def my_get_terms(self, symbols):
        terms = helpers.miscs.Miscs.get_terms_fixed_coefs(
            symbols, subset_siz=2)

        if settings.UTERMS:
            uterms = self.my_get_terms_user(symbols, settings.UTERMS)
            old_siz = len(terms)
            terms.update(uterms)
            mlog.debug("adding {} new terms from user".format(
                len(terms) - old_siz))

        terms = [data.poly.base.GeneralPoly(t) for t in terms]
        return terms

    def my_get_terms_user(self, symbols, uterms):
        assert isinstance(uterms, set) and uterms, uterms
        assert all(isinstance(t, str) for t in uterms), uterms

        mylocals = {str(s): s for s in symbols}

        import sage.all
        try:
            uterms = set(sage.all.sage_eval(term, locals=mylocals)
                         for term in uterms)
        except NameError as ex:
            raise NameError(
                "{} (defined vars: {})".format(ex, ','.join(map(str, symbols))))

        terms = set()
        for t in uterms:
            terms.add(t)
            terms.add(-t)
            for v in symbols:
                # v+t, v-t, -v+t, -v-t
                terms.add(v + t)
                terms.add(v - t)
                terms.add(-v + t)
                terms.add(-v - t)

        return terms

    def get_excludes(self, terms, inps):
        excludes = set()
        for term in terms:
            t_symbs = set(map(str, term.symbols))
            if len(t_symbs) <= 1:  # ok for finding bound of single input val
                continue

            if (inps.issuperset(t_symbs) or
                    all(s not in inps for s in t_symbs)):
                excludes.add(term)
        return excludes


class MP(Infer):
    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)

    def to_expr(self, term):
        return data.inv.mp.MP(term, is_ieq=None).expr(self.symstates.use_reals)

    def inv_cls(self, term_ub):
        return data.inv.mp.MP(term_ub)

    def my_get_terms(self, symbols):

        terms = []
        terms_u = data.poly.mp.MP.get_terms(symbols)
        terms_u_no_octs = [(a, b) for a, b in terms_u if len(b) >= 2]

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
        return terms

    def get_excludes(self, terms, inps):
        excludes = set()
        for term in terms:
            a_symbs = list(map(str, helpers.miscs.Miscs.get_vars(term.a)))
            b_symbs = list(map(str, helpers.miscs.Miscs.get_vars(term.b)))
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

        return excludes
