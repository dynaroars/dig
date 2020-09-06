"""
Find upperbound of polynomials using optimizer
"""
from abc import ABCMeta
import pdb
from time import time
import operator

import z3
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

    def gen(self, dtraces, locs=None, extra_constr=None):
        assert isinstance(dtraces, data.traces.DTraces) and dtraces, dtraces

        if locs:
            # gen preconds
            assert z3.is_expr(extra_constr)

            def _terms(_):
                return self.inp_decls.sageExprs
        else:
            locs = self.inv_decls.keys()

            def _terms(loc):
                return self.inv_decls[loc].sageExprs

        # remove terms exceeding maxV
        termss = [self.get_terms(_terms(loc)) for loc in locs]
        mlog.debug("check upperbounds for {} terms at {} locs".format(
            sum(map(len, termss)), len(locs)))
        refs = {loc: {self.inv_cls(t.mk_le(settings.IUPPER)): t for t in terms}
                for loc, terms in zip(locs, termss)}
        ieqs = data.inv.invs.DInvs()
        for loc in refs:
            for inv in refs[loc].keys():
                ieqs.setdefault(
                    loc, data.inv.invs.Invs()).add(inv)

        cexs, ieqs = self.check(ieqs, inps=None)
        ieqs = ieqs.remove_disproved()
        tasks = [(loc, refs[loc][t]) for loc in ieqs for t in ieqs[loc]]

        mlog.debug("infer upperbounds for {} terms at {} locs".format(
            len(tasks), len(locs)))

        def f(tasks):
            return [(loc, term,
                     self.maximize(loc, term, extra_constr, dtraces))
                    for loc, term in tasks]
        wrs = helpers.miscs.Miscs.run_mp('optimize upperbound', tasks, f)

        dinvs = data.inv.invs.DInvs()
        for loc, term, v in wrs:
            if v is None:
                continue
            inv = self.inv_cls(term.mk_le(v))
            inv.set_stat(data.inv.base.Inv.PROVED)
            dinvs.setdefault(loc, data.inv.invs.Invs()).add(inv)

        return dinvs

    def maximize(self, loc, term, extra_constr, dtraces):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(term,
                          (data.poly.base.GeneralPoly, data.poly.mp.MP)), \
            (term, type(term))
        assert extra_constr is None or z3.is_expr(extra_constr), extra_constr
        assert isinstance(dtraces, data.traces.DTraces), dtraces

        iupper = (settings.IUPPER_MP if isinstance(
            term, data.poly.mp.MP) else settings.IUPPER)

        # check if concrete states(traces) exceed upperbound
        if extra_constr is None:
            # skip if do prepost
            if term.eval_traces(
                    dtraces[loc], lambda v: int(v) > iupper):
                return None

        return self.symstates.maximize(
            loc, self.to_expr(term), iupper, extra_constr)

    def get_terms(self, symbols):

        terms = self.my_get_terms(symbols)
        # for t in terms:
        #     print(t)
        # DBG()
        mlog.debug("{} terms for {}".format(
            len(terms), self.__class__.__name__))

        inps = set(self.inp_decls.names)
        if settings.DO_FILTER and inps:
            # filter terms
            st = time()
            new_terms = self.filter_terms(terms, inps)
            helpers.miscs.Miscs.show_removed(
                'filter terms', len(terms), len(new_terms), time() - st)
            terms = new_terms
        return terms

    def filter_terms(self, terms, inps):
        assert isinstance(inps, set) and \
            all(isinstance(s, str) for s in inps)\
            and inps, inps

        excludes = self.get_excludes(terms, inps)
        new_terms = [term for term in terms if term not in excludes]
        return new_terms


class Ieq(Infer):
    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)

    def to_expr(self, term):
        return helpers.miscs.Z3.parse(
            str(term.poly), use_reals=self.symstates.use_reals)

    def inv_cls(self, term_ub):
        return data.inv.oct.Oct(term_ub)

    def my_get_terms(self, symbols):
        assert symbols, symbols
        assert settings.IDEG >= 1, settings.IDEG

        if settings.IDEG == 1:
            terms = helpers.miscs.Miscs.get_terms_fixed_coefs(
                symbols, settings.ITERMS, settings.ICOEFS)
        else:
            terms = helpers.miscs.Miscs.get_terms(
                list(symbols), settings.IDEG)
            terms = [t for t in terms if t != 1]
            terms = helpers.miscs.Miscs.get_terms_fixed_coefs(
                terms, settings.ITERMS, settings.ICOEFS,
                do_create_terms=False)

            terms_ = set()
            for ts in terms:
                assert ts
                ts_ = [set(t.variables()) for t, _ in ts]
                if len(ts) <= 1 or not set.intersection(*ts_):
                    terms_.add(sum(operator.mul(*tc) for tc in ts))
            terms = terms_

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

        from sage.all import sage_eval
        try:
            uterms = set(sage_eval(term, locals=mylocals)
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
    """
    Min-max plus invariants
    """

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
        assert isinstance(terms, list)
        assert all(isinstance(t, data.poly.mp.MP) for t in terms), terms
        assert isinstance(inps, set), inps

        def is_pure(xs):
            return all(x in inps for x in xs) or all(x not in inps for x in xs)

        excludes = set()
        # print(inps)
        for term in terms:
            a_symbs = set(map(str, helpers.miscs.Miscs.get_vars(term.a)))
            b_symbs = set(map(str, helpers.miscs.Miscs.get_vars(term.b)))
            # print(term, a_symbs, b_symbs)

            if not is_pure(a_symbs) or not is_pure(b_symbs):
                excludes.add(term)
                # print('excluding, not pure', term)
                continue

            inp_in_a = any(s in inps for s in a_symbs)
            inp_in_b = any(s in inps for s in b_symbs)

            # if (inp in both a and b) or inp not in a or b
            if ((inp_in_a and inp_in_b) or
                    (not inp_in_a and not inp_in_b)):
                excludes.add(term)
                # print('excluding', term)
                continue

            t_symbs = set.union(a_symbs, b_symbs)

            if len(t_symbs) <= 1:  # finding bound of single input val,
                continue

            if (inps.issuperset(t_symbs) or
                    all(s not in inps for s in t_symbs)):
                excludes.add(term)

        # ins = [t for t in terms if t not in excludes]
        # outs = [t for t in terms if t in excludes]
        # print('ins')
        # for t in ins:
        #     print(t)
        # print('outs')
        # for t in outs:
        #     print(t)
        return excludes
