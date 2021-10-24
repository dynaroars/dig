"""
Find upperbound of polynomial and min/max terms using an SMT solver optimizer
"""
import abc
import pdb
from time import time
import operator
import sympy

import z3
import settings
from helpers.miscs import Miscs, MP
from helpers.z3utils import Z3
import helpers.vcommon as CM

import data.traces
import data.inv.oct
import data.inv.mp
import infer.base

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)

class Infer(infer.base.Infer, metaclass=abc.ABCMeta):

    @staticmethod
    @abc.abstractmethod
    def to_expr(term):
        pass

    @staticmethod
    @abc.abstractmethod
    def inv_cls(term):
        pass

    @classmethod
    @abc.abstractmethod
    def my_get_terms(cls, terms, inps):
        pass

    @staticmethod
    @abc.abstractmethod
    def get_excludes(term):
        pass

    @classmethod
    def gen_from_traces(cls, traces, symbols):
        assert isinstance(traces, data.traces.Traces), traces

        maxV = cls.IUPPER
        minV = -1 * maxV

        terms = cls.my_get_terms(symbols.sageExprs)
        ps = []
        for term in terms:
            upperbound = int(max(term.eval_traces(traces)))
            if minV <= upperbound <= maxV:
                p = cls.inv_cls(term.mk_le(upperbound))
                ps.append(p)

        return ps

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

        dinvs = data.inv.invs.DInvs()

        if not termss:
            return dinvs

        mlog.debug(f"check upperbounds for {sum(map(len, termss))} "
                   f"terms at {len(locs)} locs")

        refs = {
            loc: {self.inv_cls(t.mk_le(self.get_iupper(t))): t for t in terms}
            for loc, terms in zip(locs, termss)
        }
        ieqs = data.inv.invs.DInvs()
        for loc in refs:
            for inv in refs[loc].keys():
                ieqs.setdefault(loc, data.inv.invs.Invs()).add(inv)

        cexs, ieqs = self.check(ieqs, inps=None)
        ieqs = ieqs.remove_disproved()
        tasks = [(loc, refs[loc][t]) for loc in ieqs for t in ieqs[loc]]

        mlog.debug(
            f"infer upperbounds for {len(tasks)} terms at {len(locs)} locs")

        def f(tasks):
            return [
                (loc, term, self.maximize(loc, term, extra_constr, dtraces))
                for loc, term in tasks
            ]

        wrs = MP.run_mp("optimize upperbound", tasks, f, settings.DO_MP)

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
        assert isinstance(term, (data.inv.base.RelTerm, data.inv.mp.MPTerm)), (
            term,
            type(term),
        )
        assert extra_constr is None or z3.is_expr(extra_constr), extra_constr
        assert isinstance(dtraces, data.traces.DTraces), dtraces

        iupper = self.get_iupper(term)

        # check if concrete states(traces) exceed upperbound
        if extra_constr is None:
            # skip if do prepost
            if term.eval_traces(dtraces[loc], lambda v: int(v) > iupper):
                return None

        return self.symstates.maximize(loc, self.to_expr(term), iupper, extra_constr)

    def get_terms(self, symbols):

        terms = self.my_get_terms(symbols)
        mlog.debug(f"{len(terms)} terms for {self.__class__.__name__}")

        inps = set(self.inp_decls.names)
        if settings.DO_FILTER and inps:
            st = time()
            excludes = self.get_excludes(terms, inps)
            new_terms = [term for term in terms if term not in excludes]
            Miscs.show_removed("filter terms", len(
                terms), len(new_terms), time() - st)
            terms = new_terms
        return terms

    @classmethod
    def get_iupper(cls, term):
        return (
            MMP.IUPPER
            if isinstance(term, data.inv.mp.MPTerm)
            else Ieq.IUPPER
        )


class Ieq(Infer):

    IUPPER = settings.IUPPER

    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)

    @staticmethod
    def to_expr(term):
        return Z3.parse(str(term.term))

    @staticmethod
    def inv_cls(term_ub):
        return data.inv.oct.Oct(term_ub)

    @classmethod
    def my_get_terms(cls, symbols):
        assert symbols, symbols
        assert settings.IDEG >= 1, settings.IDEG

        if settings.IDEG == 1:
            terms = Miscs.get_terms_fixed_coefs(
                symbols, settings.ITERMS, settings.ICOEFS
            )
        else:
            terms = Miscs.get_terms(list(symbols), settings.IDEG)
            terms = [t for t in terms if t != 1]
            terms = Miscs.get_terms_fixed_coefs(
                terms, settings.ITERMS, settings.ICOEFS, do_create_terms=False
            )

            terms_ = set()
            for ts in terms:
                assert ts
                ts_ = [set(t.free_symbols) for t, _ in ts]
                if len(ts) <= 1 or not set.intersection(*ts_):
                    terms_.add(sum(operator.mul(*tc) for tc in ts))
            terms = terms_
            
        if settings.UTERMS:
            uterms = cls.my_get_terms_user(symbols, settings.UTERMS)
            old_siz = len(terms)
            terms.update(uterms)
            mlog.debug(f"add {len(terms) - old_siz} new terms from user")

        terms = [data.inv.base.RelTerm(t) for t in terms]
        return terms

    @staticmethod
    def my_get_terms_user(symbols, uterms):
        assert isinstance(uterms, set) and uterms, uterms
        assert all(isinstance(t, str) for t in uterms), uterms

        uterms = set(sympy.sympify(term) for term in uterms)

        if not set(v for t in uterms for v in t.free_symbols).issubset(set(symbols)):
            raise NameError(f"{uterms} contain symbols not in {symbols}")
        terms = set()
        for t in uterms:
            terms.add(t)
            terms.add(-t)
            ts = [t_ for v in symbols for t_ in (v+t, v-t, -v+t, -v-t)]
            for t_ in ts:
                if isinstance(t_, sympy.Number):
                    mlog.warning(f"skipping {t_}")
                else:
                    terms.add(t_)

        return terms

    @staticmethod
    def get_excludes(terms, inps):
        excludes = set()
        for term in terms:
            t_symbs = set(map(str, term.symbols))
            if len(t_symbs) <= 1:  # ok for finding bound of single input val
                continue

            if inps.issuperset(t_symbs):
                excludes.add(term)
        return excludes


class MMP(Infer):
    """
    Min-max plus invariants
    """
    IUPPER = settings.IUPPER_MMP

    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)

    @staticmethod
    def to_expr(term):
        return data.inv.mp.MMP(term, is_ieq=None).expr

    @staticmethod
    def inv_cls(term_ub):
        return data.inv.mp.MMP(term_ub)

    @classmethod
    def my_get_terms(cls, symbols):
        terms = data.inv.mp.MPTerm.get_terms(symbols)
        terms = [(a, b) for a, b in terms if len(b) >= 2]  # ignore oct invs

        def _get_terms(terms, is_max):
            terms_ = [(b, a) for a, b in terms]
            return [data.inv.mp.MPTerm.mk(a, b, is_max) for a, b in terms + terms_]

        terms_max = _get_terms(terms, is_max=True)
        terms_min = _get_terms(terms, is_max=False)
        return terms_min + terms_max

    @staticmethod
    def get_excludes(terms, inps):
        assert isinstance(terms, list)
        assert all(isinstance(t, data.inv.mp.MPTerm) for t in terms), terms
        assert isinstance(inps, set), inps

        def is_pure(xs):
            # if it's small, then we won't be too strict and allow it
            return (
                len(xs) <= 2
                or all(x in inps for x in xs)
                or all(x not in inps for x in xs)
            )

        excludes = set()
        for term in terms:
            a_symbs = set(map(str, Miscs.get_vars(term.a)))
            b_symbs = set(map(str, Miscs.get_vars(term.b)))
            # print(term, a_symbs, b_symbs)

            if not is_pure(a_symbs) or not is_pure(b_symbs):
                excludes.add(term)
                # print('excluding, not pure', term)
                continue

            inp_in_a = any(s in inps for s in a_symbs)
            inp_in_b = any(s in inps for s in b_symbs)

            # exclude if (inp in both a and b) or inp not in a or b
            if (inp_in_a and inp_in_b) or (not inp_in_a and not inp_in_b):
                excludes.add(term)
                continue

            t_symbs = set.union(a_symbs, b_symbs)

            if len(t_symbs) <= 1:  # finding bound of single input val,
                continue

            if inps.issuperset(t_symbs) or all(s not in inps for s in t_symbs):
                excludes.add(term)

        return excludes
