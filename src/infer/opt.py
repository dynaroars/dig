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

        dinvs = infer.inv.DInvs()

        if not termss:
            return dinvs

        mlog.debug(f"check upperbounds for {sum(map(len, termss))} "
                   f"terms at {len(locs)} locs")

        refs = {
            loc: {self.inv_cls(t.mk_le(self.IUPPER)): t for t in terms}
            for loc, terms in zip(locs, termss)
        }
        ieqs = infer.inv.DInvs()
        for loc in refs:
            for inv in refs[loc].keys():
                ieqs.setdefault(loc, infer.inv.Invs()).add(inv)

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

        dinvs = infer.inv.DInvs()
        for loc, term, v in wrs:
            if v is None:
                continue
            inv = self.inv_cls(term.mk_le(v))
            inv.set_stat(infer.inv.Inv.PROVED)
            dinvs.setdefault(loc, infer.inv.Invs()).add(inv)

        return dinvs

    def maximize(self, loc, term, extra_constr, dtraces):
        assert isinstance(loc, str) and loc, loc
        # assert isinstance(term, (infer.inv.RelTerm, infer.mp.MPTerm)), (
        #     term,
        #     type(term),
        # )
        assert extra_constr is None or z3.is_expr(extra_constr), extra_constr
        assert isinstance(dtraces, data.traces.DTraces), dtraces

        iupper = self.IUPPER

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
