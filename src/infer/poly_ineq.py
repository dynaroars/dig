"""
Polynomial inequality invariants: degree-2 upper/lower bounds.
Found from traces only (no symbolic states required).
e.g., q*r <= 10, a^2 <= 4
"""
import pdb
import sympy
from beartype import beartype

import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs

import infer.inv
import infer.infer
import data.prog
import data.traces

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class PolyIneq(infer.inv.Inv):
    """
    Degree-2 polynomial inequality: p(vars) <= bound
    """

    @beartype
    def __init__(self, inv: sympy.Le, stat: infer.inv.InvStat | None = None) -> None:
        super().__init__(inv, stat)

    @property
    def mystr(self) -> str:
        return f"{self.inv.lhs} <= {self.inv.rhs}"

    @property
    def cinvs_category(self) -> str:
        return 'poly_ineqs'


class Infer(infer.infer._Infer):

    def gen(self) -> infer.inv.DInvs:
        raise NotImplementedError("poly_ineq uses gen_from_traces only")

    @classmethod
    def gen_from_traces(cls, traces: data.traces.Traces,
                        symbols: data.prog.Symbs) -> list:
        """
        For each degree-2 monomial p = x*y, find the tightest upper bound M
        such that p <= M holds for all traces.  Only report if M is within the
        configured threshold so that trivially large bounds are suppressed.
        """
        syms = [s for s in symbols.symbolic if not s.is_number]
        threshold = settings.POLY_IUPPER

        terms = []
        for i, x in enumerate(syms):
            for y in syms[i:]:
                terms.append(infer.inv.RelTerm(x * y))

        results = []
        for term in terms:
            vals = term.eval_traces(traces)
            if not vals:
                continue

            try:
                ivals = [int(v) for v in vals]
            except (TypeError, ValueError):
                continue

            if len(set(ivals)) == 1:
                continue  # constant — eqts already handles this

            max_v = max(ivals)
            min_v = min(ivals)

            if 0 < max_v <= threshold:
                results.append(PolyIneq(sympy.Le(term.term, max_v)))
            if -threshold <= min_v < 0:
                results.append(PolyIneq(sympy.Le(-term.term, -min_v)))

        return results
