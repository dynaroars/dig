"""
Polynomial congruence invariants: degree-2 modular relations.

Generalises infer/congruence.py to degree-2 terms.  For each degree-2
monomial p = x*y, finds n > 1 and c such that  p ≡ c (mod n)  holds across
all traces.

The modulus n is the GCD of  {p(t) - p(t0)}  for all traces t.  If that GCD
is > 1 the invariant is  p mod n == p(t0) mod n.
"""
import pdb
from functools import reduce
from math import gcd
from typing import NamedTuple
from beartype import beartype

import sympy
import z3

import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs
from helpers.z3utils import Z3
import infer.inv
import infer.infer
import data.prog
import data.traces


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class PolyModSpec(NamedTuple):
    """p ≡ b (mod n)"""
    term: sympy.Expr  # degree-2 term
    b: int
    n: int

    def __str__(self) -> str:
        return f"{self.term} === {self.b} (mod {self.n})"

    def eval(self, trace: data.traces.Trace) -> bool:
        v = int(self.term.xreplace(trace.mydict))
        return (v % self.n) == self.b

    @property
    def expr(self) -> z3.ExprRef:
        a = Z3.parse(str(self.term))
        b = Z3.parse(str(self.b))
        c = Z3.parse(str(self.n))
        return a % c == b


class PolyCong(infer.inv.Inv):
    """Invariant  p(vars) ≡ b (mod n)  for a degree-2 polynomial p."""

    @beartype
    def __init__(self, inv, stat: infer.inv.InvStat | None = None) -> None:
        assert isinstance(inv, PolyModSpec), inv
        super().__init__(inv, stat)

    @beartype
    @classmethod
    def mk(cls, term: sympy.Expr, b: int, n: int) -> infer.inv.Inv:
        return cls(PolyModSpec(term, b, n))

    @property
    def mystr(self) -> str:
        return str(self.inv)

    @property
    def cinvs_category(self) -> str:
        return 'poly_congs'

    @beartype
    def test_single_trace(self, trace: data.traces.Trace) -> bool:
        return self.inv.eval(trace)

    @beartype
    @property
    def expr(self) -> z3.ExprRef:
        return self.inv.expr


class Infer(infer.infer._Infer):

    def gen(self) -> infer.inv.DInvs:
        raise NotImplementedError("poly_cong uses gen_from_traces only")

    @classmethod
    def gen_from_traces(cls, traces: data.traces.Traces,
                        symbols: data.prog.Symbs) -> list:
        """
        For each degree-2 monomial, compute the GCD of differences from the
        first trace value.  If the GCD is > 1, the term has a modular invariant.
        """
        syms = [s for s in symbols.symbolic if not s.is_number]
        results = []

        monomials = []
        for i, x in enumerate(syms):
            for y in syms[i:]:
                monomials.append(x * y)

        for term in monomials:
            rterm = infer.inv.RelTerm(term)
            vals = rterm.eval_traces(traces)
            if not vals:
                continue

            try:
                ivals = [int(v) for v in vals]
            except (TypeError, ValueError):
                continue

            if len(set(ivals)) == 1:
                continue  # constant — eqts already handles this

            diffs = [ivals[0] - v for v in ivals]
            try:
                g = reduce(gcd, diffs)
            except TypeError:
                continue

            if g <= 1 or g == -1:
                continue

            b = ivals[0] % g
            p = PolyCong.mk(term, b, g)
            # Verify against all traces
            if not all(p.test_single_trace(t) for t in traces):
                continue
            results.append(p)

        return results
