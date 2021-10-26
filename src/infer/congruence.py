import pdb
from functools import reduce
from math import gcd
import typing

import sympy

import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs
import infer.base
import data.traces
import data.inv.base

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class MyCongruence(typing.NamedTuple):
    """
    a === b (mod n)

    x == 0 (mod 4)      #0,4,8,12,..
    x + y == 1 (mod 5)   # 1,6,11,16 ...
    """
    a: sympy.Expr
    b: int
    n: int

    def __str__(self) -> str:
        s = f"{self.a} === {self.b} (mod {self.n})"
        return s

    def _eval(self, trace: data.traces.Trace) -> bool:
        v = int(self.a.xreplace(trace.mydict))
        b = (v % self.n) == self.b
        return b


class Congruence(data.inv.base.Inv):
    def __init__(self, mycongruence, stat=None):
        """
            """
        assert isinstance(mycongruence, MyCongruence), mycongruence

        super().__init__(mycongruence, stat)

    @classmethod
    def mk(cls, term, b, n):
        return cls(MyCongruence(term, b, n))

    @property
    def mystr(self) -> str:
        return str(self.inv)

    def test_single_trace(self, trace: data.traces.Traces) -> bool:
        assert isinstance(trace, data.traces.Trace), trace
        b = self.inv._eval(trace)
        return b


class Infer(infer.base.Infer):
    @classmethod
    def gen_from_traces(cls, traces, symbols):
        ps = []
        terms = Miscs.get_terms_fixed_coefs(
            symbols.sageExprs, settings.ITERMS, settings.ICOEFS)
        for term in terms:
            term_vals = data.inv.base.RelTerm(term).eval_traces(traces)
            b, n = cls._solve(term_vals)
            if b is None:
                continue
            p = Congruence.mk(term, b, n)
            ps.append(p)

        return ps

    @classmethod
    def _solve(cls, X: typing.List[int]) -> typing.Tuple[typing.Optional[int], int]:
        assert(X), X
        b = None
        Y = [X[0] - v for v in X]
        g = reduce(gcd, Y)
        if g == 1 or g == -1:
            g = None
        else:
            b = X[0] % g
        return b, g
