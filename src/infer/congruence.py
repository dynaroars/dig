import pdb
from functools import reduce
from math import gcd
import typing

import sympy
import z3

import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs
from helpers.z3utils import Z3
import infer.inv
import infer.infer
import data.traces


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

    @property
    def expr(self) -> z3.ExprRef:
        a = Z3.parse(str(self.a))
        b = Z3.parse(str(self.b))
        c = Z3.parse(str(self.n))
        return a % b == c

    def _eval(self, trace: data.traces.Trace) -> bool:
        v = int(self.a.xreplace(trace.mydict))
        b = (v % self.n) == self.b
        return b


class Congruence(infer.inv.Inv):
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

    @property
    def expr(self) -> z3.ExprRef:
        return self.inv.expr

    def test_single_trace(self, trace: data.traces.Traces) -> bool:
        assert isinstance(trace, data.traces.Trace), trace
        b = self.inv._eval(trace)
        return b


class Infer(infer.infer._Infer):

    def gen(self, traces: data.traces.DTraces, inps: data.traces.Inps) -> infer.inv.DInvs:

        locs = traces.keys()
        # tasks = [
        #     (loc, self._get_init_traces
        #     ]

        return infer.inv.DInvs()

    @classmethod
    def gen_from_traces(cls, traces, symbols):
        ps = []
        terms = Miscs.get_terms_fixed_coefs(
            symbols.sageExprs, settings.ITERMS, settings.ICOEFS)
        for term in terms:
            term_vals = infer.inv.RelTerm(term).eval_traces(traces)
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


if __name__ == "__main__":
    import doctest
    doctest.testmod()
