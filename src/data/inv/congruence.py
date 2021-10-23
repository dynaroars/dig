import pdb
import typing

import sympy

import helpers.vcommon as CM
from helpers.miscs import Miscs
from helpers.z3utils import Z3
import settings

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

    def _eval(self, trace:data.traces.Trace) -> bool:
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
    def mk(cls, term, b,n):
        return cls(MyCongruence(term, b, n))

    @property
    def mystr(self) -> str:
        return str(self.inv)

    def test_single_trace(self, trace:data.traces.Traces) -> bool:
        assert isinstance(trace, data.traces.Trace), trace
        b = self.inv._eval(trace)
        return b


if __name__ == "__main__":
    import doctest
    doctest.testmod()
