from abc import ABCMeta, abstractmethod
import pdb
import operator
from typing import NamedTuple

import sympy

from helpers.miscs import Miscs
from helpers.z3utils import Z3
import helpers.vcommon as CM
import settings
import data.traces


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Inv(metaclass=ABCMeta):

    PROVED = "p"
    DISPROVED = "d"
    UNKNOWN = "u"

    def __init__(self, inv, stat=None):
        """
        stat = None means never been checked
        """
        assert (inv == 0 or  # FalseInv
                # PrePost and Max/MinPlus
                (isinstance(inv, tuple) and (len(inv) == 2 or len(inv) == 4)) or
                isinstance(inv, str) or   # Array relation
                isinstance(inv, (sympy.Equality, sympy.Le))), inv

        assert stat in {None, Inv.PROVED, Inv.DISPROVED, Inv.UNKNOWN}

        self.inv = inv
        if stat is None:
            self.reset_stat()
        else:
            self.stat = stat

    def __hash__(self):
        return hash(self.inv)

    def __repr__(self):
        return repr(self.inv)

    def __eq__(self, o):
        assert isinstance(o, Inv), o
        return self.inv.__eq__(o.inv)

    def __ne__(self, o):
        return not self.inv.__eq__(o.inv)

    def get_stat(self):
        return self._stat

    def set_stat(self, stat):
        assert stat in {self.PROVED, self.DISPROVED, self.UNKNOWN}, stat
        self._stat = stat

    stat = property(get_stat, set_stat)

    def reset_stat(self):
        self._stat = None

    def test(self, traces):
        assert isinstance(traces, data.traces.Traces), traces
        return all(self.test_single_trace(trace) for trace in traces)

    @property
    def is_proved(self):
        return self.stat == self.PROVED

    @property
    def is_disproved(self):
        return self.stat == self.DISPROVED

    @property
    def is_unknown(self):
        return self.stat == self.UNKNOWN

    @abstractmethod
    def test_single_trace(self, trace):
        pass


class RelInv(Inv, metaclass=ABCMeta):
    def __init__(self, rel, stat=None):
        assert isinstance(rel, (sympy.Equality, sympy.Le)), rel
        super().__init__(rel, stat)

    @property
    @abstractmethod
    def mystr(self):
        pass

    def __str__(self, print_stat=False):
        s = self.mystr
        if print_stat:
            s = f"{s} {self.stat}"
        return s

    def test_single_trace(self, trace):
        assert isinstance(trace, data.traces.Trace), trace

        # temp fix: disable traces that wih extreme large values
        # (see geo1 e.g., 435848050)
        if any(x > settings.TRACE_MAX_VAL for x in trace.vs):
            mlog.debug(f"{self}: skip trace with large val: {trace.vs}")
            return True

        try:
            bval = bool(self.inv.subs(trace.mydict))
            return bval
        except ValueError:
            mlog.debug(f"{self}: failed test")
            return False

    @property
    def expr(self):
        """
        cannot cache because z3 expr is ctype,
        not compat with multiprocessing Queue

        also, cannot save this to sel._expr
        """
        return Z3.parse(str(self))


class RelTerm(NamedTuple):
    """
    e.g., x + y,  x,  x + 3
    """

    term: sympy.Expr

    @classmethod
    def mk(cls, term):
        assert (
            isinstance(term, sympy.Expr)
            and not term.is_relational()
        ), term
        return cls(term)

    @property
    def symbols(self):
        return Miscs.get_vars(self.term)

    def eval_traces(self, traces, pred=None):
        return traces.myeval(self.term, pred)

    def mk_lt(self, val):
        return self._mk_rel(operator.lt, val)

    def mk_le(self, val):
        return self._mk_rel(operator.le, val)

    def mk_eq(self, val):
        return self._mk_rel(operator.eq, val)

    def _mk_rel(self, myop, val):
        """
        return myop(self.term, val), e.g., x + y <= 8
        """
        assert myop == operator.eq or myop == operator.le or myop == operator.lt, myop

        return myop(self.term, val)
