from abc import ABCMeta
import pdb
import operator
from typing import NamedTuple

import sage.all

from helpers.miscs import Z3, Miscs
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
        assert (inv == 0  # FalseInv
                or (isinstance(inv, tuple)
                    and (len(inv) == 2  # PrePost
                         or len(inv) == 4))  # Max/MinPlus
                or inv.is_relational()), inv

        assert stat in {None, Inv.PROVED, Inv.DISPROVED, Inv.UNKNOWN}

        self.inv = inv
        if stat is None:
            self.reset_stat()
        else:
            self.stat = stat

    def __hash__(self): return hash(self.inv)

    def __repr__(self): return repr(self.inv)

    def __eq__(self, o):
        assert isinstance(o, Inv), o
        return self.inv.__eq__(o.inv)

    def __ne__(self, o): return not self.inv.__eq__(o.inv)

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
    def is_proved(self): return self.stat == self.PROVED

    @property
    def is_disproved(self): return self.stat == self.DISPROVED

    @property
    def is_unknown(self): return self.stat == self.UNKNOWN


class RelInv(Inv, metaclass=ABCMeta):

    def __init__(self, rel, stat=None):
        assert (rel.operator() == operator.eq or
                rel.operator() == operator.le or
                rel.operator() == operator.lt), rel

        super().__init__(rel, stat)

    def __str__(self, print_stat=False):
        s = str(self.inv)
        if print_stat:
            s = "{} {}".format(s, self.stat)
        return s

    def test_single_trace(self, trace):
        assert isinstance(trace, data.traces.Trace), trace

        # temp fix: disable traces that wih extreme large values
        # (see geo1 e.g., 435848050)
        if any(x > trace.max_val for x in trace.vs):
            mlog.debug(
                "{}: skip trace with large val: {}".format(self, trace.vs))
            return True

        try:
            bval = self.inv.subs(trace.mydict)
            bval = bool(bval)
            return bval
        except ValueError:
            mlog.debug("{}: failed test".format(self))
            return False

    @property
    def expr(self):
        """
        cannot make this as property because z3 expr is ctype,
        not compat with multiprocessing Queue

        also, cannot save this to sel._expr
        """
        return Z3.parse(str(self.inv))


class RelTerm(NamedTuple):
    """
    e.g., x + y,  x,  x + 3
    """
    term: sage.symbolic.expression.Expression

    @classmethod
    def mk(cls, term):
        assert isinstance(term, sage.symbolic.expression.Expression), term
        return cls(term)

    @property
    def symbols(self):
        return Miscs.get_vars(self.term)

    def eval_traces(self, traces, pred):
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
        assert (myop == operator.eq or
                myop == operator.le or
                myop == operator.lt), myop

        return myop(self.term, val)
