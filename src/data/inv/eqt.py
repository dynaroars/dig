import operator
import pdb
import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs
import data.inv.base
import data.traces
DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Eqt(data.inv.base.RelInv):
    def __init__(self, eqt, stat=None):
        assert eqt.operator() == operator.eq, eqt
        super().__init__(eqt, stat)

    def test_single_trace(self, trace):
        assert isinstance(trace, data.traces.Trace), trace

        # temp fix: disable repeating rational when testing equality
        if (any(not x.is_integer() and Miscs.is_repeating_rational(x)
                for x in trace.vs)):
            mlog.debug("skip trace with repeating rational {}".format(self))
            return True

        return super().test_single_trace(trace)
