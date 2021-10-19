import operator
import pdb
import sympy
import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs
import data.inv.base
import data.traces
DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Eqt(data.inv.base.RelInv):
    def __init__(self, eqt, stat=None):
        assert isinstance(eqt, sympy.Equality) and eqt.rhs == 0, eqt
        super().__init__(eqt, stat)

    @property
    def mystr(self):
        return f"{self.inv.lhs} == {self.inv.rhs}"
