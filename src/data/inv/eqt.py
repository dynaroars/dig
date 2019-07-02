"""
"""

import operator
import pdb
import settings
import helpers.vcommon as CM

import data.inv.base

dbg = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class EqtInv(data.inv.base.RelInv):
    def __init__(self, eqt, stat=None):
        assert eqt.operator() == operator.eq, eqt
        super(EqtInv, self).__init__(eqt, stat)

    @property
    def is_eqt(self):
        return True
