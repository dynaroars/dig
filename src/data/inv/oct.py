import operator
import pdb

import settings
import helpers.vcommon as CM

import data.inv.base

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Oct(data.inv.base.RelInv):
    def __init__(self, myoct, stat=None):
        """
        For both <=  (normal OctInvs)  or < (Precond in PrePost)
        """
        assert myoct.operator() == operator.le or myoct.operator() == operator.lt, myoct

        super().__init__(myoct, stat)

    @property
    def is_simple(self):
        ub = self.inv.rhs()
        # need to convert to bool because ub.is_zero() might return 0 == 0
        return bool(ub.is_constant() and ub.is_zero())
