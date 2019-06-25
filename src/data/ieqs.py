import operator
import pdb

import settings
import helpers.vcommon as CM

import data.invs

dbg = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class IeqInv(data.invs.RelInv):
    def __init__(self, ieq, stat=None):
        """
        For both <=  (normal OctInvs)  or < (Precond in PrePost)
        """
        assert (ieq.operator() == operator.le or
                ieq.operator() == operator.lt), ieq

        super(IeqInv, self).__init__(ieq, stat)

    @property
    def is_ieqinv(self):
        return True
