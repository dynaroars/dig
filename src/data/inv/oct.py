import operator
import pdb
import sympy
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
        assert isinstance(myoct, sympy.Le), myoct

        super().__init__(myoct, stat)

    @property
    def is_simple(self):
        return self.inv.rhs.is_constant() and self.inv.rhs.is_zero

    @property
    def mystr(self):
        return f"{self.inv.lhs} <= {self.inv.rhs}"
