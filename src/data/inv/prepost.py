import pdb

import z3
import helpers.vcommon as CM


import settings
from data.inv.base import Inv
from data.inv.invs import Invs

dbg = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class PrePost(Inv):
    """
    Set of Preconds  -> PostInv
    """

    def __init__(self, preconds, postcond, stat=None):
        assert isinstance(preconds, Invs), preconds
        #assert postcond.is_eqt, postcond

        super(PrePost, self).__init__(
            (frozenset(preconds), postcond), stat)

        self.preconds = preconds
        self.postcond = postcond

    def expr(self, use_reals):
        """
        And(preconds) -> postcond
        """
        pre = z3.And([c.expr(use_reals) for c in self.preconds])
        post = c.expr(use_reals)
        return z3.Implies(pre, post)

    def __str__(self, print_stat=False):
        return "{} => {} {}".format(
            self.preconds.__str__(delim=" & "), self.postcond, self.stat)
