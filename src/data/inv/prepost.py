import pdb

import z3
import helpers.vcommon as CM


import settings
from data.inv.base import Inv
import data.inv.invs

dbg = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class PrePost(Inv):
    """
    Set of Preconds  -> PostInv
    """

    def __init__(self, preconds, postcond, stat=None):
        assert isinstance(preconds, data.inv.invs.Invs), preconds
        # assert postcond.is_eqt, postcond

        super(PrePost, self).__init__(
            (frozenset(preconds), postcond), stat)

        self.preconds = preconds
        self.is_conj = True   # conj preconds
        self.postcond = postcond

    def expr(self, use_reals):
        """
        And(preconds) -> postcond
        """
        if self.is_conj:
            pre = z3.And([c.expr(use_reals) for c in self.preconds])
        else:
            pre = z3.Or([c.expr(use_reals) for c in self.preconds])
        post = c.expr(use_reals)
        return z3.Implies(pre, post)

    def __str__(self, print_stat=False):
        delim = " & " if self.is_conj else " | "
        return "({}) => {} {}".format(
            self.preconds.__str__(delim=delim),
            self.postcond, self.stat)
