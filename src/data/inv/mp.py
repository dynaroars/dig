import pdb

import z3
import helpers.vcommon as CM
from helpers.miscs import Z3
import settings

import data.poly.mp
import data.inv.base
from data.traces import Trace

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class MP(data.inv.base.Inv):
    def __init__(self, term, is_ieq=True, stat=None):
        assert isinstance(term, data.poly.mp.MP)
        hash_contents = (term.a, term.b, term.is_max, is_ieq)
        super().__init__(hash_contents, stat)
        self.term = term
        self.is_ieq = is_ieq

    def __str__(self, print_stat=False):
        s = "{} {} 0".format(self.term, '<=' if self.is_ieq else '==')
        if print_stat:
            s = "{} {}".format(s, self.stat)
        return s

    def expr(self, use_reals):
        """
        # sage: x, y, z = sage.all.var('x y z')
        # sage: mp = MPInv.mk_max_ieq((x-10, y-3), (y, 5))
        # sage: mp.expr(use_reals=False)
        # If(x + -10 >= y + -3, If(y >= 5, x + -10 <= y, x + -10 <= 5),
        #    If(y >= 5, y + -3 <= y, y + -3 <= 5))

        # sage: MPInv.mk_max_ieq((x,), (y,z,0)).expr(use_reals=False)
        # If(And(y >= z, y >= 0), x <= y, If(z >= 0, x <= z, x <= 0))
        """

        a = tuple(Z3.parse(str(x), use_reals) for x in self.term.a)
        b = tuple(Z3.parse(str(x), use_reals) for x in self.term.b)

        expr = self.mp2df_expr(a, b, 0, self.term.is_max, self.is_ieq)

        if len(b) >= 3:  # more simplification
            expr = Z3.simplify(expr)

        return expr

    def test_single_trace(self, trace):
        assert isinstance(trace, Trace), trace
        trace = trace.mydict_str
        bval = data.poly.mp._eval(str(self), trace)
        assert isinstance(bval, bool), bval
        return bval

    @classmethod
    def mp2df_expr(cls, a, b, idx, is_max, is_ieq):
        """
        # sage: x, y = z3.Ints('x y')
        # sage: MPInv.mp2df_expr((x-z3.IntVal('10'), y-z3.IntVal('3')), \
        #                        (y+z3.IntVal('12'),), 0, is_max=True, is_ieq=True)
        # If(x - 10 >= y - 3, x - 10 <= y + 12, y - 3 <= y + 12)
        """
        assert isinstance(a, tuple) and a

        elem = a[idx]
        if isinstance(b, tuple):
            ite = cls.mp2df_expr(b, elem, 0, is_max, is_ieq)
        else:
            if is_ieq:
                ite = b <= elem
            else:
                ite = b >= elem

            # ite = "{} {} {}".format(b, '<=' if is_ieq else '==', elem)
        rest = a[idx + 1:]

        if not rest:  # t <= max(x,y,z)
            return ite
        else:
            rest_ite = cls.mp2df_expr(a, b, idx + 1, is_max, is_ieq)

            others = a[:idx] + rest

            # conds = ["{} {} {}".format(
            #     elem, '>=' if is_max else '<=', t) for t in others]

            conds = [elem >= t if is_max else elem <= t for t in others]
            if len(conds) >= 2:
                cond = z3.And(*conds)
            else:
                cond = conds[0]

            return z3.If(cond, ite, rest_ite)
