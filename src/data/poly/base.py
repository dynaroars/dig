from abc import ABCMeta, abstractmethod

import pdb
import operator

import helpers.vcommon as CM
import settings
from helpers.miscs import Miscs


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Poly(metaclass=ABCMeta):

    def __init__(self, poly):
        self.poly = poly

    def __hash__(self): return hash(self.poly)

    def __repr__(self): return repr(self.poly)

    def __eq__(self, o): return self.poly.__eq__(o.poly)

    @abstractmethod
    def eval_traces(self, traces):
        pass

    @abstractmethod
    def mk_le(self, val):
        pass


class GeneralPoly(Poly):
    """
    e.g., x + y,  x,  x + 3
    """

    def __init__(self, poly):
        assert Miscs.is_expr(poly), poly

        super().__init__(poly)

    @property
    def symbols(self):
        try:
            return self._symbols
        except AttributeError:
            self._symbols = Miscs.get_vars(self.poly)
            return self._symbols

    def eval_traces(self, traces):
        return traces.myeval(self.poly)

    def mk_lt(self, val):
        return self._mk_rel(operator.lt, val)

    def mk_le(self, val):
        return self._mk_rel(operator.le, val)

    def mk_eq(self, val):
        return self._mk_rel(operator.eq, val)

    def _mk_rel(self, myop, val):
        """
        return myop(self.poly, val), e.g., x + y <= 8
        """
        assert (myop == operator.eq or
                myop == operator.le or
                myop == operator.lt), myop

        return myop(self.poly, val)

    @classmethod
    def get_terms(cls, terms):
        return Miscs.get_terms_fixed_coefs(terms, 2)
