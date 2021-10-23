import pdb
from functools import reduce
from math import gcd
import typing
import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs
import data.inv.congruence
import infer.base

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)

class Congruence(infer.base.Infer):
    @classmethod
    def gen_from_traces(cls, traces, symbols):
        ps = []
        terms = Miscs.get_terms_fixed_coefs(symbols.sageExprs, settings.ITERMS, settings.ICOEFS)
        for term in terms:
            term_vals = data.inv.base.RelTerm(term).eval_traces(traces)
            b,n = cls._solve(term_vals)
            if b is None:
                continue
            p = data.inv.congruence.Congruence.mk(term, b, n)
            ps.append(p)

        return ps

    @classmethod
    def _solve(cls, X:typing.List[int] ) -> typing.Tuple[typing.Optional[int], int]:
        assert(X), X
        b = None
        Y = [X[0] - v for v in X]
        g = reduce(gcd, Y)
        if g ==1 or g == -1:
            g = None
        else:
            b = X[0] % g
        return b, g