import pdb
from functools import reduce
from math import gcd
import sympy
import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs, MP

from data.traces import Inps, Traces, DTraces
from data.inv.invs import Invs, DInvs
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
            b,n = cls.solve(term_vals)
            if b is None:
                continue
            p = data.inv.congruence.MyCongruence(term, b, n)
            ps.append(data.inv.congruence.Congruence(p))

        return ps

        
    #def found(X, n):
    #    b = X[0] % n
    #    return b,n
        #print(f'n={n} b={b}')
        #check(X, n, b)


    def solve(X)->tuple:
        assert(X), X
        b = None
        #print(f'X={X}')
        Y = [X[0] - v for v in X]
        #print('Y', Y)
        g = reduce(gcd, Y)
        if g >= 2:
        #print('g', g)
        #found(X, g)
            b = X[0] % g
        else:
            g = None
        return b, g