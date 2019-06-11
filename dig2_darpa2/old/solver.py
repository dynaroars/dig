import abc
from collections import OrderedDict, MutableSet, MutableMapping
import collections
import itertools
import random
import os.path
import sage.all

import vu_common as CM
import sageutil
import settings
logger = CM.VLog('solver')
logger.level = settings.logger_level  

import miscs

#Exceptions
class NotEnoughTraces(Exception): pass
class SameInsts(Exception): pass

isIterator = lambda it: isinstance(it, collections.Iterator)
def getTermsFixedCoefs(ss, subsetSiz):
    """
    sage: var('x y z t s u')
    (x, y, z, t, s, u)

    sage: getTermsFixedCoefs([x,y^2], 2)
    [-y^2 - x, -x, y^2 - x, -y^2, y^2, -y^2 + x, x, y^2 + x]
    """
    if len(ss) < subsetSiz: subsetSiz = len(ss)
    rs = []
    for ssSubset in itertools.combinations(ss, subsetSiz):
        css = itertools.product(*([[0, -1, 1]] * len(ssSubset)))
        r = (sum(c*t for c,t in zip(ssSubset, cs))
             for cs in css if not all(c == 0 for c in cs))
        rs.extend(r)
    return CM.vset(rs)

def getTermsFixedCoefsHalf(terms):
    """
    sage: var('x y z t s u')
    (x, y, z, t, s, u)

    sage: getTermsFixedCoefs([x,y^2], 2)
    {-y^2, -y^2 - x, -x, y^2 - x}
    """

    rs = []
    for t in terms:
        if t not in rs:
            rs.append(-1*t)
    return rs
            

def reducePoly(ps):
    """
    Return the basis (e.g., a min subset of ps that implies ps) 
    of the set of eqts input ps using Groebner basis

    sage: var('a y b q k')
    (a, y, b, q, k)

    sage: rs =  reducePoly([a*y-b==0,q*y+k-x==0,a*x-a*k-b*q==0])
    sage: assert set(rs) == set([a*y - b == 0, q*y + k - x == 0])

    sage: rs =  reducePoly([x*y==6,y==2,x==3])
    sage: assert set(rs) == set([x - 3 == 0, y - 2 == 0])

    #Attribute error occurs when only 1 var, thus return as is
    sage: rs =  reducePoly([x*x==4,x==2])
    sage: assert set(rs) == set([x == 2, x^2 == 4])
    """
    assert ps, ps
    assert (p.operator() == sage.all.operator.eq for p in ps), ps
    try:
        Q = sage.all.PolynomialRing(sage.all.QQ, sageutil.get_vars(ps))
        I = Q*ps
        ps = I.radical().interreduced_basis()
        ps = [(sage.all.SR(p) == 0) for p in ps]
    except AttributeError:
        pass

    return ps

def getCoefsLen(p):
    try:
        Q = sage.all.PolynomialRing(sage.all.QQ, sageutil.get_vars(ps))
        rs = Q(p.lhs()).coefficients()
        rs = (abs(r_.n()).str(skip_zeroes=True)
              for r_ in rs if r_ != 0.0)
        rs = (sum(map(len,r_.split('.'))) for r_ in rs)
        rs = sum(rs)
        return rs
    except Exception:
        return len(str(p))

#### Solvers for different forms of invariants ###
class Solver(object):
    __metaclass__ = abc.ABCMeta
    @abc.abstractmethod
    def solve(self, traces): return

class EqtSolver(Solver):
    maxV =  1000
    minV = -1*maxV

    RATE = 1.7  # RATE * terms

    def solve(self, terms, traces, exprs):
        invs = self._solve(terms, traces, exprs)
        invs = self.refine(invs)
        return invs

    @classmethod
    def _solve(cls, terms, traces, exprs):
        """
        sage: var('x y')
        (x, y)
        sage: ts = [1, x, y, x^2, x*y, y^2]
        sage: traces = [{y: 1, x: 1}, {y: 2, x: 4}, {y: 4, x: 16}, {y: 0, x: 0}, {y: 8, x: 64}, {y: 9, x: 81}, {y: -1, x: 1}, {y: 5, x: 25}]
        sage: assert EqtSolver(traces).solve(ts) == [y**2 - x == 0]

        sage: EqtSolver(traces[:2]).solve(ts)
        Traceback (most recent call last):
        ...
        NotEnoughTraces: cannot solve 6 unknowns with only 2 eqts
        """
        
        template, coefVars = Template.mk(terms, 0, retCoefVars=True)
        assert len(terms) == len(coefVars), (terms, coefVars)
        
        minEqts = int(round(len(terms) * EqtSolver.RATE))
        nexprs = len(exprs)
        traces = sorted(traces, key=lambda t: sum(t.itervalues()))
        for i,t in enumerate(traces):
            eqt = template.template.subs(t._dict)
            if eqt not in exprs:
                exprs.add(eqt)
                if len(exprs) >= minEqts:
                    break

        if minEqts > len(exprs):
            err = "need more traces ({} uks, {} eqts, request {} eqts)".format(
                len(terms), len(exprs), minEqts)
            raise NotEnoughTraces(err)

        if  len(exprs) == nexprs:
            raise SameInsts("similar instantiations".format(len(exprs)))
        
        logger.debug("solving {} unknowns using {} eqts"
                     .format(len(coefVars), len(exprs)))

        sols = sage.all.solve(list(exprs), coefVars, solution_dict=True)
        sols = template.instantiateSols(sols)
        return sols

    @classmethod
    def refine(cls, sols):
        if len(sols) <= 1:
            return sols

        sols = reducePoly(sols)
        sols = [s for s in sols if getCoefsLen(s) <= 100]
        return sols

class IeqSolver(Solver):
    maxV =  100000
    minV = -1 * maxV
    
    def solve(self, terms, traces, exprs, subsetSiz):
        return self._solve(terms, traces, exprs, subsetSiz)
    
    @classmethod
    def _solve(cls, terms, traces, exprs, subsetSiz):
        if isIterator(traces): traces = list(traces)
        terms = cls.getTermsFixedCoefs(terms, subsetSiz)
        rs = []
        for t in terms:
            minTraceV = min(t.subs(trace) for trace in traces)
            if minTraceV > cls.minV:
                term = t - minTraceV >= 0
                rs.append(term)
        return rs

    # def solveWeak(self, terms, traces, exprs, subsetSiz):
    #     return self._solveWeak(terms, traces, exprs, subsetSiz)

    # @classmethod
    # def _solveWeak(cls, terms, traces, exprs, subsetSiz):
    #     """
    #     Return very weak but likely true invs
    #     """
    #     terms = cls.getTermsFixedCoefs(terms, subsetSiz)
    #     sols = [(t >= (cls.minV + 1), t) for t in terms]
        
    #     sols_ = [(expr, t) for expr,t in sols
    #              if all(bool(expr.subs(t._dict)) for t in traces)]
    #     return sols

    @classmethod
    def getTermsFixedCoefs(cls, terms, subsetSiz):
        terms = [t for t in terms if t != 1]
        if not subsetSiz: subsetSiz = len(terms)
        terms = getTermsFixedCoefs(terms, subsetSiz)
        return terms

    @classmethod
    def getTermsFixedCoefsHalf(cls, terms, subsetSiz):
        terms = cls.getTermsFixedCoefs(terms, subsetSiz)
        return getTermsFixedCoefsHalf(terms)
    
    
class RangeSolver(IeqSolver):
    def solve(self, terms, traces, exprs):
        return super(RangeSolver,self).solve(terms, traces, exprs, subsetSiz=1)

class RangeSolverWeak(IeqSolver):
    def solve(self, terms, traces, exprs):
        return super(RangeSolverWeak, self).solveWeak(
            terms, traces, exprs, subsetSiz=1)
    def solve1(self, terms):
        return super(RangeSolverWeak, self).genWeaks(terms, subsetSiz=1)
    def genWeaks(self, terms):
        return super(RangeSolverWeak, self).genWeaks(terms, subsetSiz=1)


# class OctSolverWeak(IeqSolver):
#     def solve(self, terms, traces, exprs):
#         return super(RangeSolverWeak, self).solveWeak(
#             terms, traces, exprs, subsetSiz=2)
#     def solve1(self, terms):
#         return super(OctSolverWeak, self).genWeaks(terms, subsetSiz=2)
#     def genWeaks(self, terms):
#         return super(OctSolverWeak, self).genWeaks(terms, subsetSiz=2)
    
class OctSolver(IeqSolver):
    def solve(self, terms, traces):
        return super(OctSolver,self).solve(terms, traces, subsetSiz=2)

    def getTerms(self, terms):
        return super(OctSolver, self).getTermsFixedCoefs(terms, subsetSiz=2)
    
# class OctSolverWeak(IeqSolver):
#     def solveWeak(self, terms, _):
#         return super(OctSolverWeak,self).solveWeak(terms, traces, subsetSiz=2)
    

class Template(object):
    def __init__(self, template):
        assert sageutil.is_sage_expr(template), template
        
        self.template = template
    def __str__(self): return str(self.template)
    def __repr__(self): return repr(self.template)

    def instantiateTraces(self, traces, nTraces):
        """
        Instantiate a (potentially nonlinear) template with traces to obtain
        a set of linear expressions.

        sage: var('a,b,x,y,uk_0,uk_1,uk_2,uk_3,uk_4')
        (a, b, x, y, uk_0, uk_1, uk_2, uk_3, uk_4)

        sage: traces = [{y: 4, b: 2, a: 13, x: 1}, {y: 6, b: 1, a: 10, x: 2}, {y: 8, b: 0, a: 7, x: 3}, {y: 10, b: 4, a: 19, x: 4}, {y: 22, b: 30, a: 97, x: 10}, {y: 28, b: 41, a: 130, x: 13}]
        sage: exprs = Template(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0).instantiateTraces(traces, nTraces=None)
        sage: assert exprs == {uk_0 + 13*uk_1 + 2*uk_2 + uk_3 + 4*uk_4 == 0,\
        uk_0 + 10*uk_1 + uk_2 + 2*uk_3 + 6*uk_4 == 0,\
        uk_0 + 7*uk_1 + 3*uk_3 + 8*uk_4 == 0,\
        uk_0 + 19*uk_1 + 4*uk_2 + 4*uk_3 + 10*uk_4 == 0,\
        uk_0 + 97*uk_1 + 30*uk_2 + 10*uk_3 + 22*uk_4 == 0,\
        uk_0 + 130*uk_1 + 41*uk_2 + 13*uk_3 + 28*uk_4 == 0}
        """
        assert (traces and (isIterator(traces) or
                            all(isinstance(t, dict) for t in traces))), traces
        assert nTraces is None or nTraces >= 1, nTraces

        #random.shuffle(traces)
        
        if nTraces is None:
            exprs = set(self.template.subs(t) for t in traces)
        else:
            exprs = set()
            for i,t in enumerate(traces):
                expr = self.template.subs(t)
                if expr not in exprs:
                    exprs.add(expr)
                    if len(exprs) > nTraces:
                        break
                        
        return exprs

    def instantiateSols(self, sols):
        """
        Instantiate a template with solved coefficient values

        sage: var('uk_0,uk_1,uk_2,uk_3,uk_4,r14,r15,a,b,y')
        (uk_0, uk_1, uk_2, uk_3, uk_4, r14, r15, a, b, y)

        #when sols are in dict form
        sage: sols = [{uk_0: -2*r14 + 7/3*r15, uk_1: -1/3*r15, uk_4: r14, uk_2: r15, uk_3: -2*r14}]
        sage: Template(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0).instantiateSols(sols)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]

        # #when sols are not in dict form
        sage: sols = [[uk_0== -2*r14 + 7/3*r15, uk_1== -1/3*r15, uk_4== r14, uk_2== r15, uk_3== -2*r14]]
        sage: Template(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0).instantiateSols(sols)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]

        sage: Template(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0).instantiateSols([])
        []
        """

        if not sols: return []

        if len(sols) > 1:
            logger.warn('instantiateTemplateWithSols: len(sols) = {}'
                        .format(len(sols)))
            logger.warn(str(sols))

        def f_eq(d):
            if isinstance(d, list):
                f_ = self.template
                for d_ in d:
                    f_ = f_.subs(d_)
                rhsVals = CM.vset([d_.rhs() for d_ in d])
                uk_vars = sageutil.get_vars(rhsVals)
            else:
                f_ = self.template(d)
                uk_vars = sageutil.get_vars(d.values()) #e.g., r15,r16 ...

            if not uk_vars: return f_

            iM = sage.all.identity_matrix(len(uk_vars)) #standard basis
            rs = [dict(zip(uk_vars,l)) for l in iM.rows()]
            rs = [f_(r) for r in rs]
            return rs

        sols = sage.all.flatten([f_eq(s) for s in sols])

        #remove trivial (tautology) str(x) <=> str(x)
        sols = [s for s in sols
                if not (s.is_relational() and str(s.lhs()) == str(s.rhs()))]

        return sols

    @classmethod
    def mk(cls, terms, rhsVal,
           op=sage.all.operator.eq,
           prefix=None, retCoefVars=False):
        """
        get a template from terms.

        Examples:

        sage: var('a,b,x,y')
        (a, b, x, y)

        sage: Template.mk([1, a, b, x, y],0,prefix=None)
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0

        sage: Template.mk([1, x, y],0,\
        op=operator.gt,prefix=None,retCoefVars=True)
        (uk_1*x + uk_2*y + uk_0 > 0, [uk_0, uk_1, uk_2])

        sage: Template.mk([1, a, b, x, y],None,prefix=None)
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0

        sage: Template.mk([1, a, b, x, y],0,prefix='hi')
        a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0

        sage: var('x1')
        x1
        sage: Template.mk([1, a, b, x1, y],0,prefix='x')
        Traceback (most recent call last):
        ...
        AssertionError: name conflict
        """

        if not prefix: prefix = "uk_"
        coefVars = [sage.all.var(prefix + str(i)) for i in range(len(terms))]

        assert not set(terms).intersection(set(coefVars)), 'name conflict'

        template = sum(map(sage.all.prod, zip(coefVars, terms)))

        if rhsVal is not None:  #note, not None because rhsVal can be 0
            template = op(template, rhsVal)

        template = cls(template)
        if retCoefVars:
            return template, coefVars
        else:
            return template
