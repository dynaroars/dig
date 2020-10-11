import random
import itertools

import sage.all
from sage.all import cached_function

import vu_common as CM
import sageutil

import settings
logger = CM.VLog('miscs')
logger.level = settings.logger_level  
logger.printtime = settings.logger_printtime

class Miscs(object):
    @cached_function
    def ratOfStr(s):
        """
        Convert the input 's' to a rational number if possible.
        Otherwise returns None

        Examples:

        sage: assert ratOfStr('.3333333') == 3333333/10000000
        sage: assert ratOfStr('3/7') == 3/7
        sage: assert ratOfStr('1.') == 1
        sage: assert ratOfStr('1.2') == 6/5
        sage: assert ratOfStr('.333') == 333/1000
        sage: assert ratOfStr('-.333') == -333/1000
        sage: assert ratOfStr('-12.13') == -1213/100

        #Returns None because cannot convert this str
        sage: ratOfStr('333333333333333s')
        alg:Warn:cannot convert 333333333333333s to rational

        Note: this version seems to be the *fastest*
        among several ones I've tried
        %timeit ratOfStr('322')
        """
        try:
            return sage.all.QQ(s)
        except TypeError:
            pass

        try:
            return sage.all.QQ(sage.all.RR(s))
        except TypeError:
            logger.warn('cannot convert {} to rational'.format(s))
            return None

    @staticmethod
    def getTerms(ss, deg):
        """
        get a list of terms from the given list of vars and deg
        the number of terms is len(rs) == binomial(len(ss)+d, d)

        Note: itertools is faster than Sage's MultichooseNK(len(ss)+1,deg)

        sage: ts = getTerms(list(var('a b')), 3)
        sage: assert ts == [1, a, b, a^2, a*b, b^2, a^3, a^2*b, a*b^2, b^3]

        sage: ts = getTerms(list(var('a b c d e f')), 3)
        sage: ts
        [1, a, b, c, d, e, f,
        a^2, a*b, a*c, a*d, a*e, a*f,
        b^2, b*c, b*d, b*e, b*f, c^2, c*d, c*e, c*f,
        d^2, d*e, d*f, e^2, e*f, f^2, a^3, a^2*b, a^2*c, a^2*d, a^2*e,
        a^2*f, a*b^2, a*b*c, a*b*d, a*b*e, a*b*f, a*c^2, a*c*d, a*c*e,
        a*c*f, a*d^2, a*d*e, a*d*f, a*e^2, a*e*f, a*f^2,
        b^3, b^2*c, b^2*d, b^2*e, b^2*f, b*c^2, b*c*d, b*c*e, b*c*f, b*d^2,
        b*d*e, b*d*f, b*e^2, b*e*f, b*f^2, c^3, c^2*d, c^2*e, c^2*f, c*d^2,
        c*d*e, c*d*f, c*e^2, c*e*f, c*f^2, d^3, d^2*e, d^2*f, d*e^2, d*e*f,
        d*f^2, e^3, e^2*f, e*f^2, f^3]

        """
        assert deg >= 0, deg
        assert ss and all(s.is_symbol() for s in ss), ss
        ss_ = ([sage.all.SR(1)] if ss else (sage.all.SR(1),)) + ss
        combs = itertools.combinations_with_replacement(ss_, deg)
        terms = [sage.all.prod(c) for c in combs]
        return terms


    @staticmethod
    def getDeg(nvs, nts, max_deg=7):
        """
        Generates a degree wrt to a (maximum) number of terms (nss)
        """
        assert nvs >= 1, nvs
        assert nts >= nvs, (nts, nvs)
        assert max_deg >= 1, max_deg

        for d in range(1,max_deg+1):
            if d == max_deg:
                return d

            #look ahead
            nterms = sage.all.binomial(nvs + d+1, d+1) 
            if nterms > nts:
                return d

    @staticmethod
    def getAutoDeg(maxdeg, maxterm, nvars):
        if maxdeg and maxterm:
            deg = maxdeg
        elif maxdeg:
            deg = maxdeg
        else:
            if maxterm:
                deg = Miscs.getDeg(nvars, maxterm)
            else:
                deg = Miscs.getDeg(nvars, 200)
                logger.info("autodeg {}".format(deg))

        return deg


    @staticmethod
    def genInitInps(nInps, maxV, maxnInps=100):    
        #15,75=   0...15, 15..75, 75..100

        def gen(nInps, ranges):
            """
            genInps(3,[(0,20), (20,120), (120,150)])
            """
            inps = itertools.product(*itertools.repeat(range(len(ranges)),
                                                       nInps))
            return [[random.randrange(ranges[p][0], ranges[p][1])
                     for p in inp] for inp in inps]
        assert maxV >= 0
        p15 = int(maxV*.10)
        p75 = int(maxV*.90)
        a1 = (0, p15)
        a3 = (p75, maxV)
        ranges = [a1,a3]
        rinps = gen(nInps, ranges)
        if len(rinps) >= maxnInps:
            random.shuffle(rinps)
            rinps = rinps[:maxnInps]
        return rinps


    @staticmethod
    def getTermsFixedCoefs(ss, subsetSiz):
        """
        sage: var('x y z t s u')
        (x, y, z, t, s, u)

        sage: getTermsFixedCoefs([x,y^2], 2)
        [-y^2 - x, -x, y^2 - x, -y^2, y^2, -y^2 + x, x, y^2 + x]
        """
        if len(ss) < subsetSiz:
            subsetSiz = len(ss)
        rs = []
        for ssSubset in itertools.combinations(ss, subsetSiz):
            css = itertools.product(*([[0, -1, 1]] * len(ssSubset)))
            r = (sum(c*t for c,t in zip(ssSubset, cs))
                 for cs in css if not all(c == 0 for c in cs))
            rs.extend(r)

        return CM.vset(rs)

    @staticmethod
    def reduceEqts(ps):
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
        if len(ps) <= 1:
            return ps

        assert (p.operator() == sage.all.operator.eq for p in ps), ps
        try:
            Q = sage.all.PolynomialRing(sage.all.QQ, sageutil.get_vars(ps))
            I = Q*ps
            ps = I.radical().interreduced_basis()
            ps = [(sage.all.SR(p) == 0) for p in ps]
        except AttributeError:
            pass

        return ps

    @staticmethod
    def reduceSMT(ps):
        ps1 = []
        ps2 = []
        
        for p in ps:
            if (p.operator() == sage.all.operator.eq
                and len(Miscs.getCoefs(p)) > 10):
                ps2.append(p)
            else:
                ps1.append(p)
            
        if len(ps1) <= 1: return ps
        
        import smt_z3py
        #Remove "longer" property first (i.e. those with more variables)
        #ps = sorted(ps, reverse=True, key=lambda p: len(get_vars(p)))
        rs = list(ps1) #make a copy
        for p in ps1:
            if p in rs:
                #note, the use of set makes things in non order
                xclude_p = CM.vsetdiff(rs,[p])
                if smt_z3py.imply(xclude_p,p):
                    rs = xclude_p

        rs.extend(ps2)
        return rs    
    

    @staticmethod
    def elimDenom(p):
        """
        Eliminate (Integer) denominators in expression operands.
        Will not eliminate if denominators is a var (e.g.,  (3*x)/(y+2)).

        Examples:

        sage: var('x y z')
        (x, y, z)

        sage: elimDenom(3/4*x^2 + 7/5*y^3)
        28*y^3 + 15*x^2

        sage: elimDenom(-3/2*x^2 - 1/24*z^2 >= (y + 1/7))
        -252*x^2 - 7*z^2 >= 168*y + 24

        sage: elimDenom(-3/(y+2)*x^2 - 1/24*z^2 >= (y + 1/7))
        -1/24*z^2 - 3*x^2/(y + 2) >= y + 1/7

        sage: elimDenom(x + y == 0)
        x + y == 0

        """
        try:
            f = lambda g: [sage.all.Integer(o.denominator())
                           for o in g.operands()]
            denoms = f(p.lhs()) + f(p.rhs()) if p.is_relational() else f(p)
            return p * sage.all.lcm(denoms)
        except TypeError:
            return p    

    @staticmethod
    def getCoefs(p):
        """
        Return coefficients of an expression
        """
        Q = sage.all.PolynomialRing(sage.all.QQ, sageutil.get_vars(p))
        rs = Q(p.lhs()).coefficients()
        return rs

    @staticmethod
    def refine(sols):
        if not sols: return sols
        sols = Miscs.reduceEqts(sols)
        sols = [Miscs.elimDenom(s) for s in sols]
        #don't allow large coefs
        sols_ = []
        for s in sols:
            if all(abs(c) <= 20 or sage.all.mod(c,10) == 0 or sage.all.mod(c,5) == 0
                   for c in Miscs.getCoefs(s)):
                sols_.append(s)
            else:
                logger.detail("large coefs: ignore {}".format(s))
        sols = sols_
        return sols        

    @staticmethod
    def solveEqts(eqts, uks, template):
        logger.debug("solve {} uks using {} eqts".format(len(uks), len(eqts)))
        # print 'ss', type(uks), uks
        # print '\n'.join(map(str, eqts))
        
        rs = sage.all.solve(eqts, *uks, solution_dict=True)
        eqts = Miscs.instantiateTemplate(template, rs)
        eqts = Miscs.refine(eqts)
        return eqts


    @staticmethod
    def mkTemplate(terms, rhsVal,
                   op=sage.all.operator.eq,
                   prefix=None, retCoefVars=False):
        """
        get a template from terms.

        Examples:

        sage: var('a,b,x,y')
        (a, b, x, y)

        sage: GenEqts.mkTemplate([1, a, b, x, y],0,prefix=None)
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0

        sage: GenEqts.mkTemplate([1, x, y],0,\
        op=operator.gt,prefix=None,retCoefVars=True)
        (uk_1*x + uk_2*y + uk_0 > 0, [uk_0, uk_1, uk_2])

        sage: GenEqts.mkTemplate([1, a, b, x, y],None,prefix=None)
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0

        sage: GenEqts.mkTemplate([1, a, b, x, y],0,prefix='hi')
        a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0

        sage: var('x1')
        x1
        sage: GenEqts.mkTemplate([1, a, b, x1, y],0,prefix='x')
        Traceback (most recent call last):
        ...
        AssertionError: name conflict
        """

        if not prefix: prefix = "uk_"
        uks = [sage.all.var(prefix + str(i)) for i in range(len(terms))]

        assert not set(terms).intersection(set(uks)), 'name conflict'

        template = sum(map(sage.all.prod, zip(uks, terms)))

        if rhsVal is not None:  #note, not None because rhsVal can be 0
            template = op(template, rhsVal)

        return template, uks if retCoefVars else template

    @staticmethod
    def instantiateTemplate(template, sols):
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
        assert sageutil.is_sage_expr(template), template
        
        if not sols: return []
        if len(sols) > 1:
            logger.warn('instantiateTemplateWithSols: len(sols) = {}'
                        .format(len(sols)))
            logger.warn(str(sols))

        def f_eq(d):
            if isinstance(d, list):
                f_ = template
                for d_ in d:
                    f_ = f_.subs(d_)
                rhsVals = CM.vset([d_.rhs() for d_ in d])
                uk_vars = sageutil.get_vars(rhsVals)
            else:
                f_ = template(d)
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
    
    @staticmethod
    def runMP(taskname, tasks, wprocess, chunksiz, doMP):
        """
        Run wprocess on tasks in parallel
        """
        if doMP:
            from vu_common import get_workloads
            from multiprocessing import (Process, Queue, cpu_count)
            Q=Queue()
            workloads = get_workloads(tasks, 
                                      max_nprocesses=cpu_count(),
                                      chunksiz=chunksiz)

            logger.debug("workloads '{}' {}: {}"
                         .format(taskname, len(workloads), map(len,workloads)))

            workers = [Process(target=wprocess, args=(wl,Q))
                       for wl in workloads]
            for w in workers: w.start()
            wrs = []
            for _ in workers: wrs.extend(Q.get())
        else:
            wrs = wprocess(tasks, Q=None)
                            
        return wrs
