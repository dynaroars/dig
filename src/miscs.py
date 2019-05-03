import itertools
import operator
from collections import Iterable

import sage.all
from sage.all import cached_function

import z3
import vcommon as CM
import settings
mlog = CM.getLogger(__name__, settings.logger_level)


class Miscs(object):
    @staticmethod
    def msage_eval(s, d):
        assert all(isinstance(k, str) and Miscs.isExpr(v)
                   for k, v in d.iteritems()), d

        while True:
            try:
                return sage.all.sage_eval(s, d)
            except NameError as e:  # name 'yy' is not defined
                symb = str(e).split("'")[1]
                mlog.debug("create new symbol {}".format(symb))
                d[symb] = sage.all.var(symb)

    @staticmethod
    @cached_function
    def isReal(x): return isinstance(x, sage.rings.real_mpfr.RealLiteral)

    @staticmethod
    @cached_function
    def isInt(x): return isinstance(x, sage.rings.integer.Integer)

    @classmethod
    @cached_function
    def isNum(cls, x): return cls.isReal(x) or cls.isInt(x)

    @staticmethod
    @cached_function
    def isRel(f, rel=None):
        """
        sage: assert not Miscs.isRel(7.2)
        sage: assert not Miscs.isRel(x)
        sage: assert not Miscs.isRel(x+7)
        sage: assert Miscs.isRel(x==3,operator.eq)

        sage: assert Miscs.isRel(x<=3,operator.le)
        sage: assert not Miscs.isRel(x<=3,operator.lt)
        sage: assert not Miscs.isRel(x+3,operator.lt)

        sage: y = var('y')
        sage: assert Miscs.isRel(x+y<=3)
        """

        try:
            if not f.is_relational():
                return False

            if rel is None:
                return True
            else:
                return f.operator() == rel

        except AttributeError:
            return False

    @classmethod
    @cached_function
    def isEq(cls, f):
        return cls.isRel(f, operator.eq)

    @staticmethod
    @cached_function
    def isExpr(x):
        return isinstance(x, sage.symbolic.expression.Expression)

    @classmethod
    def getVars(cls, ps):
        """
        Returns a list of uniq variables from a list of properties

        Examples:

        sage: var('a b c x')
        (a, b, c, x)

        sage: assert [a, b, c, x] == Miscs.getVars([x^(a*b) + a**2+b+2==0, c**2-b==100, b**2 + c**2 + a**3>= 1])
        sage: assert Miscs.getVars(a**2+b+5*c+2==0) == [a, b, c]
        sage: assert Miscs.getVars(x+x^2) == [x]
        sage: assert Miscs.getVars([3]) == []
        sage: assert Miscs.getVars((3,'x + c',x+b)) == [b, x]
        """

        ps = ps if isinstance(ps, Iterable) else [ps]
        ps = [p for p in ps if cls.isExpr(p)]
        vs = [v for p in ps for v in p.variables()]
        return sorted(set(vs), key=str)

    @staticmethod
    @cached_function
    def ratOfStr(s):
        """
        Convert the input 's' to a rational number if possible.

        Examples:
        sage: assert Miscs.ratOfStr('.3333333') == 3333333/10000000
        sage: assert Miscs.ratOfStr('3/7') == 3/7
        sage: assert Miscs.ratOfStr('1.') == 1
        sage: assert Miscs.ratOfStr('1.2') == 6/5
        sage: assert Miscs.ratOfStr('.333') == 333/1000
        sage: assert Miscs.ratOfStr('-.333') == -333/1000
        sage: assert Miscs.ratOfStr('-12.13') == -1213/100

        #Returns None because cannot convert this str
        sage: Miscs.ratOfStr('333333333333333s')
        Traceback (most recent call last):
        ...
        TypeError: unable to convert '333333333333333s' to a real number


        Note: this version seems to be the *fastest*
        among several ones I've tried
        %timeit ratOfStr('322')
        """
        try:
            return sage.all.QQ(s)
        except TypeError:
            pass

        return sage.all.QQ(sage.all.RR(s))

    @classmethod
    def initTerms(cls, vs, deg, rate):
        assert vs, vs
        assert rate >= 0.1, rate
        assert deg >= 1, deg

        terms = cls.getTerms([sage.all.var(v) for v in vs], deg)
        template, uks = cls.mkTemplate(terms, 0, retCoefVars=True)
        nEqtsNeeded = int(rate * len(uks))
        return terms, template, uks, nEqtsNeeded

    @staticmethod
    def getTerms(ss, deg):
        """
        get a list of terms from the given list of vars and deg
        the number of terms is len(rs) == binomial(len(ss)+d, d)

        Note: itertools is faster than Sage's MultichooseNK(len(ss)+1,deg)

        sage: ts = Miscs.getTerms(list(var('a b')), 3)
        sage: assert ts == [1, a, b, a^2, a*b, b^2, a^3, a^2*b, a*b^2, b^3]

        sage: ts = Miscs.getTerms(list(var('a b c d e f')), 3)
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

    @classmethod
    def getDeg(cls, nvs, nts, max_deg=7):
        """
        Generates a degree wrt to a (maximum) number of terms (nss)
        sage: Miscs.getDeg(3, 4, 5)
        1
        sage: Miscs.getDeg(3, 1, 5)
        Traceback (most recent call last):
        ...
        AssertionError: (1, 3)
        """
        assert nvs >= 1, nvs
        assert nts >= nvs, (nts, nvs)
        assert max_deg >= 1, max_deg

        for d in range(1, max_deg+1):
            if d == max_deg:
                return d

            # look ahead
            nterms = sage.all.binomial(nvs + d+1, d+1)
            if nterms > nts:
                return d

    @classmethod
    def getAutoDeg(cls, maxdeg, nvars, maxterm):
        if maxdeg:
            deg = maxdeg
            mlog.debug("using deg {}".format(deg))
        else:
            deg = cls.getDeg(nvars, maxterm)
            mlog.debug("autodeg {}".format(deg))

        return deg

    @staticmethod
    def getTermsFixedCoefs(ss, subsetSiz):
        """
        sage: var('x y z t s u')
        (x, y, z, t, s, u)

        sage: Miscs.getTermsFixedCoefs([x,y^2], 2)
        [-y^2, y^2, -x, -y^2 - x, y^2 - x, x, -y^2 + x, y^2 + x]

        sage: assert len(Miscs.getTermsFixedCoefs([x,y,z], 2)) == 18
        sage: assert len(Miscs.getTermsFixedCoefs([x,y,z], 3)) == 26
        """
        if len(ss) < subsetSiz:
            subsetSiz = len(ss)
        rs = []
        for ssSubset in itertools.combinations(ss, subsetSiz):
            css = itertools.product(*([[0, -1, 1]] * len(ssSubset)))
            r = (sum(c*t for c, t in zip(ssSubset, cs))
                 for cs in css if not all(c == 0 for c in cs))
            rs.extend(r)

        return set(rs)

    @staticmethod
    def reduceEqts(ps):
        """
        Return the basis (e.g., a min subset of ps that implies ps) 
        of the set of eqts input ps using Groebner basis

        sage: var('a y b q k')
        (a, y, b, q, k)

        sage: rs =  Miscs.reduceEqts([a*y-b==0,q*y+k-x==0,a*x-a*k-b*q==0])
        sage: assert set(rs) == set([a*y - b == 0, q*y + k - x == 0])

        sage: rs =  Miscs.reduceEqts([x*y==6,y==2,x==3])
        sage: assert set(rs) == set([x - 3 == 0, y - 2 == 0])

        #Attribute error occurs when only 1 var, thus return as is
        sage: rs =  Miscs.reduceEqts([x*x==4,x==2])
        sage: assert set(rs) == set([x == 2, x^2 == 4])
        """
        if len(ps) <= 1:
            return ps

        assert (p.operator() == sage.all.operator.eq for p in ps), ps
        try:
            Q = sage.all.PolynomialRing(sage.all.QQ, Miscs.getVars(ps))
            I = Q*ps
            ps = I.radical().interreduced_basis()
            ps = [(sage.all.SR(p) == 0) for p in ps]
        except AttributeError:
            pass

        return ps

    @staticmethod
    def elimDenom(p):
        """
        Eliminate (Integer) denominators in expression operands.
        Will not eliminate if denominators is a var (e.g.,  (3*x)/(y+2)).

        Examples:

        sage: var('x y z')
        (x, y, z)

        sage: Miscs.elimDenom(3/4*x^2 + 7/5*y^3)
        28*y^3 + 15*x^2

        sage: Miscs.elimDenom(-3/2*x^2 - 1/24*z^2 >= (y + 1/7))
        -252*x^2 - 7*z^2 >= 168*y + 24

        sage: Miscs.elimDenom(-3/(y+2)*x^2 - 1/24*z^2 >= (y + 1/7))
        -1/24*z^2 - 3*x^2/(y + 2) >= y + 1/7

        sage: Miscs.elimDenom(x + y == 0)
        x + y == 0

        """
        try:
            def f(g): return [sage.all.Integer(o.denominator())
                              for o in g.operands()]
            denoms = f(p.lhs()) + f(p.rhs()) if p.is_relational() else f(p)
            return p * sage.all.lcm(denoms)
        except TypeError:
            return p

    @classmethod
    def getCoefs(cls, p):
        """
        Return coefficients of an expression
        sage: var('y')
        y
        sage: Miscs.getCoefs(3*x+5*y^2 == 9)
        [5, 3]
        """
        Q = sage.all.PolynomialRing(sage.all.QQ, cls.getVars(p))
        rs = Q(p.lhs()).coefficients()
        return rs

    @staticmethod
    def isRepeatingRational(x):
        "check if x is a repating rational"
        assert isinstance(x, sage.rings.rational.Rational) \
            and not x.is_integer(), x

        x1 = x.n(digits=50).str(skip_zeroes=True)
        x2 = x.n(digits=100).str(skip_zeroes=True)
        return x1 != x2

    @classmethod
    def refine(cls, sols, ignoreLargeCoefs=True):
        if not sols:
            return sols
        sols = cls.reduceEqts(sols)
        sols = [cls.elimDenom(s) for s in sols]

        def okCoefs(s): return all(
            abs(c) <= settings.MAX_LARGE_COEFS or
            sage.all.mod(c, 10) == 0 or
            sage.all.mod(c, 5) == 0
            for c in cls.getCoefs(s))

        if ignoreLargeCoefs:  # don't allow large coefs
            sols_ = []
            for s in sols:
                if okCoefs(s):
                    sols_.append(s)
                else:
                    mlog.debug("large coefs: ignore {}".format(s))
            sols = sols_
        return sols

    @classmethod
    def solveEqts(cls, eqts, uks, template):
        assert isinstance(eqts, list) and eqts, eqts
        assert isinstance(uks, list)and uks, uks
        assert len(eqts) >= len(uks), (len(eqts), len(uks))

        mlog.debug("solve {} uks using {} eqts".format(len(uks), len(eqts)))
        rs = sage.all.solve(eqts, *uks, solution_dict=True)
        assert isinstance(rs, list), rs
        assert all(isinstance(s, dict) for s in rs), rs

        # filter sols with all uks = 0, e.g., {uk_0: 0, uk_1: 0, uk_2: 0}
        rs = [d for d in rs if not all(x == 0 for x in d.itervalues())]

        reqts = cls.instantiateTemplate(template, rs)
        reqts = cls.refine(reqts)
        # print '\n'.join(map(str, eqts))
        # print uks
        # print reqts
        # CM.pause()

        return reqts

    @classmethod
    def mkTemplate(cls, terms, rhsVal,
                   op=sage.all.operator.eq,
                   prefix=None, retCoefVars=False):
        """
        get a template from terms.

        Examples:

        sage: var('a,b,x,y')
        (a, b, x, y)

        sage: Miscs.mkTemplate([1, a, b, x, y],0,prefix=None)
        (a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0,
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0)

        sage: Miscs.mkTemplate([1, x, y],0,\
        op=operator.gt,prefix=None,retCoefVars=True)
        (uk_1*x + uk_2*y + uk_0 > 0, [uk_0, uk_1, uk_2])

        sage: Miscs.mkTemplate([1, a, b, x, y],None,prefix=None)
        (a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0,
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0)

        sage: Miscs.mkTemplate([1, a, b, x, y],0,prefix='hi')
        (a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0,
        a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0)

        sage: var('x1')
        x1
        sage: Miscs.mkTemplate([1, a, b, x1, y],0,prefix='x')
        Traceback (most recent call last):
        ...
        AssertionError: name conflict
        """

        if not prefix:
            prefix = "uk_"
        uks = [sage.all.var(prefix + str(i)) for i in range(len(terms))]

        assert not set(terms).intersection(set(uks)), 'name conflict'

        template = sum(map(sage.all.prod, zip(uks, terms)))

        if rhsVal is not None:  # note, not None because rhsVal can be 0
            template = op(template, rhsVal)

        return template, uks if retCoefVars else template

    @classmethod
    def instantiateTemplate(cls, template, sols):
        """
        Instantiate a template with solved coefficient values

        sage: var('uk_0,uk_1,uk_2,uk_3,uk_4,r14,r15,a,b,y')
        (uk_0, uk_1, uk_2, uk_3, uk_4, r14, r15, a, b, y)

        #when sols are in dict form
        sage: sols = [{uk_0: -2*r14 + 7/3*r15, uk_1: -1/3*r15, uk_4: r14, uk_2: r15, uk_3: -2*r14}]
        sage: Miscs.instantiateTemplate(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0, sols)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]

        #when sols are not in dict form
        sage: sols = [[uk_0== -2*r14 + 7/3*r15, uk_1== -1/3*r15, uk_4== r14, uk_2== r15, uk_3== -2*r14]]
        sage: Miscs.instantiateTemplate(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0, sols)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]

        sage: Miscs.instantiateTemplate(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0, [])
        []
        """
        assert cls.isExpr(template), template

        if not sols:
            return []
        if len(sols) > 1:
            mlog.warn('instantiateTemplateWithSols: len(sols) = {}'
                      .format(len(sols)))
            mlog.warn(str(sols))

        def fEq(d):
            if isinstance(d, list):
                f_ = template
                for d_ in d:
                    f_ = f_.subs(d_)
                rhsVals = CM.vset([d_.rhs() for d_ in d])
                uk_vars = cls.getVars(rhsVals)
            else:
                f_ = template(d)
                uk_vars = cls.getVars(d.values())  # e.g., r15,r16 ...

            if not uk_vars:
                return f_

            iM = sage.all.identity_matrix(len(uk_vars))  # standard basis
            rs = [dict(zip(uk_vars, l)) for l in iM.rows()]
            rs = [f_(r) for r in rs]
            return rs

        sols = [y for x in sols for y in fEq(x)]

        # remove trivial (tautology) str(x) <=> str(x)
        sols = [s for s in sols
                if not (s.is_relational() and str(s.lhs()) == str(s.rhs()))]

        return sols

    @classmethod
    def getDisj(cls, p, v):
        assert cls.isExpr(p), p
        assert cls.isExpr(v) and v.is_symbol(), v
        sols = sage.all.solve(p, v)
        return sols

    @classmethod
    def strOfDisj(cls, ps):
        assert len(ps) >= 2, ps
        return "{}".format(" | ".join(map(str, ps)))

    @classmethod
    def getDisjs(cls, ps):
        assert ps, ps
        vs = cls.getVars(ps)
        pss = [(p, cls.getDisj(p, v)) for p in ps for v in vs
               if p.operator() == sage.all.operator.eq]
        pss = ["{} => ({})".format(p, cls.strOfDisj(ps))
               for p, ps in pss if len(ps) >= 2]
        return pss

    @classmethod
    def getWorkloads(cls, tasks, maxProcessces, chunksiz):
        """
        >>> wls = Miscs.getWorkloads(range(12),7,1); wls
        [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9], [10, 11]]


        >>> wls = Miscs.getWorkloads(range(12),5,2); wls
        [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9, 10, 11]]

        >>> wls = Miscs.getWorkloads(range(20),7,2); wls
        [[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11], [12, 13, 14], [15, 16, 17], [18, 19]]


        >>> wls = Miscs.getWorkloads(range(20),20,2); wls
        [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9], [10, 11], [12, 13], [14, 15], [16, 17], [18, 19]]

        """
        assert len(tasks) >= 1, tasks
        assert maxProcessces >= 1, maxProcessces
        assert chunksiz >= 1, chunksiz

        # determine # of processes
        ntasks = len(tasks)
        nprocesses = int(round(ntasks/float(chunksiz)))
        if nprocesses > maxProcessces:
            nprocesses = maxProcessces

        # determine workloads
        cs = int(round(ntasks/float(nprocesses)))
        wloads = []
        for i in range(nprocesses):
            s = i*cs
            e = s+cs if i < nprocesses-1 else ntasks
            wl = tasks[s:e]
            if wl:  # could be 0, e.g., getWorkloads(range(12),7,1)
                wloads.append(wl)

        return wloads

    @classmethod
    def runMP(cls, taskname, tasks, wprocess, chunksiz, doMP):
        """
        Run wprocess on tasks in parallel
        """
        if doMP:
            from multiprocessing import (Process, Queue, cpu_count)
            Q = Queue()
            wloads = cls.getWorkloads(
                tasks, maxProcessces=cpu_count(), chunksiz=chunksiz)

            mlog.debug("workloads '{}' {}: {}"
                       .format(taskname, len(wloads), map(len, wloads)))

            workers = [Process(target=wprocess, args=(wl, Q)) for wl in wloads]

            for w in workers:
                w.start()
            wrs = []
            for _ in workers:
                wrs.extend(Q.get())
        else:
            wrs = wprocess(tasks, Q=None)

        return wrs


class Z3(object):
    @classmethod
    def isVar(cls, v):
        return z3.is_const(v) and v.decl().kind() == z3.Z3_OP_UNINTERPRETED

    @classmethod
    def _getVars(cls, f, rs):
        """
        Helper method to obtain variables from a formula f recursively.
        Results are stored in the list rs.
        """
        assert z3.is_expr(f) or z3.is_const(f), f
        if z3.is_const(f):
            if cls.isVar(f):
                rs.add(f)
        else:
            for c in f.children():
                cls._getVars(c, rs)

    @classmethod
    @cached_function
    def getVars(cls, f):
        """
        sage: x,y,z = z3.Ints("x y z")
        sage: f = z3.And(x + y == z , y + z == z)
        sage: assert(Z3.getVars(f) == {z, y, x})
        """
        assert z3.is_expr(f), f

        rs = set()
        cls._getVars(f, rs)
        return frozenset(rs)

    @classmethod
    def createSolver(cls):
        solver = z3.Solver()
        timeout = settings.SOLVER_TIMEOUT * 1000
        solver.set(timeout=timeout)  # secs
        return solver

    @classmethod
    def extract(self, models):
        assert models is None or models is False \
            or (isinstance(models, list) and
                all(isinstance(m, z3.ModelRef) for m in models)
                and models), models

        cexs = set()
        isSucc = models is not None
        if isSucc and models:  # disproved
            cexs = [{str(s): sage.all.sage_eval(str(model[s])) for s in model}
                    for model in models]
        return cexs, isSucc

    @classmethod
    def getModels(cls, f, k):
        """
        Returns the first k models satisfiying f.
        If f is not satisfiable, returns False.
        If f cannot be solved, returns None
        If f is satisfiable, returns the first k models
        Note that if f is a tautology, i.e., True, then the result is []
        """
        assert z3.is_expr(f), f
        assert k >= 1, k

        solver = cls.createSolver()
        solver.add(f)

        models = []
        i = 0
        while solver.check() == z3.sat and i < k:
            i = i + 1
            m = solver.model()
            if not m:  # if m == []
                break
            models.append(m)
            # create new constraint to block the current model
            block = z3.Not(z3.And([v() == m[v] for v in m]))
            solver.add(block)

        stat = solver.check()

        if stat == z3.unknown:
            rs = None
        elif stat == z3.unsat and i == 0:
            rs = False
        else:
            rs = models

        return rs, stat

    @classmethod
    def imply(cls, fs, g, useReals):
        """
        sage: var('x y')
        (x, y)
        sage: assert Z3.imply([x-6==0],x*x-36==0,useReals=False)
        sage: assert Z3.imply([x-6==0,x+6==0],x*x-36==0,useReals=False)
        sage: assert not Z3.imply([x*x-36==0],x-6==0,useReals=False)
        sage: assert not Z3.imply([x-6==0],x-36==0,useReals=False)
        sage: assert Z3.imply([x-7>=0], x>=6,useReals=False)
        sage: assert not Z3.imply([x-7>=0], x>=8,useReals=False)
        sage: assert not Z3.imply([x-6>=0], x-7>=0,useReals=False)
        sage: assert not Z3.imply([x-7>=0,y+5>=0],x+y-3>=0,useReals=False)
        sage: assert Z3.imply([x-7>=0,y+5>=0],x+y-2>=0,useReals=False)
        sage: assert Z3.imply([x-2*y>=0,y-1>=0],x-2>=0,useReals=False)
        sage: assert not Z3.imply([],x-2>=0,useReals=False)
        sage: assert Z3.imply([x-7>=0,y+5>=0],x+y-2>=0,useReals=False)
        sage: assert Z3.imply([x^2-9>=0,x>=0],x-3>=0,useReals=False)
        sage: assert not Z3.imply([1/2*x**2 - 3/28*x + 1 >= 0],1/20*x**2 - 9/20*x + 1 >= 0,useReals=True)
        sage: assert Z3.imply([1/20*x**2 - 9/20*x + 1 >= 0],1/2*x**2 - 3/28*x + 1 >= 0,useReals=True)
        sage: assert Z3.imply([x-6==0],x*x-36==0,useReals=False)
        sage: assert not Z3.imply([x+7>=0,y+5>=0],x*y+36>=0,useReals=False)
        sage: assert not Z3.imply([x+7>=0,y+5>=0],x*y+35>=0,useReals=False)
        sage: assert not Z3.imply([x+7>=0,y+5>=0],x*y-35>=0,useReals=False)
        sage: assert not Z3.imply([x+7>=0],x-8>=0,useReals=False)
        sage: assert Z3.imply([x+7>=0],x+8>=0,useReals=False)
        sage: assert Z3.imply([x+7>=0],x+8.9>=0,useReals=True)
        sage: assert Z3.imply([x>=7,y>=5],x*y>=35,useReals=False)
        sage: assert not Z3.imply([x>=-7,y>=-5],x*y>=35,useReals=False)
        """

        assert all(Miscs.isExpr(f) for f in fs), fs
        assert Miscs.isExpr(g), g
        assert isinstance(useReals, bool), useReals

        if not fs:
            return False  # conservative approach
        fs = [cls.toZ3(f, useReals, useMod=False) for f in fs]
        g = cls.toZ3(g, useReals, useMod=False)

        claim = z3.Implies(z3.And(fs), g)
        models, _ = cls.getModels(z3.Not(claim), k=1)

        return models is False

    @classmethod
    def reduceSMT(cls, ps, useReals):
        eqts, eqtsLargeCoefs, ieqs = [], [], []
        for p in ps:
            if p.operator() == sage.all.operator.eq:
                if len(Miscs.getCoefs(p)) > 10:
                    eqtsLargeCoefs.append(p)
                else:
                    eqts.append(p)
            else:
                ieqs.append(p)

        if len(eqts + ieqs) <= 1:
            return ps

        ps = sorted(ieqs) + eqts
        rs = list(ps)

        for p in ps:
            if p not in rs:
                continue
            xclude = [p_ for p_ in rs if p_ != p]
            if cls.imply(xclude, p, useReals):
                rs = xclude

        rs.extend(eqtsLargeCoefs)
        return rs

    @classmethod
    @cached_function
    def toZ3(cls, p, useReals, useMod):
        """
        Convert a Sage expression to a Z3 expression

        Initially implements with a dictionary containing variables
        e.g. {x:Real('x')} but the code is longer and more complicated.
        This implemention does not require a dictionary pass in.

        sage: Z3.toZ3(x*x*x, False, useMod=False)
        x*x*x
        """

        assert isinstance(useReals, bool), useReals
        assert isinstance(useMod, bool), useMod

        def retval(p):
            if p.is_symbol():
                _f = z3.Real if useReals else z3.Int
            else:
                _f = z3.RealVal if useReals else z3.IntVal

            try:
                return _f(str(p))
            except Exception:
                assert False, "cannot parse {}".format(p)

        oprs = p.operands()
        if oprs:
            op = p.operator()

            # z3 has problem w/ t^c , so use t*t*t..
            if op == operator.pow:
                assert len(oprs) == 2, oprs
                t, c = oprs
                t = cls.toZ3(t, useReals, useMod)
                if useMod:
                    c = cls.toZ3(c, useReals, useMod)
                    res = reduce(operator.mod, [t, c])
                else:
                    vs = [t] * c
                    res = reduce(operator.mul, vs)
            else:
                oprs = [cls.toZ3(o, useReals, useMod) for o in oprs]
                res = reduce(op, oprs)

        else:
            res = retval(p)

        assert z3.is_expr(res), res
        if useMod:
            mlog.debug("mod hack: {} => {}".format(p, res))
        return res
