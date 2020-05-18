from time import time
import os.path
import itertools
from collections import OrderedDict
import collections
import os
import subprocess as sp
import shutil
from math import factorial
import sage.all
import random
import operator

import vu_common as CM
import sageutil

logger = CM.VLog('dig2')
logger.level = 0

class Miscs(object):
    @staticmethod
    def elimDenom(p):
        """
        Eliminate (Integer) denominators in expression operands.
        Will not eliminate if denominators is a var (e.g.,  (3*x)/(y+2)).

        Examples:

        sage: var('x y z')
        (x, y, z)

        sage: elim_denom(3/4*x^2 + 7/5*y^3)
        28*y^3 + 15*x^2

        sage: elim_denom(-3/2*x^2 - 1/24*z^2 >= (y + 1/7))
        -252*x^2 - 7*z^2 >= 168*y + 24

        sage: elim_denom(-3/(y+2)*x^2 - 1/24*z^2 >= (y + 1/7))
        -1/24*z^2 - 3*x^2/(y + 2) >= y + 1/7

        sage: elim_denom(x + y == 0)
        x + y == 0

        """
        try:
            f = lambda g : [sage.all.Integer(o.denominator()) for o in g.operands()]
            denoms = f(p.lhs()) + f(p.rhs()) if p.is_relational() else f(p)
            return p * sage.all.lcm(denoms)
        except TypeError:
            return p
    
    @staticmethod
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

    @staticmethod
    def strOfExp(p):
        """
        -p^3 => -(p*p*p)
        n*p^4 => n*(p*p*p*p)
        ab^3 => (ab*ab*ab)
        x*y*z^3 => x*y*(z*z*z)
        """

        def getPow(p):
            try:
                oprs = p.operands()
            except Exception:
                return []

            if p.operator() == sage.all.operator.pow:
                x,y = oprs
                pow_s = '*'.join([str(x)
                                  if x.is_symbol() else "({})".format(x)] * int(y))
                return [(str(p), '({})'.format(pow_s))]

            else:
                return [xy for o in oprs for xy in getPow(o)]

        s = str(p)
        if '^' not in s:
            return s
        rs = getPow(p)
        for (x,y) in rs: s = s.replace(x,y)
        return s
    
    @staticmethod
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
    def stripTo(s, to_s):
        return s[s.find(to_s) + 1:].strip() #e.g., ...:x  -> x

    @staticmethod
    def mkTerIdxss(ns, deg):
        assert ns >= 0, ns
        assert deg >= 1, deg
        
        ss = [None] + range(ns)
        combs = itertools.combinations_with_replacement(ss, deg)
        combs = [[idx for idx in idxs if idx is not None] for idxs in combs]
        combs = [tuple(idxs) for idxs in combs if idxs]
        return combs


    @staticmethod
    def getDeg(ns, nts, max_deg=7):
        """
        Generates a degree wrt to a (maximum) number of terms (nss)
        """
        assert ns >= 1, ns
        assert nts >= ns, (nts, ns)
        assert max_deg >= 1, max_deg

        for d in range(1, max_deg+1):
            if d == max_deg:
                return d

            #look ahead
            nterms = Miscs.mybinomial(ns + d+1, d+1) 
            if nterms > nts:
                return d

    @staticmethod
    def mybinomial(x, y):
        try:
            binom = factorial(x) // factorial(y) // factorial(x - y)
        except ValueError:
            binom = 0
    

    @staticmethod
    def getRInps(nInps, maxV):
        def _get(ranges):
            """
            getInps(3,[(0,20), (20,120), (120,150)])
            """
            inps = itertools.product(*itertools.repeat(range(len(ranges)),
                                                       nInps))
            return [tuple(random.randrange(ranges[p][0], ranges[p][1])
                          for p in inp) for inp in inps]
    
        assert maxV >= 0
        p15 = int(maxV*.10)
        p75 = int(maxV*.90)
        a1 = (0, p15)
        a3 = (p75, maxV)
        ranges = [a1,a3]
        return _get(ranges)
            
########## KLEE ##########
class KLEE(object):

    cexStr = "counterexample"
    haltStr = "halting execution, dumping remaining states"
    failedStr = "failed."
    
    def __init__(self, filename, tmpdir):
        assert os.path.isfile(filename)
        assert os.path.isdir(tmpdir)
        
        self.filename = CM.getpath(filename)
        import tempfile
        self.tmpdir = tmpdir
        logger.detail("running KLEE on {}, tmpdir {}"
                      .format(self.filename, self.tmpdir))

    def compile(self):
        #compile file with llvm
        
        includePath = "~/Src/Devel/KLEE/klee/include"
        clangOpts =  "-emit-llvm -c"
        obj = os.path.basename(self.filename) + os.extsep + 'o'
        obj = os.path.join(self.tmpdir, obj)

        cmd = ("clang -I {} {} {} -o {}"
               .format(includePath, clangOpts, self.filename, obj))
        logger.detail("$ {}".format(cmd))

        rs,rsErr = CM.vcmd(cmd)
        assert not rs, rs
        assert "clang" not in rsErr and "error" not in rsErr, rsErr
        if rsErr: logger.detail(rsErr)
        return obj

    def run(self, obj):
        #run klee and monitor its output
        kleeOutdir = "{}-klee-out".format(obj)
        if os.path.exists(kleeOutdir): shutil.rmtree(kleeOutdir)

        #"-optimize "  causes problems with prod4br
        timeout = 5
        kleeOpts = ("--allow-external-sym-calls "                    
                    "--max-time={}. "
                    "-output-dir={} "
                    .format(timeout,kleeOutdir))

        cmd = "klee {} {}".format(kleeOpts, obj).strip()
        logger.detail("$ {}".format(cmd))
        
        proc = sp.Popen(cmd,shell=True,stdout=sp.PIPE, stderr=sp.STDOUT)
        rs, rsErr = proc.communicate()
        assert not rsErr, rsErr
        return rs
    

    @classmethod
    def parseLog(cls, rs):
        """
        parse Klee's run log
        """
        if not rs: return []

        ignoresDone = ['KLEE: done: total instructions',
                        'KLEE: done: completed paths',
                        'KLEE: done: generated tests']

        ignoresRun = [ 
            'KLEE: WARNING: undefined reference to function: printf',
            'KLEE: WARNING ONCE: calling external: printf',
            'KLEE: ERROR: ASSERTION FAIL: 0',
            'KLEE: ERROR: (location information missing) ASSERTION FAIL: 0'
            ]

        ignoresMiscs = ['KLEE: NOTE: now ignoring this error at this location',
                         'GOAL: ']        

        lines = [line for line in rs.split('\n') if line]
        
        dinps = {}
        isSucc = True
        for line in lines:
            if all(x not in line for x in
                   ignoresDone + ignoresMiscs + ignoresRun):
                logger.detail("rs: {}".format(line))

            #input refuting ...: v1, v2
            if cls.cexStr in line:
                loc, inv, inp = cls.parseCex(line)
                loc = int(loc)
                if loc not in dinps: dinps[loc] = {}
                if inv not in dinps[loc]: dinps[loc][inv] = set()
                dinps[loc][inv].add(inp)
                
            elif any(s in line for s in [cls.haltStr, cls.failedStr]):
                isSucc = False

        return dinps, isSucc
    

    def getDInps(self):
        obj = self.compile()
        log = self.run(obj)
        dinps, isSucc = self.parseLog(log)
        return dinps, isSucc

    @classmethod
    def parseCex(cls, s):
        """
        sage: KLEE.parseCex("counterexample @ l8 @ 0 : 512 65")
        ('l8', '0', ('512', '65'))

        sage: KLEE.parseCex("counterexample @ l0 @ 0 + 1 > 0: 512 65")
        ('l0', '0 + 1 > 0', ('512', '65'))

        sage: KLEE.parseCex("counterexample @ l0 @ 0 + 1 > 0")
        ('l0', '0 + 1 > 0', None)
        """
        assert cls.cexStr in s, s

        if ":" in s:
            p1,p2 = s.split(":")
            inp = tuple(p2.strip().split())
        else:
            p1 = s
            inp = None
        _,loc,inv = map(lambda x: x.strip(), p1.strip().split("@"))
        
        assert loc, loc
        assert inv, inv
        if ':' in s: assert inp
        else: assert inp is None

        return loc, inv, inp
        

    #Make statements
    @classmethod
    def mkHeaders(cls):
        return ["#include <klee/klee.h>"]
    
    @classmethod
    def mkSymbolic(cls, varname, vartyp):
        """
        vartype varname;
        klee_make_symbolic(&vartype, sizeof(var1), "varname");
        """
        vdeclStr = "{} {};".format(vartyp, varname)
        ksymStr = ('klee_make_symbolic(&{}, sizeof({}), "{}");'
                   .format(varname, varname, varname))
        return vdeclStr + "\n" + ksymStr
    

    @classmethod
    def mkAssumeInps(cls, inps, inpdecls):
        """
        klee_assume(! ( (x==0 && y==1) || (x==2 && y==3) || ..))

        klee_assume(x!=0 || y!=1);
        klee_assume(x!=2 || y!=3);
        """
        ss = inpdecls.keys()
        mkOrExpr = lambda inp: "({})".format(
            " || ".join("{} != {}".format(vname, vval)
                        for vname, vval in zip(ss, inp)))
        mkAssumeOr = lambda inp: cls.mkAssume(mkOrExpr(inp))
        return map(mkAssumeOr, inps)

    @classmethod
    def mkAssumeRanges(cls, varname, minV, maxV):
        assert minV <= maxV, (minV, maxV)
        if minV == maxV:
            stmts = [cls.mkAssume("{} == {}".format(minV, varname))]
        else:
            stmt_gt = cls.mkAssume("{} <= {}".format(minV, varname))
            stmt_lt = cls.mkAssume("{} <= {}".format(varname, maxV))
            stmts = [stmt_gt, stmt_lt]
        return stmts
    
    @classmethod
    def mkAssume(cls, s): return  "klee_assume({});".format(s)
        

    @classmethod
    def mkAssertInvs(cls, invs, loc, (p1,p2)):
        """
        sage: print '\n'.join(KLEE.mkAssertInvs(["z>=0", "k==1"], "l2", (None, None)))
        if (!(z>=0)){printf("counterexample @ l2 @ z>=0\n");
        klee_assert(0);
        }
        if (!(k==1)){printf("counterexample @ l2 @ k==1\n");
        klee_assert(0);
        }

        sage: print '\n'.join(KLEE.mkAssertInvs(["z>=0", "k==1"], "l2", ("%d, %g","x, y")))
        if (!(z>=0)){printf("counterexample @ l2 @ z>=0: %d, %g\n", x, y);
        klee_assert(0);
        }
        if (!(k==1)){printf("counterexample @ l2 @ k==1: %d, %g\n", x, y);
        klee_assert(0);
        }
        """

        if p1 and p2:
            s = 'printf("{} @ {} @ {}: {}\\n", {});\n'
            _mkPrintf = lambda inv: s.format(cls.cexStr, loc, inv, p1, p2)
        else:
            s = 'printf("{} @ {} @ {}\\n");\n'
            _mkPrintf = lambda inv: s.format(cls.cexStr, loc, inv)

        _mkKleeAssert = lambda inv: ("if (!({})){{".format(inv) +
                                     _mkPrintf(inv) + 
                                     "klee_assert(0);\n}")
        stmts = []
        for inv in invs:
            assertStmt = _mkKleeAssert(inv)
            stmts.append(assertStmt)
        return stmts
    
    
########## SRC ##########
class Src(object):
    def __init__(self, filename):
        assert os.path.isfile(filename), filename
        self.filename = filename
        
    def parse(self):
        return self._parse(self.filename)

    def instrPrintfs(self, invdecls):
        assert isinstance(invdecls, dict) and invdecls, invdecls
        return self.instr(self.filename, ".printf.c", invdecls, self.mkPrintfs)

    def instrAsserts(self, props, inps, inpdecls, inps_d, startFun="mainQ"):
        assert isinstance(props, dict), props
        assert isinstance(inps, set), inps
        assert isinstance(inpdecls, dict), inpdecls

        assert (inps_d is None or
                (isinstance(inps_d, OrderedDict) and inps_d)), inps_d
        
        parts = self.mkPrintfArgs(inps_d) if inps_d else (None, None)
            
        _mk = lambda invs, loc: KLEE.mkAssertInvs(invs, loc, parts)
        stmts = self.mkProgStmts(self.filename, props, _mk)
        #comment startFun(..argv[]) and add symbolic input
        stmts_ = []
        for stmt in stmts:
            if startFun in stmt and "argv" in stmt:
                # stmt = "//" + stmt
                # stmts_.append(stmt)
                for varname, (vartyp, (minV, maxV)) in inps_d.iteritems():
                    stmt = KLEE.mkSymbolic(varname, vartyp)
                    stmts_.append(stmt)
                    if minV is not None and maxV is not None:
                        stmts__ = KLEE.mkAssumeRanges(varname, minV, maxV)
                        stmts_.extend(stmts__)

                #klee_assume(x!=0 || y!=1); klee_assume(x!=2 || y!=3);
                if inps:
                    stmts__ = KLEE.mkAssumeInps(inps, inpdecls)
                    stmts_.extend(stmts__)
                
                #call mainQ(inp0, ..);
                stmt = "{}({});".format(
                    startFun, ",".join(map(str, inps_d.iterkeys())))
                stmts_.append(stmt)
            else:
                stmts_.append(stmt)

        stmts = stmts_
            
        #add header
        stmts = ["#include <klee/klee.h>"] + stmts
        
        fname = self.filename + ".klee_assert.c"
        CM.vwrite(fname, '\n'.join(stmts))
        CM.vcmd("astyle -Y {}".format(fname))
        return fname
    


    ##### class methods #####
    @classmethod
    def _parse(cls, filename, startfun="mainQ", traceindicator="//%%%traces:"):
        """
        Return 
        inpdecls = {'x':'int', 'y':'double', ..}
        invdecls = {'lineno' : {'x':'int'; 'y':'double'}}
        """
        def mkVarsDict(s):
            #%%%indicator double x , double y .. ->  {x: int, y: double}
            #where x and y are SAGE's symbolic variables
            contents = (x.split() for x in s.split(','))
            try:
                return OrderedDict((k.strip(), t.strip()) for t,k in contents)
            except ValueError:
                return None

        inpdecls, invdecls = OrderedDict(), OrderedDict()
        for i,l in enumerate(CM.iread(filename)):            
            i = i + 1
            l = l.strip()
            if not l: continue

            if startfun in l and l.endswith(' {'):  #void startfun(int x, double y) {
                l = l.split('(')[1].split(')')[0]  #int x, double y
                inpdecls = mkVarsDict(l)

            elif l.startswith(traceindicator):
                invdecls[i] = mkVarsDict(Miscs.stripTo(l, ':'))

                
        assert invdecls
        assert (inpdecls is None or
                (isinstance(inpdecls, OrderedDict) and inpdecls)), inpdecls

        return inpdecls, invdecls
        


    @classmethod
    def mkPrintfArgs(cls, vars_d):
        """
        Return 2 strings representing 2 args to a printf stmt
        sage: vars_d = OrderedDict([('x','int'),('y','double')])
        sage: Src.mkPrintfArgs(vars_d)
        ('%d %g', 'x, y')
        """
        assert isinstance(vars_d, OrderedDict) and vars_d, vars_d
        p1 = []
        for k in vars_d:
            typ = vars_d[k]
            if isinstance(vars_d[k], tuple): #(typ, (minV, maxV))
                typ = vars_d[k][0]
                
            if typ == "int":
                a = "%d"
            else:
                a = "%g"
            p1.append(a)
        p1 = ' '.join(p1)
        p2 = ', '.join(map(str, vars_d.iterkeys()))
        return p1, p2
    
    @classmethod
    def mkPrintfs(cls, vars_d, lineno):
        """
        sage: vars_d = OrderedDict([('x','int'),('y','double')])
        sage: Src.mkPrintfs(vars_d, 1)
        ['printf("l12: %d %g\\n", x, y);']
        """
        assert lineno >= 1, lineno
        p1, p2 = cls.mkPrintfArgs(vars_d)
        stmt = 'printf("l{}: {}\\n", {});'.format(lineno, p1, p2)
        return [stmt]

    @classmethod
    def mkAsserts(cls, invs, linePrefix):
        stmts = []
        stmts.append("/* {}: DIG generated {} invs */"
                     .format(linePrefix, len(invs)))

        for inv in invs:
            assertStmt = "assert({}); /*DIG generated*/".format(inv)
            stmts.append(assertStmt)
        return stmts

    @classmethod
    def mkProgStmts(cls, filename, locs_d, mk_f):
        stmts = []
        for i, l in enumerate(CM.iread(filename)):
            i = i + 1
            l = l.strip()
            if not l: continue
            stmts.append(l)
            
            lineno = i
            if lineno in locs_d and locs_d[lineno]:
                stmts_ = mk_f(locs_d[lineno], lineno)
                stmts.extend(stmts_)
                
        return stmts
    
    @classmethod
    def instr(cls, filename, filePostfix, locs_d, mkStmts):
        stmts = cls.mkProgStmts(filename, locs_d, mkStmts)
        fname = filename + filePostfix
        CM.vwrite(fname, '\n'.join(stmts))
        _ = CM.vcmd("astyle -Y {}".format(fname))
        return fname

class EqtSolver(object):
    def __init__(self):
        pass

    @classmethod
    def refine(cls, sols):
        if len(sols) <= 1:
            return sols

        sols = Miscs.reducePoly(sols)
        #sols = [s for s in sols if getCoefsLen(s) <= 100]
        return sols    

    @classmethod
    def solve(cls, termIdxss, ss, uks, ttraces):
        """
        Return a *set* of equations
        """
        assert ttraces, ttraces
        assert isinstance(termIdxss, list) and termIdxss, termIdxss
        assert isinstance(uks, list) and len(uks) == len(termIdxss) + 1, uks
        assert isinstance(ss, list) and ss, ss

        #mk exprs
        exprs = [[uks[0]] + [u*v for u,v in zip(uks[1:], tcs)] for tcs in ttraces]
        exprs = [sum(l) == 0 for l in exprs]
        logger.debug("solve {} eqts for {} uks".format(len(exprs), len(uks)))

        sols = sage.all.solve(exprs, uks, solution_dict=True)
        if not sols: return []

        if len(sols) > 1: logger.warn('Two sols: {}'.format(sols))
        sols = [s for sol in sols for s in cls.analyze_sol(sol)]

        sols = [cls.mk_eqt(ss, termIdxss, uks, sol) for sol in sols]
        sols = [sol for sol in sols if sol is not None]
        sols = cls.refine(sols)

        sols = [Miscs.elimDenom(sol) for sol in sols] 
        sols = [Miscs.strOfExp(sol) for sol in sols] 
        return set(sols)

    @classmethod
    def mk_eqt(cls, ss, termIdxss, uks, uk_sols):
        """
        ss = [x, y, s, t]
        termIdxss = [(0,), (1,), (2,), (3,)]
        uks = [uk_0, uk_1, uk_2, uk_3, uk_4]
        uks = [(uk_1, -2), (uk_2, 0), (uk_3, 0), (uk_4, 1), (uk_0, -7)]
        uk_sols= [(uk_1, -2), (uk_2, 0), (uk_3, 0), (uk_4, 1), (uk_0, -7)]

        return a string
        """
        assert len(termIdxss) == len(uks) - 1
        assert len(uk_sols) == len(uks)

        terms = cls.mymul(ss, termIdxss) #(1*x, 1*y, 1*s, 1*t)
        uk_sols_d = dict(uk_sols)  #uk_1: -2, uk_2: 0
        denoms = [v.denominator() for v in uk_sols_d.itervalues()]
        lcm = sage.all.lcm(denoms)
        uk_vs = [int(lcm * uk_sols_d[uk]) for uk in uks]
        if not all(Traces.rangeMaxV >= v >= -Traces.rangeMaxV for v in uk_vs):
            return None

        terms = [t if uk_v == 1 else uk_v * t
                 for uk_v, t in zip(uk_vs[1:], terms) if uk_v != 0]
        if uk_vs[0] != 0: terms = [uk_vs[0]] + terms

        if terms:
            rs = sum(terms) == 0
            return rs
        else:
            return None
        

    @classmethod
    def analyze_sol(cls, sol):
        assert isinstance(sol, dict) and sol

        rs = sageutil.get_vars(sol.values())  #r1,r2,r3 ..
        imatrix = [[1 if j == i else 0 for j in range(len(rs))]
                   for i in range(len(rs))]
        rs = [dict(zip(rs, l)) for l in imatrix]
        #rs: [{r2: 0, r3: 0, r1: 1}, {r2: 1, r3: 0, r1: 0}, {r2: 0, r3: 1, r1: 0}]
        #d: {uk_2: r3, uk_3: r2, uk_4: r1, uk_0: -7*r1 - 7*r3, uk_1: -2*r1 - r2 - 2*r3}
        rs = [[(uk, rs.subs(rd)) for uk,rs in sol.iteritems()] for rd in rs]
        return rs

    @classmethod
    def mymul(cls, ls, idxss):
        rs = [ls[idxs[0]] if len(idxs) == 1 else
              reduce(operator.mul, [ls[i] for i in idxs], 1)
              for idxs in idxss]
        return tuple(rs)
    
    
    
class Traces(set):
    rangeMaxV = 1000
    traceMaxV = 1000000 #only use traces within (-traceMax, traceMax)
    def __init__(self):
        super(Traces, self).__init__(set())

    #cache this
    def instantiateAndFilter(self, termIdxss):
        if not self: return set()
        _inst = lambda tc: tuple(reduce(operator.mul, [tc[i] for i in idxs], 1)
                                 for idxs in termIdxss)
        
        traces = map(_inst, self)
        traces = set(tc for tc in traces
                     if all(self.traceMaxV >= t >= -self.traceMaxV for t in tc))
        return traces

    @staticmethod
    def parse(tracefile):
        """
        parse trace for file
        """
        assert isinstance(tracefile, str), tracefile        

        dtraces = {}
        for l in CM.iread_strip(tracefile):
            if not l: continue
            
            #l22: 8460 16 0 1 16 8460
            parts = l.split(':')
            assert len(parts) == 2
            lineno = int(parts[0].strip()[1:])  #l22

            tracevals = parts[1].strip().split()
            tracevals = map(Miscs.ratOfStr, tracevals)

            if lineno not in dtraces:
                dtraces[lineno] = Traces()
            dtraces[lineno].add(tuple(tracevals))

        return dtraces

    @staticmethod
    def merge(traces, newTraces):
        assert isinstance(traces, dict), traces
        assert isinstance(newTraces, dict), newTraces

        for loc in newTraces:
            assert newTraces[loc]

            if loc not in traces:
                traces[loc] = Traces()

            for trace in newTraces[loc]:
                traces[loc].add(trace)
        
            
class DIG2(object):
    def __init__(self, filename):

        import tempfile
        self.tmpdir = tempfile.mkdtemp(dir="/var/tmp", prefix="DIG2_")
        self.filename = filename
        basename = os.path.basename(self.filename)
        src = os.path.join(self.tmpdir, basename)
        _, rs_err = CM.vcmd("astyle -Y < {} > {}".format(self.filename, src))
        assert not rs_err, rs_err
        logger.debug("src: {}".format(src))

        self.src = Src(src)
        self.inpdecls, self.invdecls = self.src.parse()
        
    def start(self, seed, maxdeg, maxterm):
        #set seed
        import random
        random.seed(seed)
        sage.all.set_random_seed(seed)
        logger.debug('set seed to: {} (test {})'
                     .format(seed, sage.all.randint(0, 100)))

        maxvars = max(self.invdecls.itervalues(), key=lambda d: len(d))
        #set terms
        if maxdeg and maxterm:
            deg = maxdeg
        elif maxdeg:
            deg = maxdeg
        elif maxterm:
            deg = Miscs.getDeg(len(maxvars), maxterm)
        else:
            deg = Miscs.getDeg(len(maxvars), 200)

        self.deg = deg

        #other miscs setups
        self.tcsFile = "{}.tcs".format(self.src.filename)
        self.printfSrc = self.src.instrPrintfs(self.invdecls)
        self.exeFile = "{}.exe".format(self.printfSrc)
        ## -lm for math.h to work
        cmd = "gcc -lm {} -o {}".format(self.printfSrc, self.exeFile)
        CM.vcmd(cmd)
        
        gTraces = dict()  #global set of traces
        gInps = set() #global set of inps
        
        for loc in self.invdecls:
            invs = self.infer(loc, self.deg, gTraces, gInps)

    def infer(self, loc, deg, gTraces, gInps):
        assert isinstance(gTraces, dict), gTraces
        assert isinstance(gInps, set), gInps
        
        logger.debug("loc '{}': infer deg {} invs over {} vars: {}".format(
            loc, deg, len(self.invdecls[loc]),
            ', '.join(self.invdecls[loc])))
            
        #get terms
        ss = [sage.all.var(k) for k in self.invdecls[loc]]
        termIdxss = Miscs.mkTerIdxss(len(ss), deg)

        nuks = len(termIdxss) + 1
        nTracesFactor = 1.2        
        nTracesNeeded = int(nuks * nTracesFactor)

        ttraces = self.getInitTraces(loc, nTracesNeeded,
                                     termIdxss, gTraces, gInps)
        if not ttraces:
            logger.warn('unable to get enough traces')
            return []

        uks = [sage.all.var('uk{}'.format(i))
               for i in range(len(termIdxss) + 1)]

        eqts = set()  #results
        cache = set() #cache  {p:T|F|None}
        
        newTraces = True
        while newTraces:
            newTraces = False
            logger.debug("infer using {} traces".format(len(ttraces)))
            neweqts = EqtSolver.solve(termIdxss, ss, uks, ttraces)
            if neweqts:
                logger.debug('{} candidates:\n{}'.format(
                    len(neweqts), '\n'.join(map(str, neweqts))))

            unchecks = [eqt for eqt in neweqts if eqt not in cache]
            if unchecks:
                for prop in unchecks: cache.add(prop)
                
                logger.debug("check {} unchecked ({} candidates)"
                             .format(len(unchecks), len(neweqts)))

                propStats, traces = self.check({loc: unchecks}, gInps, doSafe=False)
                if loc in traces: #new traces (i.e., counterexample found)
                    assert traces[loc]
                    Traces.merge(gTraces, traces[loc])
                    
                    newTraces = True  #reloop
                    ttraces = gtraces[loc].instantiateAndFilter(termIdxss)


                assert loc in propStats                    
                for prop in unchecks:
                    if prop not in propStats[loc] or propStats[loc][prop] != False:
                        eqts.add(prop)
                    
            logger.debug("got {} eqts".format(len(eqts)))
            if eqts: logger.debug('\n'.join(map(str, eqts)))
            

        return cache
    
    def getInitTraces(self, loc, nTracesNeeded, termIdxss, gTraces, gInps):

        assert isinstance(gTraces, dict), gTraces
        assert isinstance(gInps, set), gInps
        
        if loc not in gTraces:
            gTraces[loc] = Traces()

        ttraces = gTraces[loc].instantiateAndFilter(termIdxss)
        while nTracesNeeded > len(ttraces):
            logger.debug("need more traces (have {}, need >= {})"
                         .format(len(ttraces), nTracesNeeded))
                                 
            inps = Miscs.getRInps(len(self.inpdecls), Traces.rangeMaxV)
            inps = [inp for inp in inps if inp not in gInps]
            for inp in inps: gInps.add(inp)

            newTraces = self.texec(inps)
            Traces.merge(gTraces, newTraces)
            
            assert (loc not in newTraces or newTraces[loc])
            if loc not in newTraces:
                _, newTraces_ = self.check({loc: [0]}, gInps, doSafe=True)
                Traces.merge(gTraces, newTraces_)

                if loc not in newTraces_:
                    logger.warn("rinps cannot reach loc '{}'".format(loc))
                    return None

            ttraces = gTraces[loc].instantiateAndFilter(termIdxss)


        return ttraces
            
    def texec(self, inps):
        """
        Run the program on inpts and get traces, e.g., {1: {(t1), (t2)}}
        """
        assert inps, inps
        if os.path.isfile(self.tcsFile): os.remove(self.tcsFile)
        
        for inp in inps:
            inp_ = ' '.join(map(str, inp))
            cmd = "{} {} >> {}".format(self.exeFile, inp_, self.tcsFile)
            logger.detail(cmd)
            CM.vcmd(cmd)

        traces = Traces.parse(self.tcsFile)
        return traces
    
    def check(self, props, inps, doSafe):
        """
        Check given props and return counterexamples (traces)
        """
        #{loc1:invs1, .., loc2:invs2}
        assert isinstance(props, dict) and props, props  

        logger.detail("check {} props".format(
            sum(map(len, props.itervalues()))))
        propStats, newInps = self.getInpsRange(props, inps, doSafe)
        if newInps: #run and extract traces
            traces = self.texec(newInps)
        else:
            traces = {}
        return propStats, traces


        
    #Verifier functions
    def getInps(self, props, gInps, minV, maxV, doSafe):
        assert isinstance(props, dict), props
        assert isinstance(gInps, set), ginps
        assert minV < maxV, (minV, maxV)
        assert isinstance(doSafe, bool), doSafe

        def _add(klInps, newInps, gInps):
            for inp in klInps:
                assert inp and len(self.inpdecls) == len(inp)
                assert inp not in gInps, inp

                newInps.add(inp)
                gInps.add(inp)


        if self.inpdecls:
            inps_d = OrderedDict((vname, (vtyp, (minV, maxV)))
                                 for vname, vtyp in self.inpdecls.iteritems())
        else:
            inps_d = None

        propStats = dict()
        newInps = set()
        if doSafe:
            #prove individually
            for loc, invs in props.iteritems():
                for inv in invs:
                    tprops = dict()
                    if loc not in tprops: tprops[loc] = set()
                    tprops[loc].add(inv)
                    
                    klSrc = self.src.instrAsserts(
                        tprops, gInps, self.inpdecls, inps_d)
                    klDInps, isSucc = KLEE(klSrc, self.tmpdir).getDInps()

                    if loc not in propStats: propStats[loc]=dict()
                    assert inv not in propStats[loc]
                    try:
                        klInps = klDInps[loc][str(inv)]
                        _add(klInps, newInps, gInps)
                        propStats[loc][inv] = False #not inv, counterexample
                    except KeyError:
                        propStats[loc][inv] = True if isSucc else None

        else:
            #do all at once
            tprops = dict()
            for loc, invs in props.iteritems():
                for inv in invs:
                    if loc not in tprops: tprops[loc] = set()
                    tprops[loc].add(inv)

            klSrc = self.src.instrAsserts(tprops, gInps, self.inpdecls, inps_d)
            klDInps, _ = KLEE(klSrc, self.tmpdir).getDInps()

            #IMPORTANT: getDInps() returns an isSucc flag (false if timeout),
            #but it's not useful here (when having multiple klee_asserts)
            #because even if isSucc, it doesn't guarantee to generate cex
            #for a failed assertions (that means we can't claim if an assertion
            #without cex is proved).
            for loc, invs in props.iteritems():
                if loc not in propStats: propStats[loc]=dict()

                for inv in invs:
                    assert inv not in propStats[loc]
                    try:
                        klInps = klDInps[loc][str(inv)]
                        _add(klInps, newInps, gInps)
                        propStats[inv] = False
                    except KeyError:
                        pass

        return propStats, newInps
                    
    def getInpsRange(self, invs, inps, doSafe):
        minv, maxv = -Traces.rangeMaxV, Traces.rangeMaxV 
        return self.getInps(invs, inps, minv, maxv, doSafe)

    def getInpsNoRange(self, invs, inps):
        minv,maxv = -Traces.rangeMaxV * 10, Traces.rangeMaxV * 10
        return self.getInps(invs, inps, minv, maxv, doSafe=True)
                            
if __name__ == "__main__":
    import argparse
    aparser = argparse.ArgumentParser("DIG2 (Dynamic Invariant Generator)")
    aparser.add_argument("inp", help="inp")

    
    #0 Error #1 Warn #2 Info #3 Debug #4 Detail
    aparser.add_argument("--logger_level", "-logger_level",
                         help="set logger info",
                         type=int,
                         choices=range(5),
                         default = 2)

    aparser.add_argument("--seed", "-seed",
                         type=float,
                         help="use this seed")
    
    aparser.add_argument("--maxdeg", "-maxdeg",
                         type=int,
                         default=None,
                         help="find nonlinear invs up to degree")

    aparser.add_argument("--maxterm", "-maxterm",
                         type=int,
                         default=None,
                         help="autodegree")

    aparser.add_argument("--maxtimeRT", "-maxtimeRT",
                         type=int,
                         default=5,
                         help="max number of secs for reachability tool")


    args = aparser.parse_args()
    logger.level = args.logger_level

    if __debug__: logger.warn("DEBUG MODE ON. Can be slow !")
    seed = round(time(), 2) if args.seed is None else float(args.seed)

    
    #Run it
    st = time()
    dig2 = DIG2(args.inp)
    
    invs = dig2.start(seed=seed, maxdeg=args.maxdeg, maxterm=args.maxterm)
    logger.info("time {}s".format(time() - st))
    

