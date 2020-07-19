import abc
from collections import OrderedDict, MutableSet, MutableMapping
import collections
import itertools
import os.path
import sage.all

import vu_common as CM
import sageutil
import settings
logger = CM.VLog('alg')
logger.level = settings.logger_level  

from klee import KLEE 

isIterator = lambda it: isinstance(it, collections.Iterator)
stripTo = lambda s, to_s: s[s.find(to_s) + 1:].strip() #e.g., ...:x  -> x

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
        css = itertools.product(*([[-1, 0, 1]] * len(ssSubset)))
        r = (sum(c*t for c,t in zip(ssSubset, cs))
             for cs in css if not all(c == 0 for c in cs))
        rs.extend(r)

    return CM.vset(rs)

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
    
### Classes ###
class MySet(MutableSet):
    __metaclass__ = abc.ABCMeta
    def __init__(self): self.__set__ = set()
    def __len__(self): return len(self.__set__)
    def __iter__(self): return iter(self.__set__)    
    def discard(self, inp): raise NotImplementedError("discard")
    def __str__(self): return ", ".join(map(str, sorted(self)))

    @abc.abstractmethod
    def __contains__(self, inp): return inp in self.__set__
    @abc.abstractmethod
    def add(self, inp):
        notIn = False
        if inp not in self.__set__:
            notIn = True
            self.__set__.add(inp)
        return notIn

class MyDict(MutableMapping):
    __metaclass__ = abc.ABCMeta
    def __init__(self): self.__dict__ = {}
    def __len__(self): return len(self.__dict__)
    def __getitem__(self, key): return self.__dict__[key]
    def __iter__(self): return iter(self.__dict__)    
    def __setitem__(self, key, val): raise NotImplementedError("setitem")
    def __delitem__(self, key): raise NotImplementedError("delitem")

    def addToSet(self, key, val, cls):
        assert issubclass(cls, MySet), cls
        if key not in self.__dict__:
            self.__dict__[key] = cls()
        return self.__dict__[key].add(val)
    
    @property
    def siz(self): return sum(map(len, self.itervalues()))
    
#Exceptions
class NotEnoughTraces(Exception): pass

#Inputs
class Inp(CM.HDict):
    def __str__(self):
        return " ".join("{}={}".format(x,y) for x,y in self.iteritems())
    
class Inps(MySet):
    def __contains__(self, inp):
        assert isinstance(inp, Inp), inp
        return super(Inps, self).__contains__(inp)

    def add(self, inp):
        assert isinstance(inp, Inp), inp
        return super(Inps, self).add(inp)

    @classmethod
    def mk(cls, inpdecls, minV, maxV):
        assert (inpdecls is None or
                (isinstance(inpdecls, OrderedDict) and inpdecls)), inpdecls
        assert minV <= maxV, (minV, maxV)

        if not inpdecls: return Inps()
        possVals = sorted(set([minV, maxV, (minV+maxV)/2, 0]))
        inps = Inps()
        combs = itertools.combinations_with_replacement(possVals, len(inpdecls))
        for comb in combs:
            inp = Inp(zip(inpdecls, comb))
            inps.add(inp)

        return inps

        
#Traces
class Trace(CM.HDict):
    """
    Hashable traces
    """

    def __str__(self):
        return " ".join("{}={}".format(x,y) for x,y in self.iteritems())
        
    @property
    def _dict(self):
        """
        Some Sage substitution requires dict format
        """
        try:
            return self._d
        except AttributeError:
            self._d = dict(self)
            return self._d
        
    @classmethod
    def parse(cls, tracefile, invdecls):
        """
        parse trace for new traces
        """
        assert isinstance(tracefile, str), tracefile        
        assert isinstance(invdecls, dict) and invdecls, invdecls

        new_dtraces = DTraces()
        for l in CM.iread_strip(tracefile):
            #l22: 8460 16 0 1 16 8460
            parts = l.split(':')
            assert len(parts) == 2
            lineno = parts[0].strip()  #l22
            assert lineno in invdecls, (lineno, invdecls)

            tracevals = parts[1].strip().split()
            tracevals = map(ratOfStr, tracevals)
            ss = invdecls[lineno].keys()
            assert len(ss) == len(tracevals)

            trace = cls(zip(ss, tracevals))
            new_dtraces.addToSet(lineno, trace)
        return new_dtraces

class Traces(MySet):
    def __contains__(self, trace):
        assert isinstance(trace, Trace), trace
        return super(Traces, self).__contains__(trace)

    def add(self, trace):
        assert isinstance(trace, Trace), trace
        return super(Traces, self).add(trace)

    def __str__(self, printStat=False):
        return ", ".join(map(str, sorted(self)))
    
class DTraces(MyDict):
    def addToSet(self, loc, trace):
        assert isinstance(loc, str), loc
        assert isinstance(trace, Trace), trace
        return super(DTraces, self).addToSet(loc, trace, Traces)

    def update(self, dtraces):
        """
        Update dtraces to contain conents of self and return diffs
        """
        new_dtraces = DTraces()
        for loc in self:
            for trace in self[loc]:
                notIn = dtraces.addToSet(loc, trace)
                if notIn:
                    new_dtraces.addToSet(loc, trace)
                else:
                    logger.detail("{} exist".format(trace))
        return new_dtraces

    def __str__(self):
        return "\n".join("{}: {}".format(loc, len(traces))
                         for loc, traces in self.iteritems())

class Inv(object):
    PROVED = "p"
    DISPROVED = "d"
    UNKNOWN = "u"
    
    def __init__(self, inv):
        assert inv == 0 or inv == 1 or inv.is_relational(), inv
        self.inv = inv
        
        self.resetStat()
        self.resetTemplateID()
        
    def __str__(self, printStat=False):
        s = str(self.inv)
        if printStat: s = "{} {}".format(s, self.stat)
        return s
    
    def __hash__(self): return hash(self.inv)
    def __repr__(self): return repr(self.inv)
    def __eq__(self, o): return self.inv.__eq__(o.inv)
    def __ne__(self, o): return not self.inv.__eq__(o.inv)

    def getStat(self): return self._stat    
    def setStat(self, stat):
        assert stat in {self.PROVED, self.DISPROVED, self.UNKNOWN}, stat
        self._stat = stat
    stat = property(getStat, setStat)

    def resetStat(self): self._stat = None
        
    @property
    def isProved(self): return self.stat == self.PROVED
    @property
    def isDisproved(self): return self.stat == self.DISPROVED
    @property
    def isUnknown(self): return self.stat == self.UNKNOWN

    @classmethod
    def mkFalse(cls): return cls(0)

    def getTemplateID(self): return self._tid
    def setTemplateID(self, tid):
        self._tid = tid
    templateID = property(getTemplateID, setTemplateID)
    def resetTemplateID(self): self._tid = None

class Invs(MySet):
    def __contains__(self, inv):
        assert isinstance(inv, Inv), inv
        return super(Invs, self).__contains__(inv)

    def add(self, inv):
        assert isinstance(inv, Inv), inv
        return super(Invs, self).add(inv)

    def __str__(self, printStat=False):
        return ", ".join(map(lambda inv: inv.__str__(printStat), sorted(self)))

class DInvs(MyDict):
    def __str__(self, printStat=False):
        return "\n".join("{}: {}".format(loc, invs.__str__(printStat))
                         for loc, invs in self.iteritems())

    def addToSet(self, loc, inv):
        assert isinstance(loc, str), loc
        assert isinstance(inv, Inv), inv
        return super(DInvs, self).addToSet(loc, inv, Invs)

    def __setitem__(self, loc, invs):
        assert isinstance(loc, str), loc
        assert isinstance(invs, Invs), invs
        
        self.__dict__[loc] = invs

    def resetStats(self):
        for loc in self:
            for inv in self[loc]:
                inv.resetStat()
        

    def merge(self, dinvs):
        assert isinstance(dinvs, DInvs), dinvs
        merged_dinvs = DInvs()
        for dinvs_ in [self, dinvs]:
            for loc in dinvs_:
                for inv in dinvs_[loc]:
                    if not inv.isDisproved: 
                        merged_dinvs.addToSet(loc, inv)
                        
        return merged_dinvs

    def removeDisproved(self):
        dinvs = DInvs()
        for loc in self:
            for inv in self[loc]:
                assert inv.stat is not None, inv
                if not inv.isDisproved:
                    dinvs.addToSet(loc, inv)

        return dinvs
    
    def update(self, dinvs):
        assert isinstance(dinvs, DInvs), dinvs
        new_dinvs = DInvs()
        for loc in self:
            if loc not in dinvs:
                dinvs[loc] = self[loc]
                new_dinvs[loc] = self[loc]
            elif dinvs[loc] != self[loc]:
                new_invs = Invs()
                for inv in self[loc]:
                    if inv not in dinvs[loc]:
                        new_invs.add(inv)
                    else:
                        invs_l = list(dinvs[loc])
                        old_inv = invs_l[invs_l.index(inv)]
                        if inv.stat != old_inv.stat:
                            inv.stat = old_inv.stat
                dinvs[loc] = self[loc]
                new_dinvs[loc] = new_invs

        return new_dinvs

    @classmethod
    def mkFalses(cls, locs):
        dinvs = DInvs()
        for loc in locs: dinvs.addToSet(loc, Inv.mkFalse())
        return dinvs
        
class Src(object):
    
    def __init__(self, filename):
        assert os.path.isfile(filename), filename
        self.filename = filename
        
    def parse(self): return self._parse(self.filename)
    
    def instrPrintfs(self, invdecls):
        assert isinstance(invdecls, dict) and invdecls, invdecls
        return self.instr(self.filename, ".printf.c", invdecls, self.mkPrintfs)
    
    def instrKleeAsserts(self, dinvs, inps, inps_d, startFun="mainQ"):
        assert isinstance(dinvs, DInvs), dinvs
        assert (inps_d is None or
                (isinstance(inps_d, OrderedDict) and inps_d)), inps_d
        
        assert isinstance(inps, Inps), inps

        if inps_d:
            parts = self.mkPrintfArgs(inps_d)
        else:
            parts = (None, None)
        _mk = lambda invs, loc: KLEE.mkAssertInvs(invs, loc, parts)
        stmts = self.mkProgStmts(self.filename, dinvs, _mk)
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
                    stmts__ = KLEE.mkAssumeInps(inps)
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

    @classmethod
    def _parse(cls, filename, startFun="mainQ", traceIndicator="//%%%traces:"):
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
                return OrderedDict(
                    (sage.all.var(k.strip()), t.strip()) for t,k in contents )
            except ValueError:
                return None

        inpdecls = OrderedDict()
        invdecls = OrderedDict()
        for i,l in enumerate(CM.iread(filename)):            
            i = i + 1
            l = l.strip()
            if not l: continue

            if startFun in l and l.endswith(' {'):  #void startFun(int x, double y) {
                l = l.split('(')[1].split(')')[0]  #int x, double y
                inpdecls = mkVarsDict(l)

            elif l.startswith(traceIndicator):
                vars_d = mkVarsDict(stripTo(l, ':'))
                linePrefix = 'l' + str(i)
                invdecls[linePrefix] = vars_d
                
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
    def mkPrintfs(cls, vars_d, linePrefix):
        """
        sage: vars_d = OrderedDict([('x','int'),('y','double')])
        sage: Src.mkPrintfs(vars_d, "l12")
        ['printf("l12: %d %g\\n", x, y);']
        """
        assert (isinstance(linePrefix, str) and
                linePrefix.startswith("l")), linePrefix
        p1, p2 = cls.mkPrintfArgs(vars_d)
        stmt = 'printf("{}: {}\\n", {});'.format(linePrefix, p1, p2)
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
            
            linePrefix = 'l' + str(i)
            if linePrefix in locs_d and locs_d[linePrefix]:
                stmts_ = mk_f(locs_d[linePrefix], linePrefix)
                stmts.extend(stmts_)
                
        return stmts
    
    @classmethod
    def instr(cls, filename, filePostfix, locs_d, mkStmts):
        stmts = cls.mkProgStmts(filename, locs_d, mkStmts)
        
        fname = filename + filePostfix
        CM.vwrite(fname, '\n'.join(stmts))
        CM.vcmd("astyle -Y {}".format(fname))
        return fname


class DIG2(object):
    def __init__(self, filename):
        assert os.path.isfile(filename), filename
        self.filename = filename

    def initialize(self, seed, tmpdir):
        #set seed
        import random        
        random.seed(seed)
        sage.all.set_random_seed(seed)
        logger.info('set seed to: {} (test {})'
                    .format(seed, sage.all.randint(0,100)))

        fname = os.path.basename(self.filename)
        src = os.path.join(tmpdir, fname)
        _, rs_err = CM.vcmd("astyle -Y < {} > {}".format(self.filename, src))
        assert not rs_err, rs_err
        
        self.src = Src(src)
        self.inpdecls, self.invdecls = self.src.parse()
        self.printfSrc = self.src.instrPrintfs(self.invdecls)
        self.exeFile = "{}.exe".format(self.printfSrc)
        #-lm for math.h to work
        cmd = "gcc -lm {} -o {}".format(self.printfSrc, self.exeFile) 
        CM.vcmd(cmd)
        
        #tracefile
        self.tcsFile =  "{}.tcs".format(self.printfSrc)

    def checkReachability(self, tmpdir):
        #check for reachability using inv False (0)
        dinvs = DInvs.mkFalses(self.invdecls)
        inps = Inps()        
        dtraces = self.checkInvs(dinvs, inps, tmpdir, doSafe=True)
        return dinvs, dtraces, inps
        
    def start(self, seed, deg, doEqts, doIeqs, ieqTyp, tmpdir):
        assert isinstance(seed, (int,float)), seed
        assert deg >= 1, deg
        assert isinstance(doEqts, bool), doEqts
        assert isinstance(doIeqs, bool), doIeqs
        assert os.path.isdir(tmpdir), tmpdir
        
        self.initialize(seed, tmpdir)

        logger.info("checking reachability")
        dinvs, dtraces, inps = self.checkReachability(tmpdir)
        
        if dtraces:
            logger.info("considering invs at {} locs: {}"
                        .format(len(dtraces),
                                ', '.join(map(str,dtraces))))
            def _infer(solverCls):
                infer_f = lambda deg, locs, dtraces, dinvs, doWeak: self.infer(
                    deg, locs, dtraces, dinvs, solverCls, doWeak)
                dinvs = self.approx(deg, dtraces, inps, infer_f, tmpdir)
                return dinvs

            if doIeqs:
                logger.info("inferring {} ieqs".format(ieqTyp))
                if ieqTyp.startswith("oct"):
                    solverCls = OctSolver
                else:
                    solverCls = RangeSolver
                dinvs_ = _infer(solverCls)
                dinvs = dinvs.merge(dinvs_)

            if doEqts:
                logger.info("inferring eqts")
                dinvs_ = _infer(EqtSolver)
                dinvs = dinvs.merge(dinvs_)

        
        logger.info("final checking {} candidate invs\n{}"
                    .format(dinvs.siz, dinvs.__str__(printStat=True)))

        #try to remove unknown ones using specific inputs
        #_ = self.getKleeInpsPreset(dinvs, inps, tmpdir)
        
        #final tests
        dinvs.resetStats()
        _ = self.getKleeInpsNoRange(dinvs, inps, tmpdir)
        dinvs = dinvs.removeDisproved()

        logger.info("got {} invs\n{} (test {})"
                    .format(dinvs.siz, dinvs.__str__(printStat=True),
                            sage.all.randint(0,100)))
                    
        return dinvs

    def getKleeInps(self, dinvs, inps, minV, maxV, tmpdir, doSafe):
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(inps, Inps), inps
        assert os.path.isdir(tmpdir), tmpdir
        assert isinstance(doSafe, bool), doSafe

        def addInps(klInps, new_inps, inps):
            for inp in klInps:
                if self.inpdecls:
                    assert inp and len(self.inpdecls) == len(inp)
                    inp = Inp(zip(self.inpdecls, inp))
                else:
                    inp = Inp() #empty inp
                assert inp not in inps, inp
                inps.add(inp)
                new_inps.add(inp)

        if self.inpdecls:
            inps_d = OrderedDict((vname, (vtyp, (minV, maxV)))
                                 for vname, vtyp in self.inpdecls.iteritems())
        else:
            inps_d = None
        
        new_inps = Inps()
        if doSafe:
            #prove individually
            for loc,invs in dinvs.iteritems():
                for inv in invs:
                    if inv.stat is not None: continue

                    dinvs_ = DInvs()
                    dinvs_.addToSet(loc, inv)
                    klSrc = self.src.instrKleeAsserts(dinvs_, inps, inps_d)
                    klDInps, isSucc = KLEE(klSrc, tmpdir).getDInps()
                    try:
                        klInps = klDInps[loc][str(inv)]
                        addInps(klInps, new_inps, inps)
                        inv.stat = Inv.DISPROVED
                    except KeyError:
                        if isSucc:
                            inv.stat = Inv.PROVED
                        else:
                            inv.stat = Inv.UNKNOWN

            for loc,invs in dinvs.iteritems():
                assert(inv.stat is not None for inv in invs)

        else:
            #do all at once
            dinvs_ = DInvs()
            for loc, invs in dinvs.iteritems():
                for inv in invs:
                    if inv.stat is None:
                        dinvs_.addToSet(loc, inv)

            klSrc = self.src.instrKleeAsserts(dinvs_, inps, inps_d)
            klDInps, _ = KLEE(klSrc, tmpdir).getDInps()

            #IMPORTANT: getDInps() returns an isSucc flag (false if timeout),
            #but it's not useful here (when having lots of a klee_asserts)
            #because even if isSucc, it doesn't guarantee to generate cex
            #for a failed assertions (that means we can't claim if an assertion
            #without cex is proved).
            for loc, invs in dinvs.iteritems():
                for inv in invs:
                    if inv.stat is not None: continue
                    try:
                        klInps = klDInps[loc][str(inv)]
                        addInps(klInps, new_inps, inps)
                        inv.stat = Inv.DISPROVED
                    except KeyError:
                        pass

        return new_inps
                    
    def getKleeInpsRange(self, dinvs, inps, tmpdir, doSafe):
        return self.getKleeInps(dinvs, inps, 
                                IeqSolver.minV, IeqSolver.maxV,
                                tmpdir, doSafe)

    def getKleeInpsNoRange(self, dinvs, inps, tmpdir):
        return self.getKleeInps(dinvs, inps, 
                                IeqSolver.minV*10, IeqSolver.maxV*10,
                                tmpdir, doSafe=True)

    def getKleeInpsPreset(dinvs, inps, tmpdir):
        return self.getKleeInps(dinvs, inps, 
                                IeqSolver.minV, IeqSolver.maxV,
                                tmpdir, doSafe=True)        
    
    def getTraces(self, inps):
        assert isinstance(inps, Inps) and inps, inps
        
        if os.path.isfile(self.tcsFile): os.remove(self.tcsFile)
        
        for inp in inps:
            inp_ = ' '.join(map(str,[v for _,v in inp.iteritems()]))
            cmd = "{} {} >> {}".format(self.exeFile, inp_, self.tcsFile)
            logger.detail(cmd)
            CM.vcmd(cmd)

        new_dtraces = Trace.parse(self.tcsFile, self.invdecls)
        return new_dtraces        
        
    def checkInvs(self, dinvs, inps, tmpdir, doSafe):
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(inps, Inps), inps
        assert os.path.isdir(tmpdir), tmpdir

        logger.detail("checking {} invs:\n{}".format(
            dinvs.siz, dinvs.__str__(printStat=True)))
        new_inps = self.getKleeInpsRange(dinvs, inps, tmpdir, doSafe)
        if not new_inps:
            return DTraces()
        else:
            new_dtraces = self.getTraces(new_inps)
            logger.debug("got {} traces from {} inps"
                         .format(new_dtraces.siz, len(new_inps)))
            return new_dtraces
        
    def approx(self, deg, dtraces, inps, infer_f, tmpdir):
        assert deg >= 1, deg
        assert isinstance(dtraces, DTraces) and dtraces, dtraces        
        assert isinstance(inps, Inps), inps        
        assert os.path.isdir(tmpdir), tmpdir

        dinvs = DInvs()
        locs = dtraces.keys()
        curIter = 0
        while True:
            if not locs:
                logger.debug("no new traces")
                break

            dinvs_, needMoreTraces = infer_f(
                deg, locs, dtraces, dinvs, curIter==0)
            new_dinvs = dinvs_.update(dinvs)

            curIter += 1
            logger.info(
                "iter {}, invs {}, inps {}, traces {}, rand {}".
                format(curIter, dinvs.siz, len(inps), dtraces.siz,
                       sage.all.randint(0,100)))

            locsMoreTraces = [loc for loc in needMoreTraces
                              if needMoreTraces[loc]]
            if locsMoreTraces:
                logger.debug("getting more traces for {} locs: {}"
                             .format(len(locsMoreTraces),
                                     ",".join(map(str, locsMoreTraces))))
                dinvsFalse = DInvs.mkFalses(locsMoreTraces)
                dtraces_ = self.checkInvs(dinvsFalse, inps, tmpdir,doSafe=False)
                new_dtraces = dtraces_.update(dtraces)
                locs = new_dtraces.keys()
                continue

            if new_dinvs:
                logger.debug("{} new invs:\n{}"
                             .format(new_dinvs.siz,
                                     new_dinvs.__str__(printStat=True)))
            else:
                logger.debug("no new invs")
                break

            dtraces_ = self.checkInvs(dinvs, inps, tmpdir, doSafe=False)
            new_dtraces = dtraces_.update(dtraces)
            loc = new_dtraces.keys()
            
        return dinvs
        
    def infer(self, deg, locs, dtraces, dinvs, solverCls, doWeak):
        assert deg >= 1, deg
        assert isinstance(locs, list) and locs, locs
        assert isinstance(dtraces, DTraces) and dtraces, dtraces
        assert isinstance(dinvs, DInvs), dinvs

        needMoreTraces = {loc:False for loc in locs}
        dinvs_ = DInvs()
        for loc in locs:
            assert dtraces[loc], loc
            terms = [sage.all.var(k) for k in self.invdecls[loc]]
            
            try:
                if issubclass(solverCls, EqtSolver): #eqts
                    terms = getTerms(terms, deg)
                    traces = (t._dict for t in dtraces[loc])
                    solver = solverCls(traces)
                    invs = solver.solve(terms)
                    
                else:  #ieqs
                    traces = (t._dict for t in dtraces[loc])
                    solver = solverCls(traces)
                    if doWeak:
                        invs = solver.solveWeak(terms)
                    else:
                        invs = solver.solve(terms)

                invs = solverCls.refine(invs)
                for inv in invs:
                    dinvs_.addToSet(loc, Inv(inv))
                    
            except NotEnoughTraces as ex:
                logger.detail("loc {}: {}".format(loc, ex))                
                needMoreTraces[loc] = True
                
        return dinvs_, needMoreTraces
        
#### Solvers for different forms of invariants ###
class Solver(object):
    __metaclass__ = abc.ABCMeta
    def __init__(self, traces):
        assert isIterator(traces) or traces, traces
        self.traces = traces

    @abc.abstractmethod
    def solve(self): return

class EqtSolver(Solver):

    RATE = 1.7
    
    def __init__(self, traces):
        super(EqtSolver, self).__init__(traces)

    def solve(self, terms): return self._solve(terms, self.traces)

    @classmethod
    def _solve(cls, terms, traces):
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
        nTraces = int(round(len(terms) * EqtSolver.RATE))
        eqts = list(template.instantiateTraces(traces, nTraces))
        if  len(eqts) < nTraces:
            raise NotEnoughTraces("need more traces ({} unknowns , {} eqts)"
                                  .format(len(terms), len(eqts)))
        
        try:
            logger.detail("solving {} unknowns using {} eqts"
                          .format(len(coefVars), len(eqts)))
            sols = sage.all.solve(eqts, coefVars, solution_dict=True)
            sols = template.instantiateSols(sols)
            return sols
        except Exception as ex:
            logger.warn(str(ex))
            return []

    @classmethod
    def refine(cls, sols):
        if len(sols) <= 1:
            return sols

        sols = reducePoly(sols)
        sols = [s for s in sols if getCoefsLen(s) <= 100]
        return sols

class IeqSolver(Solver):
    """
    sage: var('x y z')
    (x, y, z)
    sage: traces = tcs=[{x:2,y:-8,z:-7}, {x:0,y:-15,z:88}, {x:15,y:5,z:0}]
    sage: RangeSolver(traces).solve([x, y])
    [-x + 15 >= 0, x >= 0, -y + 5 >= 0, y + 15 >= 0]

    sage: OctSolver(traces).solve([x, y, z])
    [-x - y + 20 >= 0, -x + 15 >= 0, -x + y + 15 >= 0, -y + 5 >= 0,
    y + 15 >= 0, x - y - 10 >= 0, x >= 0, x + y + 15 >= 0,
    -x - z + 88 >= 0, -x + z + 15 >= 0,  -z + 88 >= 0, z + 7 >= 0,
    x - z + 88 >= 0,  x + z + 5 >= 0, -y - z + 73 >= 0, -y + z + 5 >= 0,
    y - z + 103 >= 0,  y + z + 15 >= 0]

    sage: assert len(IeqSolver(traces).solve([x, y, z], subsetSiz=None)) == 26
    """

    minV = -10000
    maxV =  10000

    def __init__(self, traces):
        super(IeqSolver, self).__init__(traces)
        
    def solve(self, terms, subsetSiz):
        return self._solve(terms, self.traces, subsetSiz)
    
    def solveWeak(self, terms, subsetSiz):
        return self._solveWeak(terms, subsetSiz)
    
    @classmethod
    def _solve(cls, terms, traces, subsetSiz):
        if isIterator(traces): traces = list(traces)
        terms = cls.getTermsFixedCoefs(terms, subsetSiz)
        rs = []
        for t in terms:
            minTraceV = min(t.subs(trace) for trace in traces)
            if minTraceV > cls.minV:
                term = t - minTraceV >= 0
                rs.append(term)
        return rs

    @classmethod
    def _solveWeak(cls, terms, subsetSiz):
        """
        Return very weak but likely true invs
        """
        terms = cls.getTermsFixedCoefs(terms, subsetSiz)
        return [t - (cls.minV+1) >= 0 for t in terms]
    
    @classmethod
    def refine(cls, sols): return sols

    @classmethod
    def getTermsFixedCoefs(cls, terms, subsetSiz):
        terms = [t for t in terms if t != 1]
        if not subsetSiz: subsetSiz = len(terms)
        terms = getTermsFixedCoefs(terms, subsetSiz)
        return terms

class RangeSolver(IeqSolver):
    def solve(self, terms):
        return super(RangeSolver,self).solve(terms, subsetSiz=1)
    
    def solveWeak(self, terms):
        return super(RangeSolver,self).solveWeak(terms, subsetSiz=1)
    
class OctSolver(IeqSolver):
    def solve(self, terms):
        return super(OctSolver,self).solve(terms, subsetSiz=2)
    def solveWeak(self, terms):
        return super(OctSolver,self).solveWeak(terms, subsetSiz=2)

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
