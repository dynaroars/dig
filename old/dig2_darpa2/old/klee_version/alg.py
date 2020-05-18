import abc
from collections import OrderedDict, MutableSet, MutableMapping
import collections
import itertools
import os.path
import sage.all

import vu_common as CM
from sageutil import is_sage_expr
import settings
logger = CM.VLog('alg')
logger.level = settings.logger_level  

import miscs
from klee import KLEE 
from solver import EqtSolver, RangeSolver, OctSolver, IeqSolver

### Classes ###
class MySet(MutableSet):
    __metaclass__ = abc.ABCMeta
    def __init__(self): self.__set__ = set()
    def __len__(self): return len(self.__set__)
    def __iter__(self): return iter(self.__set__)    
    def __str__(self): return ", ".join(map(str, sorted(self)))
    def discard(self, inp): raise NotImplementedError("discard")
    
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

        dtraces = DTraces()
        for l in CM.iread_strip(tracefile):
            #l22: 8460 16 0 1 16 8460
            parts = l.split(':')
            assert len(parts) == 2
            lineno = parts[0].strip()  #l22
            assert lineno in invdecls, (lineno, invdecls)

            tracevals = parts[1].strip().split()
            tracevals = map(miscs.ratOfStr, tracevals)
            ss = invdecls[lineno].keys()
            assert len(ss) == len(tracevals)

            trace = cls(zip(ss, tracevals))
            dtraces.addToSet(lineno, trace)
        return dtraces

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

        if not miscs.checkVals(trace.itervalues()):
            return
        
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
        
        if is_sage_expr(self.inv):
            inv = miscs.elim_denom(self.inv)
            s = miscs.strOfExp(inv)
        else:
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
        deltas = DInvs()
        for loc in self:
            if loc not in dinvs:
                dinvs[loc] = self[loc]
                deltas[loc] = self[loc]
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
                deltas[loc] = new_invs

        return deltas

    @classmethod
    def mkFalses(cls, locs):
        dinvs = DInvs()
        for loc in locs:
            dinvs.addToSet(loc, Inv.mkFalse())
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
                vars_d = mkVarsDict(miscs.stripTo(l, ':'))
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
    def __init__(self, filename, tmpdir):
        assert os.path.isfile(filename), filename
        assert os.path.isdir(tmpdir), tmpdir
        self.filename = filename
        self.tmpdir = tmpdir
        
    def initialize(self, seed):
        #set seed
        import random        
        random.seed(seed)
        sage.all.set_random_seed(seed)
        logger.info('set seed to: {} (test {})'
                    .format(seed, sage.all.randint(0,100)))

        fname = os.path.basename(self.filename)
        src = os.path.join(self.tmpdir, fname)
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

    def checkReach(self):

        #check for reachability using inv False (0)
        dinvs = DInvs.mkFalses(self.invdecls)        
        inps = Inps()

        #use some initial inps first
        rinps = miscs.genInitInps(len(self.inpdecls), IeqSolver.maxV)
        for inp in rinps: inps.add(Inp(zip(self.inpdecls, inp)))
        dtraces = self.getTraces(inps)
        #update invs and reachable locs
        unreach_locs = set()
        for loc in dinvs:
            if loc in dtraces:
                for inv in dinvs[loc]:
                    inv.stat = Inv.DISPROVED #reachable
            else:
                unreach_locs.add(loc)

        if unreach_locs: #use reach tool to generate traces
            unreach_dinvs = DInvs.mkFalses(unreach_locs)
            unreach_dtraces = self.checkInvs(unreach_dinvs, inps, doSafe=True)
            unreach_dtraces.update(dtraces)

        return dinvs, dtraces, inps
        
    def start(self, seed, deg, doEqts, doIeqs, ieqTyp):
        assert isinstance(seed, (int,float)), seed
        assert deg >= 1 or callable(deg), deg
        assert isinstance(doEqts, bool), doEqts
        assert isinstance(doIeqs, bool), doIeqs

        self.initialize(seed)

        logger.info("checking reachability")
        dinvs, dtraces, inps = self.checkReach()
        if dtraces:                                          
            def _infer(solverCls):
                infer_f = lambda deg, locs, dtraces, doWeak: self.infer(
                    deg, locs, dtraces, solverCls, doWeak)
                dinvs = self.approx(deg, dtraces, inps, infer_f)
                return dinvs

            locs_s = "{} locs: {}".format(
                len(dtraces), ', '.join(map(str,dtraces)))

            if doIeqs:
                logger.info("inferring {} ieqs at {}".format(ieqTyp, locs_s))
                if ieqTyp.startswith("oct"):
                    solverCls = OctSolver
                else:
                    solverCls = RangeSolver
                dinvs_ = _infer(solverCls)
                dinvs = dinvs.merge(dinvs_)

            if doEqts:
                logger.info("inferring eqts at {}".format(locs_s))
                dinvs_ = _infer(EqtSolver)
                dinvs = dinvs.merge(dinvs_)

        
        logger.info("final checking {} invs".format(dinvs.siz))
        logger.detail(dinvs.__str__(printStat=True))
        
        #try to remove unknown ones using specific inputs
        #_ = self.getKleeInpsPreset(dinvs, inps, tmpdir)

        #re-test against all traces
        # for loc in dinvs:
        #     for inv in dinvs[loc]:
        #         print loc, inv
        #         print [inv.inv.subs(t._dict) for t in dtraces[loc]]
                    
        #         if not all(bool(inv.inv.subs(t._dict)) for t in dtraces[loc]):
        #             print "DISPROVED"
        
        #final tests
        dinvs.resetStats()
        _ = self.getKleeInpsNoRange(dinvs, inps)
        dinvs = dinvs.removeDisproved()

        logger.info("got {} invs\n{} (test {})"
                    .format(dinvs.siz, dinvs.__str__(printStat=True),
                            sage.all.randint(0,100)))
                    
        return dinvs

    def getKleeInps(self, dinvs, inps, minV, maxV, doSafe):
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(inps, Inps), inps
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
                    klDInps, isSucc = KLEE(klSrc, self.tmpdir).getDInps()
                    try:
                        klInps = klDInps[loc][str(inv)]
                        addInps(klInps, new_inps, inps)
                        inv.stat = Inv.DISPROVED
                    except KeyError:
                        inv.stat = Inv.PROVED if isSucc else Inv.UNKNOWN

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
            klDInps, _ = KLEE(klSrc, self.tmpdir).getDInps()

            #IMPORTANT: getDInps() returns an isSucc flag (false if timeout),
            #but it's not useful here (when haveing multiple klee_asserts)
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
                    
    def getKleeInpsRange(self, dinvs, inps, doSafe):
        return self.getKleeInps(dinvs, inps, 
                                IeqSolver.minV, IeqSolver.maxV, doSafe)

    def getKleeInpsNoRange(self, dinvs, inps):
        return self.getKleeInps(dinvs, inps, 
                                IeqSolver.minV*10, IeqSolver.maxV*10,
                                doSafe=True)

    def getKleeInpsPreset(dinvs, inps):
        return self.getKleeInps(dinvs, inps, 
                                IeqSolver.minV, IeqSolver.maxV,
                                doSafe=True)        
    
    def getTraces(self, inps):
        assert isinstance(inps, Inps) and inps, inps
        
        if os.path.isfile(self.tcsFile): os.remove(self.tcsFile)
        
        for inp in inps:
            inp_ = ' '.join(map(str,[v for _,v in inp.iteritems()]))
            cmd = "{} {} >> {}".format(self.exeFile, inp_, self.tcsFile)
            logger.detail(cmd)
            CM.vcmd(cmd)

        # print self.tcsFile
        # CM.pause()
        new_dtraces = Trace.parse(self.tcsFile, self.invdecls)
        return new_dtraces        
        
    def checkInvs(self, dinvs, inps, doSafe):
        assert isinstance(dinvs, DInvs), dinvs
        assert isinstance(inps, Inps), inps

        logger.detail("checking {} invs:\n{}".format(
            dinvs.siz, dinvs.__str__(printStat=True)))
        new_inps = self.getKleeInpsRange(dinvs, inps, doSafe)
        
        if not new_inps:
            return DTraces()
        else:
            new_dtraces = self.getTraces(new_inps)
            logger.debug("got {} traces from {} inps"
                         .format(new_dtraces.siz, len(new_inps)))
            return new_dtraces

    def approx(self, deg, dtraces, inps, infer_f):
        """iterative refinment algorithm"""
        
        assert deg >= 1, deg
        assert isinstance(dtraces, DTraces) and dtraces, dtraces        
        assert isinstance(inps, Inps), inps        

        dinvs = DInvs()
        locs = dtraces.keys()
        curIter = 0
        while True:
            if not locs:
                logger.debug("no new traces")
                break

            dinvs_, locsMoreTraces = infer_f(deg, locs, dtraces, curIter==0)
            deltas = dinvs_.update(dinvs)
            
            curIter += 1
            logger.info(
                "iter {}, invs {}, inps {}, traces {}, rand {}".
                format(curIter, dinvs.siz, len(inps), dtraces.siz,
                       sage.all.randint(0,100)))

            if locsMoreTraces:
                logger.debug("getting more traces for {} locs: {}"
                             .format(len(locsMoreTraces),
                                     ",".join(map(str, locsMoreTraces))))
                dinvsFalse = DInvs.mkFalses(locsMoreTraces)
                dtraces_ = self.checkInvs(dinvsFalse, inps, doSafe=False)
                new_dtraces = dtraces_.update(dtraces)
                locs = new_dtraces.keys()
                continue

            #deltas means some changed
            #(this could be adding to or removing from dinvs, thus
            #deltas.siz could be 0, e.g., dinvs has a, b and dinvs_ has a)
            if deltas:
                logger.debug("{} new invs:\n{}"
                             .format(deltas.siz,
                                     deltas.__str__(printStat=True)))
            else:
                logger.debug("no new invs")
                break

            dtraces_ = self.checkInvs(dinvs, inps, doSafe=False)
            new_dtraces = dtraces_.update(dtraces)
            locs = new_dtraces.keys()
            
        return dinvs
        
    def infer(self, deg, locs, dtraces, solverCls, doWeak):
        """
        call DIG's algorithm to infer invariants from traces
        """
        assert deg >= 1 or callable(deg), deg
        assert isinstance(locs, list) and locs, locs
        assert isinstance(dtraces, DTraces) and dtraces, dtraces

        locsMoreTraces = []
        dinvs = DInvs()
        for loc in locs:
            assert dtraces[loc], loc
            terms = [sage.all.var(k) for k in self.invdecls[loc]]
            logger.debug("infer using vars: {}, deg: {}, and traces: {}".format(
                len(terms), deg, len(dtraces[loc])))
            
            try:
                traces = (t._dict for t in dtraces[loc])
                if callable(deg):
                    deg = deg(len(terms))
                    logger.info("autodeg {}".format(deg))
                    
                if issubclass(solverCls, EqtSolver): #eqts
                    terms = miscs.getTerms(terms, deg)
                    solver = solverCls(traces)
                    invs = solver.solve(terms)
                    
                else:  #ieqs
                    solver = solverCls(traces)
                    if doWeak:
                        invs = solver.solveWeak(terms)
                    else:
                        invs = solver.solve(terms)

                invs = solverCls.refine(invs)
                for inv in invs:
                    dinvs.addToSet(loc, Inv(inv))
                    
            except miscs.NotEnoughTraces as ex:
                logger.detail("loc {}: {}".format(loc, ex))                
                locsMoreTraces.append(loc)

        return dinvs, locsMoreTraces
        
