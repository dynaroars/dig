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
from cpa import RT   #Reachability Tool
from src import Src
import solver

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
    def parse(cls, tracefile):
        """
        parse trace for new traces
        """
        assert isinstance(tracefile, str), tracefile        

        dtraces = {}
        for l in CM.iread_strip(tracefile):
            #disproved x + y == 0 @ line 20: 924 9 0 1 9 924
            inv_s, trace_s = l.split(':')
            #lineno = parts[0].strip()  #l22
            
            #inv
            inv_s, line_s = inv_s.strip().split('@')
            inv = inv_s.replace('disproved', '').strip()
            
            #traces
            tracevals = trace_s.strip().split()
            tracevals = tuple(miscs.ratOfStr(t) for t in tracevals)
            if inv not in dtraces:
                dtraces[inv] = set()
            dtraces[inv].add(tracevals)
        return dtraces

class MySet(MutableSet):
    __metaclass__ = abc.ABCMeta
    def __init__(self): self.__set__ = set()
    def __len__(self): return len(self.__set__)
    def __iter__(self): return iter(self.__set__)    
    def __str__(self): return ", ".join(map(str, sorted(self)))
    def discard(self): raise NotImplementedError("discard")
    
    @abc.abstractmethod
    def __contains__(self, inp): return inp in self.__set__
    @abc.abstractmethod
    def add(self, inp):
        notIn = False
        if inp not in self.__set__:
            notIn = True
            self.__set__.add(inp)
        return notIn
    
class Inv(object):
    PROVED = "p"
    DISPROVED = "d"
    UNKNOWN = "u"
    
    def __init__(self, inv):
        assert inv == 0 or inv == 1 or inv.is_relational(), inv
        self.resetStat()
        #self.resetTemplateID()

        self.inv = inv
        
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

class Invs(MySet):
    def __contains__(self, inv):
        assert isinstance(inv, Inv), inv
        return super(Invs, self).__contains__(inv)

    def add(self, inv):
        assert isinstance(inv, Inv), inv
        return super(Invs, self).add(inv)

    def remove(self, inv):
        assert isinstance(inv, Inv), inv
        self.__set__.remove(inv)

    def clear(self):
        self.__set__.clear()

    def __str__(self, printStat=False):
        return ", ".join(map(lambda inv: inv.__str__(printStat), sorted(self)))

    def resetStats(self):
        for inv in self:
            inv.resetStat()

    def removeDisproved(self, disproves={}):
        newInvs = Invs()
        for inv in self:
            if not (inv.isDisproved or inv in disproves):
                newInvs.add(inv)
        self.__set__ = newInvs
        
    @classmethod
    def mk(cls, invs):
        newInvs = Invs()
        if not CM.is_iterable(invs):
            newInvs.add(invs)
        else:
            for inv in invs:
                newInvs.add(inv)
        return newInvs
    
class DIG2(object):
    def __init__(self, filename, tmpdir):
        assert os.path.isfile(filename), filename
        assert os.path.isdir(tmpdir), tmpdir
        self.filename = filename
        self.tmpdir = tmpdir
        self.rtCalls = 0
        
    # def genEqts(self, invs, inps, traces):
    #     exprs = set()
    #     curIter = 0
        
    #     while True:
    #         curIter += 1
    #         logger.info(
    #             "iter {}, invs {}, inps {}, traces {}, exprs {}, rand {}".
    #             format(curIter, len(invs), len(inps), len(traces), len(exprs),
    #                    sage.all.randint(0,100)))
    #         logger.debug(str(invs))

    #         if not traces:
    #             logger.debug("no more traces")
    #             break

    #         try:
    #             invs_ = self.infer(traces, exprs, solvercls)
    #             if invs_:
    #                 logger.debug(str(invs_))
    #         except solver.NotEnoughTraces as e:
    #             logger.detail(str(e))
    #             invs__ = Invs()
    #             invs__.add(Inv(0))
    #             traces = self.check(invs__, inps, solvercls.minV, solvercls.maxV)
    #             continue
    #         except solver.SameInsts as e:
    #             logger.detail(str(e))
    #             break  

    #         if not invs_ or invs_ == invs:
    #             break

    #         invs = invs_
    #         traces = self.check(invs, inps, solvercls.minV, solvercls.maxV)
    #         print 'traces', traces
    #         invs = invs.removeDisproved()
            
    #     return invs

    def guessCheck(self, term, etraces, minV, maxV, oMinV, oMaxV):
        assert minV <= maxV, (minV, maxV)
        assert oMinV < oMaxV, (oMinV, oMaxV)
        assert isinstance(etraces, set), etraces
        
        if minV == maxV:
            return maxV
        elif maxV - minV == 1:
            inv = Inv(term <= minV)
            print 'final rt {}'.format(inv)
            disproved = self.checkRT(Invs.mk(inv), set(),
                                     oMinV, oMaxV, quickbreak=True)
            return maxV if disproved else minV
            
        v = sage.all.ceil((maxV + minV)/2.0)
        inv = Inv(term <= v)
        #print 'rt {}'.format(inv)
        traces = self.check(Invs.mk(inv), set(), oMinV, oMaxV, dorandom=False)
        print term, minV, maxV, 'checking ', inv
        if traces: #disproved
            minV = max(term.subs(tc._dict) for tc in traces)
            for tc in traces: etraces.add(tc)
            print 'disproved', minV
        else:
            maxV = v
            print 'proved', maxV

        return self.guessCheck(term, etraces, minV, maxV, oMinV, oMaxV)

    def genEqts1(self, einps, traces):
        exprs = set()
        terms = miscs.getTerms(self.ss, self.deg)
        from solver import EqtSolver
        solvercls = EqtSolver()
        minV, maxV = EqtSolver.minV, EqtSolver.maxV
        
        eqts = Invs()
        while True:
            if not traces:
                logger.debug("no more traces")
                break

            try:
                #infer
                neweqts = solvercls.solve(terms, traces, exprs)
                neweqts = Invs.mk(map(Inv, neweqts))
                if neweqts:  logger.debug(str(neweqts))
            except solver.NotEnoughTraces as e:
                logger.debug(str(e))
                traces = self.check(Invs.mk(Inv.mkFalse()), einps, minV, maxV)
                continue
            except solver.SameInsts as e:
                logger.debug(str(e))
                break

            if not neweqts or neweqts == eqts:
                break

            eqts = neweqts
            traces = self.check(eqts, einps, minV, maxV)
            eqts.removeDisproved()

        return eqts

    def genOcts(self, einps, etraces):
        logger.debug("generate octagonal invs")

        mminV, mmaxV = self.minV + 1, self.maxV - 1
        #octagonal invs        
        solvercls = solver.OctSolver()
        octTerms = solvercls.getTerms(self.ss)  #x,-x, x-y, -x+y, ..
        # print octTerms
        # CM.pause()
        
        octInvs = [Inv(ot <= mmaxV) for ot in octTerms]
            
        octD = dict(zip(octInvs, octTerms))

        octInvs = Invs.mk(octInvs)
        for oInv in octInvs:
            print oInv
        CM.pause()
        disproved = self.checkRT(octInvs, einps,
                                 self.unboundMinV, self.unboundMaxV,
                                 quickbreak=False)

        print disproved
        CM.pause("disproved")
        octInvs.removeDisproved(disproved)
        invs = Invs()
        for octInv in octInvs:
            octTerm = octD[octInv]            
            logger.detail("refine {} (compute upperbound for '{}')"
                          .format(octInv, octTerm))

            mminV = max(octTerm.subs(tc._dict) for tc in etraces)
            boundV = self.guessCheck(octTerm, etraces,
                                     mminV, mmaxV,
                                     self.unboundMinV, self.unboundMaxV)
            inv = Inv(octTerm <= boundV)
            print 'obtained', inv
            invs.add(inv)
            logger.detail("{}".format(inv))            

        if invs:
            logger.info("{} ieqs (rtCalls {})\n{}"
                        .format(len(invs), self.rtCalls, invs))
            
        return invs
            
    def start(self, seed, deg, maxtime):
        assert isinstance(seed, (int,float)), seed
        assert deg >= 1 or callable(deg), deg
        assert isinstance(maxtime, int) and maxtime >= 1, maxtime
        
        self.initialize(seed, deg, maxtime)
        invs = Invs()
        
        einps, etraces = set(), set()
        
        logger.debug("check reachability")
        traces = self.check(Invs.mk(Inv.mkFalse()), einps, self.minV, self.maxV)
        for tc in traces: etraces.add(tc)
        
        if not traces:
            logger.warn("Unreachable location (inv = False)")            
            return
        
        # binvs = self.genOcts(einps, etraces)
        # for inv in binvs: invs.add(inv)

        # print 'traces: ', len(etraces)
        binvs = self.genEqts1(einps, etraces)
        for inv in binvs: invs.add(inv)
        print 'traces: ', len(etraces)
        
        logger.info("final checking {} candidate invs\n{}"
                    .format(len(invs), invs))
        disproved = self.checkRT(
            invs, einps, self.unboundMinV, self.unboundMaxV, quickbreak=False)
        invs.removeDisproved(disproved)
        logger.debug(str(invs))
        return invs

    def mexec(self, exe, inps):
        assert isinstance(exe, str) and exe.endswith(".exe"), exe
        assert isinstance(inps, set) and inps, inps
        
        if os.path.isfile(self.tcsFile): os.remove(self.tcsFile)
        for inp in inps:
            inp = ' '.join(map(str, inp))
            cmd = "{} {} >> {}".format(exe, inp, self.tcsFile)
            logger.detail(cmd)
            CM.vcmd(cmd)
        return Trace.parse(self.tcsFile)

    def pp(self, invs, dtraces, maxV):
        maxV = maxV + 1
        checkvals = lambda vs: all(-1*maxV <= v <= maxV for v in vs)

        ss = self.invdecls.keys()
        traces = []
        for inv in invs:
            k = str(inv)
            if k in dtraces:
                logger.detail("{} disproved".format(inv))
                inv.stat = Inv.DISPROVED
                ts = [Trace(zip(ss, t))
                      for t in dtraces[k] if checkvals(t)]
                traces.extend(ts)
            else:
                inv.stat = Inv.UNKNOWN

        return traces

    def checkRT(self, invs, einps, minV, maxV, quickbreak):
        assert isinstance(invs, Invs) and invs, invs
        assert isinstance(einps, set), einps
        assert minV < maxV, (minV, maxV)
        assert isinstance(quickbreak, bool), quickbreak
        
        if self.inpdecls:
            inps_d = OrderedDict(
                (vname, (vtyp, (minV, maxV)))
                for vname, vtyp in self.inpdecls.iteritems())
        else:
            inps_d = None

        disproved = {}
        for inv in invs:
            einps_ = set(CM.HDict(zip(self.inpdecls, inp)) for inp in einps)
            rtSrc = self.src.instrAssertsRT(set([inv]), einps_, inps_d,
                                            self.invdecls, self.lineno)
            _, inps = RT(rtSrc, self.maxtime, self.tmpdir).getDInps()  #run
            self.rtCalls += 1
            if inps:
                logger.detail("RT disproved {}".format(inv))
                disproved[inv] = inps
                if quickbreak:
                    return disproved
        return disproved
                
    def check(self, invs, einps, minV, maxV, dorandom=True):
        assert isinstance(invs, Invs) and invs, invs 
        assert isinstance(einps, set) #existing inps

        src = self.src.instrDisproves(invs, self.invdecls, self.lineno)
        exe = "{}.exe".format(src)
        cmd = "gcc -lm {} -o {}".format(src, exe) 
        rs, rs_err = CM.vcmd(cmd)
        assert not rs, rs
        assert not rs_err, rs_err

        traces = None
        if dorandom:
            inps = miscs.genInps(len(self.inpdecls), maxV)
            for inp in inps: einps.add(inp)
            dtraces = self.mexec(exe, inps)
            traces = self.pp(invs, dtraces, maxV)

        #use RT
        if not traces:
            disproved = self.checkRT(invs, einps, minV, maxV, quickbreak=True)
            if disproved:
                inps = set()
                for dinv in disproved:
                    for inp in disproved[dinv]:
                        inp = tuple([inp[str(k)] for k in self.inpdecls])
                        einps.add(inp)
                        inps.add(inp)
                dtraces = self.mexec(exe, inps)
                traces = self.pp(invs, dtraces, maxV)
        
        return traces
        
    # def infer(self, traces, exprs, solvercls):
    #     assert traces
        
    #     logger.debug("infer: vs {}, deg {}, traces {}, exprs {}".format(
    #         len(self.ss), self.deg, len(traces), len(exprs)))

    #     terms = miscs.getTerms(self.ss, self.deg)  #cache
    #     invs = solvercls().solve(terms, traces, exprs)
    #     newInvs = Invs()
    #     for inv in invs:
    #         newInvs.add(Inv(inv))
    #     return newInvs

    def initialize(self, seed, deg, maxtime):
        import random        
        random.seed(seed)
        sage.all.set_random_seed(seed)
        logger.info('set seed to: {} (test {})'
                    .format(seed, sage.all.randint(0,100)))

        fname = os.path.basename(self.filename)
        src = os.path.join(self.tmpdir, fname)
        _, rs_err = CM.vcmd("astyle -Y < {} > {}".format(self.filename, src))
        assert not rs_err, rs_err
        logger.debug("src: {}".format(src))
        
        self.src = Src(src)
        self.inpdecls, self.invdecls, self.lineno = self.src.parse()
        self.ss = [sage.all.var(k) for k in self.invdecls]

        if callable(deg):
            self.deg = deg(len(self.ss))
            logger.info("autodeg {}".format(self.deg))
        else:
            self.deg = deg

        self.maxtime = maxtime
            
        #tracefile
        self.tcsFile =  "{}.tcs".format(self.src.filename)

        from solver import IeqSolver
        self.minV, self.maxV = IeqSolver.minV, IeqSolver.maxV
        self.unboundMinV, self.unboundMaxV = self.minV * 10, self.maxV * 10
