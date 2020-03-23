#Todo 1: parallelize equations (should speed up lcm etc)
#Todo 2: eqts, after generate candidates first time, check them against init traces
#then add the cex traces to exprs
#Todo 4: no need to exclude inps when checking inv

from collections import OrderedDict
import os.path
import sage.all

import vu_common as CM
import sageutil
from miscs import Miscs
from src import Src

import settings
logger = CM.VLog('alg')
logger.level = settings.logger_level  
logger.printtime = settings.logger_printtime

from ds import Inp, Inps, Traces, DTraces, Inv, Invs, DInvs
from prover import Prover

class Gen(object):
    def __init__(self, inpdecls, invdecls, tcsFile, exeFile, prover):
        self.invdecls = invdecls
        self.inpdecls = inpdecls
        self.tcsFile = tcsFile
        self.exeFile = exeFile
        self.prover = prover
        
    def getTraces(self, inps):
        """
        Run program on inps and get traces
        """
        assert isinstance(inps, Inps) and inps, inps

        tcsFile = "{}_{}".format(self.tcsFile, hash(str(inps))).replace("-","_")
        if os.path.isfile(tcsFile):
            traces = DTraces.parse(tcsFile, self.invdecls)
        else:
            for inp in inps:
                inp_ = ' '.join(map(str, inp))
                cmd = "{} {} >> {}".format(self.exeFile, inp_, tcsFile)
                logger.detail(cmd)
                CM.vcmd(cmd)
            traces = DTraces.parse(tcsFile, self.invdecls)

        assert all(loc in self.invdecls for loc in traces), traces.keys()
        return traces

    @staticmethod
    def updateInps(newDInps, inps):
        if not newDInps: return Inps()
        _f = lambda dInps: (Inp(inp) for loc in dInps
                            for inv in dInps[loc]
                            for inp in dInps[loc][inv])
        if isinstance(newDInps, dict):
            newInps = _f(newDInps)
        else:
            assert isinstance(newDInps, list) and newDInps, newDInps
            newInps = [inp for d in newDInps for inp in _f(d)]

        newInps = Inps(inp for inp in newInps if inp not in inps)
        for inp in newInps: inps.add(inp) #update inps
        return newInps

    def getTracesAndUpdate(self, inps, traces):
        assert inps
        newTraces = self.getTraces(inps)
        newTraces = newTraces.update(traces, self.invdecls)
        return newTraces

    def checkReach(self):
        #check for reachability using inv False (0)
        dinvs = DInvs.mkFalses(self.invdecls)        
        inps = Inps()

        #use some initial inps first
        rinps = Miscs.genInitInps(len(self.inpdecls), DTraces.inpMaxV)
        logger.debug("gen {} random inps".format(len(rinps)))
        for inp in rinps: inps.add(Inp(inp))
        
        traces = self.getTraces(inps)
        unreachLocs = [loc for loc in dinvs if loc not in traces]
        if unreachLocs:
            logger.debug("use RT to generate traces for {}".format(
                ','.join(map(str, unreachLocs))))
            unreachInvs = DInvs.mkFalses(unreachLocs)
            cInps, _, _ = self.prover.checkRange(unreachInvs, inps=None)
            newInps = self.updateInps(cInps, inps)
            _ = self.getTracesAndUpdate(newInps, traces)
            
        #remove FALSE invs indicating unreached locs
        for loc in traces:
            assert traces[loc]
            dinvs[loc].clear()

        return dinvs, traces, inps    
        
class GenEqts(Gen):
    def __init__(self, inpdecls, invdecls, tcsFile, exeFile, prover):
        super(GenEqts, self).__init__(inpdecls, invdecls, tcsFile, exeFile, prover)


    def getInitTraces(self, loc, deg, traces, inps, rate=1.5):
        vs = tuple(self.invdecls[loc])
        
        terms = Miscs.getTerms([sage.all.var(k) for k in vs], deg)
        template, uks = Miscs.mkTemplate(terms, 0, retCoefVars=True)
        nEqtsNeeded = int(rate * len(uks))
        exprs = traces[loc].instantiate(template, nEqtsNeeded)

        while nEqtsNeeded > len(exprs):
            logger.debug("{}: need more traces ({} eqts, need >= {})"
                         .format(loc, len(exprs), nEqtsNeeded))
            dinvsFalse = DInvs.mkFalses([loc])
            cInps, _, _ = self.prover.checkRange(dinvsFalse, inps)
            if loc not in cInps:
                logger.warn("{}: cannot generate enough traces".format(loc))
                return
            
            newInps = Gen.updateInps(cInps, inps)
            newTraces = self.getTracesAndUpdate(newInps, traces)
            assert newTraces[loc]
            logger.debug("obtain {} new traces".format(len(newTraces[loc])))
            newExprs = newTraces[loc].instantiate(template,
                                                  nEqtsNeeded - len(exprs))
            for expr in newExprs:
                assert expr not in exprs
                exprs.add(expr)
                
        return template, uks, exprs

    def infer(self, loc, template, uks, exprs, dtraces, inps):
        assert isinstance(loc, str), loc
        assert sageutil.is_sage_expr(template), template
        assert isinstance(uks, list), uks
        assert isinstance(exprs, set) and exprs, exprs
        assert isinstance(dtraces, DTraces) and dtraces, dtraces
        assert isinstance(inps, Inps) and inps, inps

        vs = tuple(self.invdecls[loc])
        cache = set()
        eqts = set() #results
        exprs = list(exprs)

        newInps = []
        while True:
            logger.debug("{}: infer using {} exprs".format(loc, len(exprs)))
            newEqts = Miscs.solveEqts(exprs, uks, template)
            unchecks = [eqt for eqt in newEqts if eqt not in cache]

            if not unchecks:
                logger.debug("{}: no new results -- break".format(loc))
                break
                
            logger.debug('{}: {} candidates:\n{}'.format(
                loc, len(newEqts), '\n'.join(map(str, newEqts))))

            logger.debug("{}: check {} unchecked ({} candidates)"
                         .format(loc, len(unchecks), len(newEqts)))

            dinvs = DInvs.mk(loc, Invs.mk(map(Inv, unchecks)))
            dInps, dCexs, dinvs = self.prover.checkRange(dinvs, inps=None) 

            if dInps: newInps.append(dInps)
            _ = [eqts.add(inv) for inv in dinvs[loc] if not inv.isDisproved]
            _ = [cache.add(inv.inv) for inv in dinvs[loc]
                 if inv.stat is not None]

            if loc not in dCexs:
                logger.debug("{}: no disproved candidates -- break".format(loc))
                break

            cexs = Traces.extract(dCexs[loc], vs)
            exprs_ = cexs.instantiate(template, None)

            logger.debug("{}: {} new cex exprs".format(loc, len(exprs_)))
            exprs.extend(exprs_)

        return eqts, newInps
                
    def gen(self, deg, traces, inps):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces) and traces, traces                
        assert isinstance(inps, Inps), inps

        #first obtain enough traces
        initrs = [self.getInitTraces(loc, deg, traces, inps) for loc in traces]
        tasks = [(loc, rs) for loc, rs in zip(traces, initrs) if rs]

        #then solve/prove in parallel
        def wprocess(tasks, Q):
            rs = [(loc, self.infer(loc, template, uks, exprs, traces, inps))
                  for loc, (template, uks, exprs) in tasks]
            if Q is None:
                return rs
            else:
                Q.put(rs)

        wrs = Miscs.runMP('find eqts', tasks, wprocess, chunksiz=1,
                          doMP=settings.doMP and len(tasks) >= 2)

        dinvs = DInvs()            
        for loc, (eqts, newInps) in wrs:
            newInps = Gen.updateInps(newInps, inps)
            logger.debug("{}: got {} eqts, {} new inps".format(loc, len(eqts), len(newInps)))
            if eqts: logger.debug('\n'.join(map(str, eqts)))
            dinvs[loc] = Invs.mk(eqts)
        return dinvs

class GenIeqs(Gen):
    def __init__(self, inpdecls, invdecls, tcsFile, exeFile, prover):
        super(GenIeqs, self).__init__(inpdecls, invdecls, tcsFile, exeFile, prover) 
        
    def gen(self, deg, traces, inps):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces), traces
        assert isinstance(inps, Inps), inps

        assert isinstance(traces, DTraces) and traces, traces                
        assert isinstance(inps, Inps), inps

        mymaxv  = 10
        maxV = mymaxv
        minV = -1*maxV

        #without these restrictions, klee takes a long time to run
        ubmaxV = maxV*2
        ubminV = -1*ubmaxV

        locs = traces.keys()
        vss = [[sage.all.var(k) for k in self.invdecls[loc]]  for loc in locs]
        mydeg = 2
        if mydeg > 2:
            logger.warn("not Oct invs (deg {}). Might be slow".format(deg))
        termss = [Miscs.getTermsFixedCoefs(vs, mydeg) for vs in vss]
        logger.info("{} locs: check upperbounds for {} terms".format(
            len(locs), sum(map(len, termss))))
        
        refs = {loc: {Inv(t <= maxV): t for t in terms}
                for loc, terms in zip(locs, termss)}
        ieqs = DInvs((loc, Invs.mk(refs[loc].keys())) for loc in refs)
        myinps = None
        cInps, cTraces, ieqs = self.prover.check(ieqs, myinps, ubminV, ubmaxV)
        if cInps:
            newInps = Gen.updateInps(cInps, inps)
            _ = self.getTracesAndUpdate(newInps, traces)
        
        ieqs = ieqs.removeDisproved()
        tasks = [(loc, refs[loc][ieq]) for loc in ieqs for ieq in ieqs[loc]]

        logger.debug("{} locs: compute upperbounds for {} terms".format(
            len(locs), len(tasks)))
        
        def _f(loc, term):
            vs = traces[loc].myeval(term)
            try:
                mminV = int(max(minV, max(v for v in vs if v < maxV)))
            except ValueError:
                mminV = minV
                
            logger.detail("{}: compute ub for '{}', start w/ min {}, maxV {})"
                         .format(loc, term, mminV, maxV))
            
            disproves = set()
            boundV = self.guessCheck(loc, term, traces, inps, 
                                     mminV, maxV, ubminV, ubmaxV, disproves)
            if boundV not in disproves and boundV not in {maxV, minV}:
                inv = Inv(term <= boundV)
                logger.detail("got {}".format(inv))
                return inv
            else:
                return None

        def wprocess(tasks, Q):
            rs = [(loc, _f(loc, term)) for loc, term in tasks]
            if Q is None:
                return rs
            else:
                Q.put(rs)
        
        doMP = settings.doMP and len(tasks) >= 2
        wrs = Miscs.runMP('guesscheck', tasks, wprocess, chunksiz=1, doMP=doMP)
        rs = [(loc, inv) for loc, inv in wrs if inv]
        dinvs = DInvs()
        for loc, inv in rs:
            if loc not in dinvs: dinvs[loc] = Invs()
            dinvs[loc].add(inv)
        return dinvs

    def guessCheck(self, loc, term, traces, inps, minV, maxV,
                   ubMinV, ubMaxV, disproves):
        assert minV <= maxV, (minV, maxV, term)
        assert ubMinV < ubMaxV, (ubMinV, ubMaxV)
        assert isinstance(traces, DTraces), traces
        assert isinstance(disproves, set), disproves

        #print term, minV, maxV, ubMinV, ubMaxV
        if minV == maxV: return maxV
        elif maxV - minV == 1:
            if minV in disproves:
                return maxV
            inv = Inv(term <= minV)
            inv_ = DInvs.mk(loc, Invs.mk([inv]))
            _, dCexs, _ = self.prover.check(inv_, None, ubMinV, ubMaxV)

            if loc in dCexs:
                assert dCexs[loc]
                disproves.add(minV)
                return maxV
            else:
                return minV

        v = sage.all.ceil((maxV + minV)/2.0)
        inv = Inv(term <= v)
        inv_ = DInvs.mk(loc, Invs.mk([inv]))
        _, dCexs, _ = self.prover.check(inv_, None, ubMinV, ubMaxV)
            
            
        if loc in dCexs: #disproved
            assert dCexs[loc]            
            cexs = Traces.extract(dCexs[loc], tuple(self.invdecls[loc]),
                                  useOne=False)
            minV = int(max(cexs.myeval(term)))
            disproves.add(v)
        else:
            maxV = v

        return self.guessCheck(loc, term, traces, inps,
                               minV, maxV, ubMinV, ubMaxV,
                               disproves)

class DIG2(object):
    def __init__(self, filename):
        assert os.path.isfile(filename), filename

        import tempfile
        tmpdir = tempfile.mkdtemp(dir=settings.tmpdir, prefix="DIG2_")
        basename = os.path.basename(filename)
        src = os.path.join(tmpdir, basename)
        _, rs_err = CM.vcmd("astyle -Y < {} > {}".format(filename, src))
        assert not rs_err, rs_err
        logger.debug("src: {}".format(src))
        src = Src(src)
        self.inpdecls, self.invdecls = src.parse()
        printfSrc = src.instrPrintfs(self.invdecls)
        exeFile = "{}.exe".format(printfSrc)
        cmd = "gcc -lm {} -o {}".format(printfSrc, exeFile) #-lm for math.h
        CM.vcmd(cmd)
        tcsFile =  "{}.tcs".format(printfSrc) #tracefile

        self.prover = Prover(src, self.inpdecls, self.invdecls, tmpdir)
        self.tmpdir = tmpdir
        self.filename = filename
        self.tcsFile = tcsFile
        self.exeFile = exeFile
        logger.info("analyze {}".format(filename))


    def start(self, seed, maxdeg, maxterm, doEqts, doIeqs):
        assert isinstance(seed, (int,float)), seed
        assert isinstance(doEqts, bool), doEqts
        assert isinstance(doIeqs, bool), doIeqs

        from time import time
        st = time()
        
        import random
        random.seed(seed)
        sage.all.set_random_seed(seed)
        logger.info('set seed to: {} (test {})'
                    .format(seed, sage.all.randint(0,100)))

        ##determine degree
        maxvars = max(self.invdecls.itervalues(), key=lambda d: len(d))
        deg = Miscs.getAutoDeg(maxdeg, maxterm, len(maxvars))

        solver =  Gen(self.inpdecls, self.invdecls, self.tcsFile, self.exeFile, self.prover)        
        logger.info("check reachability")
        dinvs, traces, inps = solver.checkReach()
        if not traces:
            return dinvs

        def strOfLocs(locs):
            _f = lambda vts: ', '.join("{} {}".format(vts[v], v) for v in vts)
            s = '; '.join("{} ({})".format(
                loc, _f(self.invdecls[loc])) for loc in locs)
            return "{} locs: {}".format(len(locs), s)
            
        def _gen(typ):
            st_gen = time()
            cls = GenEqts if typ == 'eqts' else GenIeqs
            logger.info("gen {} at {}".format(typ, strOfLocs(traces.keys())))
            solver =  cls(self.inpdecls, self.invdecls, self.tcsFile, self.exeFile, self.prover)
            invs = solver.gen(deg, traces, inps)

            logger.debug("gen {}: ({}s)".format(typ, time() - st_gen))
            if invs:
                dinvs.merge(invs)
                logger.info("{} invs:\n{}".format(dinvs.siz, dinvs))                
            
        if doEqts: _gen('eqts')
        if doIeqs: _gen('ieqs')        
            
        logger.info("test {} invs on all {} traces".format(dinvs.siz, traces.siz))
        dinvs = dinvs.testTraces(traces)

        logger.info("find uniq invs")
        st_uniq = time()
        logger.info("{} invs:\n{}".format(dinvs.siz, dinvs))
        oldSiz = dinvs.siz
        
        def wprocess(tasks, Q):
            rs = [(loc, Miscs.reduceSMT(invs)) for loc, invs in tasks]
            if Q is None:
                return rs
            else:
                Q.put(rs)
        
        tasks = [(loc, [inv.inv for inv in dinvs[loc]]) for loc in dinvs]
        wrs = Miscs.runMP("uniqify", tasks, wprocess, chunksiz=1,
                          doMP=settings.doMP and len(tasks) >= 2)

        dinvs = DInvs((loc, Invs(map(Inv, invs)))
                      for loc, invs in wrs if invs)

        logger.debug("uniqify: remove {} redundant invs ({}s)"
                     .format(oldSiz - dinvs.siz, time() - st_uniq))

        logger.info("*** {}, {} locs, invs {}, inps {}, time {} s, rand {}: \n{}"
                    .format(self.filename, len(dinvs), dinvs.siz, len(inps), 
                            time() - st, sage.all.randint(0,100),
                            dinvs))
        import shutil
        logger.debug("rm -rf {}".format(self.tmpdir))
        shutil.rmtree(self.tmpdir)
        
        return dinvs
