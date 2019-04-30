from time import time
from abc import ABCMeta, abstractmethod
import math
import os.path
import sage.all
import vcommon as CM
from miscs import Miscs
from ds import Inps, Traces, DTraces, Inv, Invs, DInvs
from cegir import Cegir

import settings
mlog = CM.getLogger(__name__, settings.logger_level)


class CegirEqts(Cegir):
    def __init__(self, symstates, prog):
        super(CegirEqts, self).__init__(symstates, prog)
        self.useRandInit = False  # use symstates or random to get init inps

    def whileRand(self, loc, template, nEqtsNeeded, inps, traces):
        """
        repeatedly get more inps using random method
        """
        exprs = traces[loc].instantiate(template, nEqtsNeeded)

        doRand = True
        while nEqtsNeeded > len(exprs):
            newTraces = {}
            mlog.debug("{}: need more traces ({} eqts, need >= {}, inps {})"
                       .format(loc, len(exprs), nEqtsNeeded, len(inps)))
            if doRand:
                rInps = self.symstates.genRandInps(self.prog)
                mlog.debug("gen {} random inps".format(len(rInps)))
                rInps = inps.myupdate(rInps, self.inpDecls.names)
                if rInps:
                    newTraces = self.getTracesAndUpdate(rInps, traces)

            if loc not in newTraces:
                doRand = False

                dinvsFalse = DInvs.mkFalses([loc])
                cexs, _ = self.symstates.check(dinvsFalse, inps)
                # cannot find new inputs
                if loc not in cexs:
                    mlog.debug("{}: cannot find new inps (curr inps :{})"
                               .format(loc, len(inps)))
                    return

                newInps = inps.myupdate(cexs, self.inpDecls.names)
                newTraces = self.getTracesAndUpdate(newInps, traces)

                # cannot find new traces (new inps do not produce new traces)
                if loc not in newTraces:
                    ss = ["{}: cannot find new traces".format(loc),
                          "(new inps {}, ".format(len(newInps)),
                          "curr traces {})".format(
                              len(traces[loc]) if loc in traces else 0)]
                    mlog.debug(', '.join(ss))
                    return

            assert newTraces[loc]
            mlog.debug("obtain {} new traces".format(len(newTraces[loc])))
            newExprs = newTraces[loc].instantiate(
                template, nEqtsNeeded - len(exprs))

            for expr in newExprs:
                assert expr not in exprs
                exprs.add(expr)

        return exprs

    def whileSymstates(self, loc, template, nEqtsNeeded, inps, traces):
        """
        repeated get more traces using the symstates (e.g., Klee)
        """
        assert isinstance(loc, str), loc
        assert nEqtsNeeded >= 1, nEqtsNeeded

        exprs = traces[loc].instantiate(template, nEqtsNeeded)
        while nEqtsNeeded > len(exprs):
            mlog.debug("{}: need more traces ({} eqts, need >= {})"
                       .format(loc, len(exprs), nEqtsNeeded))
            dinvsFalse = DInvs.mkFalses([loc])
            cexs, _ = self.symstates.check(dinvsFalse, inps)
            if loc not in cexs:
                mlog.error("{}: cannot generate enough traces".format(loc))
                return

            newInps = inps.myupdate(cexs, self.inpDecls.names)
            newTraces = self.getTracesAndUpdate(newInps, traces)
            assert newTraces[loc]
            mlog.debug("obtain {} new traces".format(len(newTraces[loc])))
            newExprs = newTraces[loc].instantiate(
                template, nEqtsNeeded - len(exprs))

            for expr in newExprs:
                assert expr not in exprs
                exprs.add(expr)

        return exprs

    def getInitTraces(self, loc, deg, traces, inps, rate):
        "Initial loop to obtain (random) traces to bootstrap eqt solving"

        assert deg >= 1, deg
        assert isinstance(rate, float) and rate >= 0.1, rate

        if self.useRandInit:
            whileF, whileFName = self.whileRand, "random"
        else:
            whileF, whileFName = self.whileSymstates, "symstates"
        mlog.debug("{}: gen init inps using {} (curr inps {}, traces {})"
                   .format(loc, whileFName, len(inps), len(traces)))

        terms, template, uks, nEqtsNeeded = Miscs.initTerms(
            self.invDecls[loc].names, deg, rate)
        exprs = whileF(loc, template, nEqtsNeeded, inps, traces)

        # if cannot generate sufficient traces, adjust degree
        while (not exprs):
            if deg < 2:
                return  # cannot generate enough traces

            deg = deg - 1
            mlog.info("Reduce polynomial degree to {}, terms {}, uks {}"
                      .format(deg, len(terms), len(uks)))
            terms, template, uks, nEqtsNeeded = Miscs.initTerms(
                self.invDecls[loc].names, deg, rate)
            exprs = whileF(loc, template, nEqtsNeeded, inps, traces)

        return template, uks, exprs

    def infer(self, loc, template, uks, exprs, dtraces, inps):
        assert isinstance(loc, str) and loc, loc
        assert Miscs.isExpr(template), template
        assert isinstance(uks, list), uks
        assert isinstance(exprs, set) and exprs, exprs
        assert isinstance(dtraces, DTraces) and dtraces, dtraces
        assert isinstance(inps, Inps) and inps, inps

        cache = set()
        eqts = set()  # results
        exprs = list(exprs)

        newCexs = []
        curIter = 0

        while True:
            curIter += 1
            mlog.debug("{}, iter {} infer using {} exprs"
                       .format(loc, curIter, len(exprs)))

            newEqts = Miscs.solveEqts(exprs, uks, template)
            unchecks = [eqt for eqt in newEqts if eqt not in cache]

            if not unchecks:
                mlog.debug("{}: no new results -- break".format(loc))
                break

            mlog.debug('{}: {} candidates:\n{}'.format(
                loc, len(newEqts), '\n'.join(map(str, newEqts))))

            mlog.debug("{}: check {} unchecked ({} candidates)"
                       .format(loc, len(unchecks), len(newEqts)))

            dinvs = DInvs.mk(loc, Invs.mk(map(Inv, unchecks)))
            cexs, dinvs = self.symstates.check(dinvs, inps=None)

            if cexs:
                newCexs.append(cexs)

            _ = [eqts.add(inv) for inv in dinvs[loc] if not inv.isDisproved]
            _ = [cache.add(inv.inv) for inv in dinvs[loc]
                 if inv.stat is not None]

            if loc not in cexs:
                mlog.debug("{}: no disproved candidates -- break".format(loc))
                break

            cexs = Traces.extract(cexs[loc])
            cexs = cexs.padZeros(set(self.invDecls[loc].names))
            exprs_ = cexs.instantiate(template, None)
            mlog.debug("{}: {} new cex exprs".format(loc, len(exprs_)))
            exprs.extend(exprs_)

        return eqts, newCexs

    def gen(self, deg, traces, inps):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces) and traces, traces
        assert isinstance(inps, Inps), inps

        # first obtain enough traces
        initrs = [self.getInitTraces(loc, deg, traces, inps, settings.eqtrate)
                  for loc in traces]
        tasks = [(loc, rs) for loc, rs in zip(traces, initrs) if rs]
        if not tasks:  # e.g., cannot obtain enough traces
            return

        # then solve/prove in parallel
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
        for loc, (eqts, newCexs) in wrs:
            newInps = inps.myupdate(newCexs, self.inpDecls.names)
            mlog.debug("{}: got {} eqts, {} new inps"
                       .format(loc, len(eqts), len(newInps)))
            if eqts:
                mlog.debug('\n'.join(map(str, eqts)))
            dinvs[loc] = Invs.mk(eqts)

        return dinvs
