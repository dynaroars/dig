import math
import vcommon as CM
from miscs import Miscs
from ds import Inps, Traces, DTraces, Inv, Invs, DInvs
from cegir import Cegir

import settings
mlog = CM.getLogger(__name__, settings.logger_level)


class CegirIeqs(Cegir):
    def __init__(self, symstates, prog):
        super(CegirIeqs, self).__init__(symstates, prog)

    def gen(self, deg, traces, inps):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces) and traces, traces
        assert isinstance(inps, Inps), inps

        maxV = settings.OCT_MAX_V
        minV = -1*maxV

        locs = traces.keys()
        vss = [self.invDecls[loc].sageExprs for loc in locs]

        if deg > 2:
            mlog.debug("reduce deg {} to 2 for oct ieqs".format(deg))
            deg = 2

        termss = [Miscs.getTermsFixedCoefs(vs, deg) for vs in vss]
        mlog.info("check upperbounds for {} terms at {} locs".format(
            sum(map(len, termss)), len(locs)))

        # if "a" in str(t) and "-" not in str(t)
        refs = {loc: {Inv(t <= maxV): t for t in terms}
                for loc, terms in zip(locs, termss)}

        ieqs = DInvs((loc, Invs.mk(refs[loc].keys())) for loc in refs)
        myinps = None  # dummy
        cexs, ieqs = self.symstates.check(ieqs, myinps)

        if cexs:
            newInps = inps.myupdate(cexs, self.inpDecls.names)
            if newInps:
                self.getTracesAndUpdate(newInps, traces)

        ieqs = ieqs.removeDisproved()
        tasks = [(loc, refs[loc][ieq]) for loc in ieqs for ieq in ieqs[loc]]

        mlog.debug("{} locs: compute upperbounds for {} terms".format(
            len(locs), len(tasks)))

        def _f(loc, term):
            statsd = {maxV: Inv.PROVED}

            # start with this minV
            vs = traces[loc].myeval(term)
            try:
                mminV = int(max(minV, max(v for v in vs if v < maxV)))
            except ValueError:
                mminV = minV

            # start with this maxV
            i = -1
            v = mminV
            while True:
                if i != -1:  # not first time
                    v = mminV + 2**i

                if v >= maxV:
                    break

                i = i + 1
                inv = Inv(term <= v)
                inv_ = DInvs.mk(loc, Invs.mk([inv]))
                cexs, _ = self.symstates.check(inv_, inps=None)
                assert v not in statsd, v
                statsd[v] = inv.stat

                if loc in cexs:  # disproved
                    cexs = Traces.extract(cexs[loc], useOne=False)
                    mminV = int(max(cexs.myeval(term)))
                else:  # proved , term <= v
                    break

            mmaxV = v if v < maxV else maxV
            mlog.debug("{}: compute ub for '{}', start w/ minV {}, maxV {})"
                       .format(loc, term, mminV, mmaxV))
            boundV = self.guessCheck(loc, term, mminV, mmaxV, statsd)
            if (boundV not in statsd or statsd[boundV] != Inv.DISPROVED):
                stat = statsd[boundV] if boundV in statsd else None
                inv = Inv(term <= boundV, stat)
                mlog.debug("got {}".format(inv))
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
            if loc not in dinvs:
                dinvs[loc] = Invs()
            dinvs[loc].add(inv)
        return dinvs

    def guessCheck(self, loc, term, minV, maxV, statsd):
        assert isinstance(loc, str) and loc, loc
        assert minV <= maxV, (minV, maxV, term)
        assert isinstance(statsd, dict), statsd  # {v : proved}

        # print loc
        # print term
        # print minV, maxV

        if minV == maxV:
            return maxV
        elif maxV - minV == 1:
            if (minV in statsd and statsd[minV] == Inv.DISPROVED):
                return maxV

            inv = Inv(term <= minV)
            inv_ = DInvs.mk(loc, Invs.mk([inv]))
            cexs, _ = self.symstates.check(inv_, inps=None)

            assert minV not in statsd
            statsd[minV] = inv.stat

            if loc in cexs:
                return maxV
            else:
                return minV

        v = (maxV + minV)/2.0
        v = int(math.ceil(v))  # sage.all.ceil(v)

        inv = Inv(term <= v)
        inv_ = DInvs.mk(loc, Invs.mk([inv]))
        cexs, _ = self.symstates.check(inv_, inps=None)

        assert v not in statsd
        statsd[v] = inv.stat

        if loc in cexs:  # disproved
            cexs = Traces.extract(cexs[loc], useOne=False)
            minV = int(max(cexs.myeval(term)))
        else:
            maxV = v
        return self.guessCheck(loc, term, minV, maxV, statsd)
