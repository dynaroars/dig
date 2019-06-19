import math
import pdb

import vcommon as CM
from miscs import Miscs

import settings
from ds import Inps, Traces, DTraces
from invs import Inv, MPInv, Invs, DInvs
from cegir import Cegir

dbg = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class CegirMP(Cegir):
    def __init__(self, symstates, prog):
        super(CegirMP, self).__init__(symstates, prog)

    def gen(self, traces, inps):
        assert isinstance(traces, DTraces) and traces, traces
        assert isinstance(inps, Inps), inps

        locs = traces.keys()
        symbolss = [self.inv_decls[loc].sageExprs for loc in locs]
        termss = [MPInv.get_terms(symbols) for symbols in symbolss]

        mlog.info("check upperbounds for {} terms at {} locs".format(
            sum(map(len, termss)), len(locs)))

        maxV = settings.OCT_MAX_V
        minV = -1*maxV
        refs = {loc: {MPInv.mk_max_ieq((lh - maxV,), rh): (lh, rh)
                      for lh, rh in terms}
                for loc, terms in zip(locs, termss)}

        ieqs = DInvs([(loc, Invs(refs[loc].keys())) for loc in refs])
        myinps = None  # dummy
        cexs, ieqs = self.symstates.check(ieqs, myinps)

        if cexs:
            newInps = inps.myupdate(cexs, self.inp_decls.names)
            if newInps:
                self.get_traces(newInps, traces)

        ieqs = ieqs.remove_disproved()
        tasks = [(loc, refs[loc][ieq]) for loc in ieqs for ieq in ieqs[loc]]
        mlog.debug("{} locs: compute upperbounds for {} terms".format(
            len(locs), len(tasks)))

        def _f(loc, mp):
            assert isinstance(mp, MPInv), mp
            statsd = {maxV: Inv.PROVED}

            # start with this minV
            traces_ = [t.mydict_str for t in traces[loc]]
            vs = [mp.myeval(t) for t in traces_]
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
                cexs, stat = self.mk_upper_and_check(loc, mp, v)
                assert v not in statsd, v
                statsd[v] = stat

                if loc in cexs:  # disproved
                    mminV = self.get_max_from_cexs(loc, mp, cexs)
                else:  # proved , term <= v
                    break

            mmaxV = v if v < maxV else maxV
            mlog.debug("{}: compute ub for '{}', start w/ minV {}, maxV {})"
                       .format(loc, mp.term, mminV, mmaxV))
            boundV = self.guess_check(loc, mp, mminV, mmaxV, statsd)

            if (boundV not in statsd or statsd[boundV] != Inv.DISPROVED):
                stat = statsd[boundV] if boundV in statsd else None
                inv = mp.term_upper(boundV)
                inv.stat = stat
                mlog.debug("got {}".format(inv))
                return inv
            else:
                return None

        def f(tasks):
            return [(loc, _f(loc, MPInv.mk_max_ieq((lh,), rh)))
                    for loc, (lh, rh) in tasks]
        wrs = Miscs.run_mp_simple('guesscheck', tasks, f, doMP=settings.doMP)
        rs = [(loc, inv) for loc, inv in wrs if inv]
        dinvs = DInvs()
        for loc, inv in rs:
            dinvs.setdefault(loc, Invs()).add(inv)
        return dinvs

    def guess_check(self, loc, mp, minV, maxV, statsd):
        assert isinstance(mp, MPInv)
        assert isinstance(loc, str) and loc, loc
        assert minV <= maxV, (minV, maxV, mp.term)
        assert isinstance(statsd, dict), statsd  # {v : proved}

        if minV == maxV:
            return maxV
        elif maxV - minV == 1:
            if (minV in statsd and statsd[minV] == Inv.DISPROVED):
                return maxV

            cexs, stat = self.mk_upper_and_check(loc, mp, minV)
            assert minV not in statsd
            statsd[minV] = stat

            if loc in cexs:
                return maxV
            else:
                return minV

        v = (maxV + minV)/2.0
        v = int(math.ceil(v))

        cexs, stat = self.mk_upper_and_check(loc, mp, v)
        assert v not in statsd, (mp.term, minV, maxV, v, stat, statsd[v])
        statsd[v] = stat

        if loc in cexs:  # disproved
            minV = self.get_max_from_cexs(loc, mp, cexs)
        else:
            maxV = v

        if minV > maxV:
            dbg()
        return self.guess_check(loc, mp, minV, maxV, statsd)

    def mk_upper_and_check(self, loc, mp, v):
        inv = mp.term_upper(v)
        inv_ = DInvs.mk(loc, Invs([inv]))
        cexs, _ = self.symstates.check(inv_, inps=None)
        return cexs, inv.stat

    def get_max_from_cexs(self, loc, mp, cexs):
        mycexs = Traces.extract(cexs[loc], useOne=False)
        vals = [mp.myeval(t.mydict_str) for t in mycexs]
        maxV = int(max(vals))
        return maxV
