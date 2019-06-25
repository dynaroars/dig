import math
import pdb

import helpers.vcommon as CM
from helpers.miscs import Miscs

import settings
from data.traces import Inps, Traces, DTraces
from data.invs import Inv, Invs, DInvs
from data.mps import MPInv
from cegir.base import Cegir

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
        termss_u = [MPInv.get_terms(symbols) for symbols in symbolss]
        termss_l = [[(b, a) for a, b in terms] for terms in termss_u]
        termss = [ts_u + ts_l for ts_u, ts_l in zip(termss_u, termss_l)]

        mlog.debug("check upperbounds for {} terms at {} locs".format(
            sum(map(len, termss)), len(locs)))
        maxV = settings.OCT_MAX_V
        minV = -1*maxV
        refs = {loc: {MPInv.mk_max_ieq(a, b).mk_upper(maxV): (a, b)
                      for a, b in terms}
                for loc, terms in zip(locs, termss)}

        mps = DInvs([(loc, Invs(refs[loc].keys())) for loc in refs])

        cexs, mps = self.symstates.check(mps, inps=None)
        if cexs:
            cexs_inps = inps.myupdate(cexs, self.inp_decls.names)
            if cexs_inps:
                self.get_traces(cexs_inps, traces)

        mps = mps.remove_disproved()

        tasks = [(loc, refs[loc][mp]) for loc in mps for mp in mps[loc]]
        mlog.debug("{} locs: infer upperbounds for {} terms".format(
            len(locs), len(tasks)))

        def f(tasks):
            return [(loc,
                     self.gc(loc, MPInv.mk_max_ieq(a, b),
                             minV, maxV, traces))
                    for loc, (a, b) in tasks]
        wrs = Miscs.run_mp('guesscheck', tasks, f)
        rs = [(loc, inv) for loc, inv in wrs if inv]
        dinvs = DInvs()
        for loc, inv in rs:
            dinvs.setdefault(loc, Invs()).add(inv)
        return dinvs

    def gc(self, loc, mp, minV, maxV, traces):
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
            cexs, stat = self._mk_upp_and_check(loc, mp, v)
            assert v not in statsd, v
            statsd[v] = stat

            if loc in cexs:  # disproved
                mminV = self._get_max_from_cexs(loc, mp, cexs)
            else:  # proved , term <= v
                break

        mmaxV = v if v < maxV else maxV
        mlog.debug("{}: compute ub for '{}', start w/ minV {}, maxV {})"
                   .format(loc, mp.term, mminV, mmaxV))
        boundV = self.guess_check(loc, mp, mminV, mmaxV, statsd)

        if (boundV not in statsd or statsd[boundV] != Inv.DISPROVED):
            stat = statsd[boundV] if boundV in statsd else None
            inv = mp.mk_upper(boundV)
            inv.stat = stat
            mlog.debug("got {}".format(inv))
            return inv
        else:
            return None

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

            cexs, stat = self._mk_upp_and_check(loc, mp, minV)
            assert minV not in statsd
            statsd[minV] = stat

            return maxV if loc in cexs else minV

        v = (maxV + minV)/2.0
        v = int(math.ceil(v))

        cexs, stat = self._mk_upp_and_check(loc, mp, v)
        assert v not in statsd, (mp.term, minV, maxV, v, stat, statsd[v])
        statsd[v] = stat

        if loc in cexs:  # disproved
            minV = self._get_max_from_cexs(loc, mp, cexs)
        else:
            maxV = v

        if minV > maxV:
            mlog.warn("{}, {}, minV {} > maxV {}".format(
                loc, mp.term, minV, maxV))

        return self.guess_check(loc, mp, minV, maxV, statsd)

    def _mk_upp_and_check(self, loc, mp, v):
        inv = mp.mk_upper(v)
        inv_ = DInvs.mk(loc, Invs([inv]))
        cexs, _ = self.symstates.check(inv_, inps=None)
        return cexs, inv.stat

    def _get_max_from_cexs(self, loc, mp, cexs):
        mycexs = Traces.extract(cexs[loc], useOne=False)
        vals = [mp.myeval(t.mydict_str) for t in mycexs]
        maxV = int(max(vals))
        return maxV
