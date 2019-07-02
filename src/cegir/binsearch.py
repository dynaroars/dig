"""
Find upperbound of polynomials using binary search-CEGIR approach
"""
import math
import pdb

import helpers.vcommon as CM
from helpers.miscs import Miscs

import settings
from data.traces import Inps, Traces, DTraces
import data.poly.base
import data.poly.mp
from data.inv.base import Inv, Invs, DInvs
import data.inv.mp
import data.inv.ieq
from cegir.base import Cegir

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class CegirBinSearch(Cegir):
    def __init__(self, symstates, prog):
        super(CegirBinSearch, self).__init__(symstates, prog)

    def gen(self, traces, inps):
        assert isinstance(traces, DTraces) and traces, traces
        assert isinstance(inps, Inps), inps

        locs = traces.keys()
        termss = [self.get_terms(self.inv_decls[loc].sageExprs)
                  for loc in locs]

        mlog.debug("check upperbounds for {} terms at {} locs".format(
            sum(map(len, termss)), len(locs)))
        maxV = settings.OCT_MAX_V
        minV = -1*maxV
        refs = {loc: {self.mk_lt(t, maxV): t for t in terms}
                for loc, terms in zip(locs, termss)}
        ieqs = DInvs([(loc, Invs(refs[loc].keys())) for loc in refs])

        cexs, ieqs = self.symstates.check(ieqs, inps=None)
        if cexs:
            cexs_inps = inps.myupdate(cexs, self.inp_decls.names)
            if cexs_inps:
                self.get_traces(cexs_inps, traces)

        ieqs = ieqs.remove_disproved()

        tasks = [(loc, refs[loc][mp]) for loc in ieqs for mp in ieqs[loc]]
        mlog.debug("{} locs: infer upperbounds for {} terms".format(
            len(locs), len(tasks)))

        def f(tasks):
            return [(loc,
                     self.gc(loc, term, minV, maxV, traces))
                    for loc, term in tasks]
        wrs = Miscs.run_mp('guesscheck', tasks, f)
        rs = [(loc, inv) for loc, inv in wrs if inv]
        dinvs = DInvs()
        for loc, inv in rs:
            dinvs.setdefault(loc, Invs()).add(inv)
        return dinvs

    def gc(self, loc, term, minV, maxV, traces):
        assert isinstance(term, data.poly.base.Poly)
        statsd = {maxV: Inv.PROVED}

        # start with this minV
        vs = term.eval_traces(traces[loc])
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
            cexs, stat = self._mk_upp_and_check(loc, term, v)
            assert v not in statsd, v
            statsd[v] = stat

            if loc in cexs:  # disproved
                mminV = self._get_max_from_cexs(loc, term, cexs)
            else:  # proved , term <= v
                break

        mmaxV = v if v < maxV else maxV
        mlog.debug("{}: compute ub for '{}', start w/ minV {}, maxV {})"
                   .format(loc, term, mminV, mmaxV))
        boundV = self.guess_check(loc, term, mminV, mmaxV, statsd)

        if (boundV not in statsd or statsd[boundV] != Inv.DISPROVED):
            stat = statsd[boundV] if boundV in statsd else None
            inv = self.mk_lt(term, boundV)
            inv.stat = stat
            mlog.debug("got {}".format(inv))
            return inv
        else:
            return None

    def guess_check(self, loc, term, minV, maxV, statsd):
        assert isinstance(loc, str) and loc, loc
        assert minV <= maxV, (minV, maxV, term)
        assert isinstance(statsd, dict), statsd  # {v : proved}

        if minV == maxV:
            return maxV
        elif maxV - minV == 1:
            if (minV in statsd and statsd[minV] == Inv.DISPROVED):
                return maxV

            cexs, stat = self._mk_upp_and_check(loc, term, minV)
            assert minV not in statsd
            statsd[minV] = stat

            return maxV if loc in cexs else minV

        v = (maxV + minV)/2.0
        v = int(math.ceil(v))

        cexs, stat = self._mk_upp_and_check(loc, term, v)
        assert v not in statsd, (term.term, minV, maxV, v, stat, statsd[v])
        statsd[v] = stat

        if loc in cexs:  # disproved
            minV = self._get_max_from_cexs(loc, term, cexs)
        else:
            maxV = v

        if minV > maxV:
            mlog.warn("{}, {}, minV {} > maxV {}".format(
                loc, term, minV, maxV))

        return self.guess_check(loc, term, minV, maxV, statsd)

    def get_terms(self, symbols):
        terms = []

        def _get_terms(terms_u, is_max):
            terms_l = [(b, a) for a, b in terms_u]
            terms = terms_u + terms_l
            terms = [data.poly.mp.MP(a, b, is_max) for a, b in terms]
            return terms

        if settings.DO_IEQS:
            oct_siz = 2
            terms_ieqs = Miscs.get_terms_fixed_coefs(symbols, oct_siz)
            terms_ieqs = [data.poly.base.GeneralPoly(t) for t in terms_ieqs]
            terms.extend(terms_ieqs)

        if settings.DO_MINMAXPLUS:
            terms_u = data.poly.mp.MP.get_terms(symbols)
            terms_u_no_octs = [(a, b) for a, b in terms_u
                               if len(b) >= 2]

            if settings.DO_IEQS:  # ignore oct invs
                terms_u = terms_u_no_octs

            terms_max = _get_terms(terms_u, is_max=True)

            # BUG when include this with CohenDiv
            terms_min = _get_terms(terms_u_no_octs, is_max=False)
            terms.extend(terms_max + terms_min)

        return terms

    def mk_lt(self, term, v):
        inv = term.mk_lt(v)
        if isinstance(term, data.poly.base.GeneralPoly):
            inv = data.inv.ieq.IeqInv(inv)
        else:
            inv = data.inv.mp.MP(inv)
        return inv

    def _mk_upp_and_check(self, loc, term, v):
        inv = self.mk_lt(term, v)
        inv_ = DInvs.mk(loc, Invs([inv]))
        cexs, _ = self.symstates.check(inv_, inps=None)
        return cexs, inv.stat

    def _get_max_from_cexs(self, loc, term, cexs):
        mycexs = Traces.extract(cexs[loc], useOne=False)
        return int(max(term.eval_traces(mycexs)))
