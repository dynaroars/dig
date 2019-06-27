"""
CEGIR algorithm
"""
import abc
import math
import pdb

import helpers.vcommon as CM
from helpers.miscs import Miscs

import settings
from data.traces import Inps, Traces, DTraces
from data.invs import Inv, Invs, DInvs
from data.mps import MPTerm, MPInv
from data.ieqs import IeqInv
from cegir.base import Cegir

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class CegirUpperBinSearch(Cegir):
    __metaclass__ = abc.ABCMeta

    def __init__(self, symstates, prog):
        super(CegirUpperBinSearch, self).__init__(symstates, prog)

    def gen(self, traces, inps):
        assert isinstance(traces, DTraces) and traces, traces
        assert isinstance(inps, Inps), inps

        locs = traces.keys()
        symbolss = [self.inv_decls[loc].sageExprs for loc in locs]
        termss = self.get_termss(symbolss)

        mlog.debug("check upperbounds for {} terms at {} locs".format(
            sum(map(len, termss)), len(locs)))
        maxV = settings.OCT_MAX_V
        minV = -1*maxV
        refs = {loc: {self.mk_upper(self.to_term(t), maxV): t for t in terms}
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
                     self.gc(loc, self.to_term(term), minV, maxV, traces))
                    for loc, term in tasks]
        wrs = Miscs.run_mp('guesscheck', tasks, f)
        rs = [(loc, inv) for loc, inv in wrs if inv]
        dinvs = DInvs()
        for loc, inv in rs:
            dinvs.setdefault(loc, Invs()).add(inv)
        return dinvs

    def gc(self, loc, term, minV, maxV, traces):
        statsd = {maxV: Inv.PROVED}

        # start with this minV
        vs = self.eval_traces(term, traces[loc])
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
            inv = self.mk_upper(term, boundV)
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

    @abc.abstractmethod
    def _mk_upp_and_check(self, loc, term, v):
        pass

    def _get_max_from_cexs(self, loc, term, cexs):
        mycexs = Traces.extract(cexs[loc], useOne=False)
        return int(max(self.eval_traces(term, mycexs)))

    @abc.abstractmethod
    def get_termss(self, symbolss):
        pass

    @abc.abstractmethod
    def eval_traces(self, term, traces):
        pass

    def to_term(self, term):
        return term

    @abc.abstractmethod
    def mk_upper(self, term, v):
        pass


class CegirIeqs(CegirUpperBinSearch):
    def get_termss(self, symbolss):
        oct_siz = 2
        termss = [Miscs.get_terms_fixed_coefs(symbols, oct_siz)
                  for symbols in symbolss]
        return termss

    def eval_traces(self, term, traces):
        return traces.myeval(term)

    def _mk_upp_and_check(self, loc, term, v):
        inv = self.mk_upper(term, v)
        inv_ = DInvs.mk(loc, Invs([inv]))
        cexs, _ = self.symstates.check(inv_, inps=None)
        return cexs, inv.stat

    def mk_upper(self, term, v):
        return IeqInv(term <= v)


class CegirMP(CegirUpperBinSearch):
    def get_termss(self, symbolss):
        termss_u = [MPTerm.get_terms(symbols) for symbols in symbolss]
        termss_l = [[(b, a) for a, b in terms] for terms in termss_u]
        termss = [ts_u + ts_l for ts_u, ts_l in zip(termss_u, termss_l)]
        return termss

    def to_term(self, term):
        assert isinstance(term, tuple) and len(term) == 2, term

        return MPTerm.mk_max(term[0], term[1])

    def eval_traces(self, term, traces):
        vs = [term.myeval(t.mydict_str) for t in traces]
        return vs

    def _mk_upp_and_check(self, loc, term, v):
        inv = self.mk_upper(term, v)
        inv_ = DInvs.mk(loc, Invs([inv]))
        cexs, _ = self.symstates.check(inv_, inps=None)
        return cexs, inv.stat

    def mk_upper(self, term, v):
        term_u = term.mk_upper(v)
        return MPInv(term_u)
        # return term.mk_upper(v)
