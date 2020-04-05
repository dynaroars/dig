"""
Find upperbound of polynomials using binary search-CEGIR approach
"""
import math
import pdb
from time import time

import z3
import sage.all

import helpers.vcommon as CM
from helpers.miscs import Miscs
import helpers.miscs

import settings
import data.traces
import data.poly.base
import data.poly.mp
import data.inv.mp
import data.inv.oct
import cegir.base

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class CegirBinSearch(cegir.base.Cegir):
    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)

    def gen(self, traces, inps):
        assert isinstance(traces, data.traces.DTraces) and traces, traces
        assert isinstance(inps, data.traces.Inps), inps

        statss = []
        locs = traces.keys()
        termss = [self.get_terms(self.inv_decls[loc].sageExprs)
                  for loc in locs]

        mlog.debug("check upperbounds for {} terms at {} locs".format(
            sum(map(len, termss)), len(locs)))
        maxV = settings.OCT_MAX_V
        minV = -1*maxV
        refs = {loc: {self.mk_le(t, maxV): t for t in terms}
                for loc, terms in zip(locs, termss)}
        ieqs = data.inv.invs.DInvs(
            [(loc, data.inv.invs.Invs(refs[loc].keys())) for loc in refs])

        cexs, ieqs, stats = self.check(ieqs, inps=None)
        statss.extend(stats)

        if cexs:
            cexs_inps = inps.merge(cexs, self.inp_decls.names)
            if cexs_inps:
                self.get_traces(cexs_inps, traces)

        ieqs = ieqs.remove_disproved()

        tasks = [(loc, refs[loc][mp]) for loc in ieqs for mp in ieqs[loc]]
        mlog.debug("{} locs: infer upperbounds for {} terms".format(
            len(locs), len(tasks)))

        def f(tasks):
            return [(loc, self.gc(loc, term, minV, maxV, traces))
                    for loc, term in tasks]
        wrs = Miscs.run_mp('guesscheck', tasks, f)

        dinvs = data.inv.invs.DInvs()
        for loc, (inv, stats) in wrs:
            statss.extend(stats)
            if inv:
                dinvs.setdefault(loc, data.inv.invs.Invs()).add(inv)

        return dinvs, statss

    def gc(self, loc, term, minV, maxV, traces):
        assert isinstance(term, data.poly.base.Poly)
        assert minV <= maxV, (minV, maxV)
        statsd = {maxV: data.inv.base.Inv.PROVED}

        #print(self.find_max(loc, term))
        statss = []

        # start with this minV
        vs = term.eval_traces(traces[loc])
        try:
            mymaxV = int(max(v for v in vs))
            if mymaxV > maxV:
                # occurs when checking above fails
                # (e.g., cannot show term <= maxV even though it is true)
                return None, statss

            mminV = int(max(minV, mymaxV))
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
            cexs, stat, stats = self._mk_upp_and_check(loc, term, v)
            statss.extend(stats)
            assert v not in statsd, v
            statsd[v] = stat

            if loc in cexs:  # disproved
                mminV = self._get_max_from_cexs(loc, term, cexs)
                if mminV >= maxV:
                    return None, statss

            else:  # proved , term <= v
                break

        mmaxV = v if v < maxV else maxV
        mlog.debug("{}: compute ub for '{}', start with minV {}, maxV {})"
                   .format(loc, term, mminV, mmaxV))

        assert mminV <= mmaxV, (term, mminV, mmaxV)
        boundV = self.guess_check(
            loc, term, mminV, mmaxV, statsd, statss)

        if (boundV is not None and
                (boundV not in statsd or statsd[boundV] != data.inv.base.Inv.DISPROVED)):
            stat = statsd[boundV] if boundV in statsd else None
            inv = self.mk_le(term, boundV)
            inv.stat = stat
            mlog.debug("got {}".format(inv))
            return inv, statss
        else:
            return None, statss

    def guess_check(self, loc, term, minV, maxV, statsd, statss):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(statsd, dict), statsd  # {v : proved}
        assert isinstance(statss, list), statss

        if minV > maxV:
            mlog.warning("{}: (guess_check) term {} has minV {} > maxV {}".format(
                loc, term, minV, maxV))
            return None  # temp fix

        if minV == maxV:
            return maxV
        elif maxV - minV == 1:
            if (minV in statsd and statsd[minV] == data.inv.base.Inv.DISPROVED):
                return maxV

            cexs, stat, stats = self._mk_upp_and_check(loc, term, minV)
            statss.extend(stats)

            assert minV not in statsd
            statsd[minV] = stat
            ret = maxV if loc in cexs else minV
            return ret

        v = (maxV + minV)/2.0
        v = int(math.ceil(v))

        cexs, stat, stats = self._mk_upp_and_check(loc, term, v)
        statss.extend(stats)
        assert v not in statsd, (term.term, minV, maxV, v, stat, statsd[v])
        statsd[v] = stat

        if loc in cexs:  # disproved
            minV = self._get_max_from_cexs(loc, term, cexs)
        else:
            maxV = v

        return self.guess_check(loc, term, minV, maxV, statsd, statss)

    def get_terms(self, symbols):

        terms = []
        if settings.DO_IEQS:
            oct_siz = 2
            terms_ieqs = Miscs.get_terms_fixed_coefs(symbols, oct_siz)
            terms_ieqs = [data.poly.base.GeneralPoly(t) for t in terms_ieqs]
            mlog.debug("{} terms for Ieqs".format(len(terms_ieqs)))
            terms.extend(terms_ieqs)

        if settings.DO_MINMAXPLUS:
            terms_u = data.poly.mp.MP.get_terms(symbols)
            terms_u_no_octs = [(a, b) for a, b in terms_u
                               if len(b) >= 2]

            if settings.DO_IEQS:  # ignore oct invs
                terms_u = terms_u_no_octs

            def _get_terms(terms_u, is_max):
                terms_l = [(b, a) for a, b in terms_u]
                terms = terms_u + terms_l
                terms = [data.poly.mp.MP(a, b, is_max) for a, b in terms]
                return terms

            terms_max = _get_terms(terms_u, is_max=True)

            terms_min = _get_terms(terms_u_no_octs, is_max=False)
            terms_mp = terms_min + terms_max
            terms.extend(terms_mp)
            mlog.debug("{} terms for MP".format(len(terms_mp)))
            print(terms_mp)

        if settings.DO_TERM_FILTER:
            st = time()
            new_terms = self.filter_terms(
                terms, set(self.prog.inp_decls.names))
            Miscs.show_removed('term filter',
                               len(terms), len(new_terms), time() - st)
            return new_terms
        else:
            return terms

    @staticmethod
    def filter_terms(terms, inps):
        assert isinstance(inps, set) and \
            all(isinstance(s, str) for s in inps), inps

        if not inps:
            mlog.warning("Have not tested case with no inps")

        excludes = set()
        for term in terms:
            if isinstance(term, data.poly.mp.MP):
                a_symbs = list(map(str, Miscs.get_vars(term.a)))
                b_symbs = list(map(str, Miscs.get_vars(term.b)))
                inp_in_a = any(s in inps for s in a_symbs)
                inp_in_b = any(s in inps for s in b_symbs)

                if ((inp_in_a and inp_in_b) or
                        (not inp_in_a and not inp_in_b)):
                    excludes.add(term)
                    continue

                t_symbs = set(a_symbs + b_symbs)

            else:
                t_symbs = set(map(str, term.symbols))

            if len(t_symbs) <= 1:  # ok for finding bound of single input val
                continue

            if (inps.issuperset(t_symbs) or
                    all(s not in inps for s in t_symbs)):
                excludes.add(term)

        new_terms = [term for term in terms if term not in excludes]
        return new_terms

    def mk_le(self, term, v):
        inv = term.mk_le(v)
        if isinstance(term, data.poly.base.GeneralPoly):
            inv = data.inv.oct.Oct(inv)
        else:
            inv = data.inv.mp.MP(inv)
        return inv

    def _mk_upp_and_check(self, loc, term, v):
        assert isinstance(v, int), v
        inv = self.mk_le(term, v)
        inv_ = data.inv.invs.DInvs.mk(loc, data.inv.invs.Invs([inv]))
        cexs, _, stats = self.check(
            inv_, inps=None, check_mode=self.symstates.check_validity)

        return cexs, inv.stat, stats

    def _get_max_from_cexs(self, loc, term, cexs):
        mycexs = data.traces.Traces.extract(cexs[loc], useOne=False)
        return int(max(term.eval_traces(mycexs)))

    def find_max(self, loc, term):
        ss = self.symstates.ss[loc]
        ss = z3.And([ss[depth].myexpr for depth in ss])
        term = helpers.miscs.Z3.parse(str(term.poly), use_reals=False)
        opt = z3.Optimize()
        opt.add(ss)
        opt.maximize(term)
        stat = opt.check()

        v = None
        if stat == z3.sat:
            model = opt.model()
            #term = -(x+y)
            # create a dict from model, e.g., d = {x: 5, y = 10}
            # v will then be term.subs(d)
            for s in model:
                if str(s) == str(term):
                    v = model[s]
                    break

            if v is not None:
                v = int(str(v))
                print(term, v)
            else:
                print('???', term, model)
                assert False
        else:
            raise NotImplementedError("deal with this: {}".format(stat))

        return v
