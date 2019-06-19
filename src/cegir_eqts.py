import pdb

import vcommon as CM
import settings
from miscs import Miscs

from cegir import Cegir
from ds import Inps, Traces, DTraces
from invs import Invs, EqtInv, DInvs


trace = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class CegirEqts(Cegir):
    def __init__(self, symstates, prog):
        super(CegirEqts, self).__init__(symstates, prog)
        self.useRandInit = False  # use symstates or random to get init inps

    def gen(self, deg, traces, inps):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces) and traces, traces
        assert isinstance(inps, Inps), inps

        # first obtain enough traces
        initrs = [self.getInitTraces(loc, deg, traces, inps, settings.EQT_RATE)
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
            newInps = inps.myupdate(newCexs, self.inp_decls.names)
            mlog.debug("{}: got {} eqts, {} new inps"
                       .format(loc, len(eqts), len(newInps)))
            if eqts:
                mlog.debug('\n'.join(map(str, eqts)))
            dinvs[loc] = Invs(eqts)

        return dinvs

    def while_rand(self, loc, template, n_eqts_needed, inps, traces):
        """
        repeatedly get more inps using random method
        """
        exprs = traces[loc].instantiate(template, n_eqts_needed)

        doRand = True
        while n_eqts_needed > len(exprs):
            newTraces = {}
            mlog.debug("{}: need more traces ({} eqts, need >= {}, inps {})"
                       .format(loc, len(exprs), n_eqts_needed, len(inps)))
            if doRand:
                rInps = self.prog.gen_rand_inps()
                mlog.debug("gen {} random inps".format(len(rInps)))
                rInps = inps.myupdate(rInps, self.inp_decls.names)
                if rInps:
                    newTraces = self.get_traces(rInps, traces)

            if loc not in newTraces:
                doRand = False

                dinvsFalse = DInvs.mk_false_invs([loc])
                cexs, _ = self.symstates.check(dinvsFalse, inps)
                # cannot find new inputs
                if loc not in cexs:
                    mlog.debug("{}: cannot find new inps (curr inps :{})"
                               .format(loc, len(inps)))
                    return

                newInps = inps.myupdate(cexs, self.inp_decls.names)
                newTraces = self.get_traces(newInps, traces)

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
                template, n_eqts_needed - len(exprs))

            for expr in newExprs:
                assert expr not in exprs
                exprs.add(expr)

        return exprs

    def while_symstates(self, loc, template, n_eqts_needed, inps, traces):
        """
        repeated get more traces using the symstates (e.g., Klee)
        """
        assert isinstance(loc, str), loc
        assert n_eqts_needed >= 1, n_eqts_needed

        exprs = traces[loc].instantiate(template, n_eqts_needed)
        while n_eqts_needed > len(exprs):
            mlog.debug("{}: need more traces ({} eqts, need >= {})"
                       .format(loc, len(exprs), n_eqts_needed))
            dinvsFalse = DInvs.mk_false_invs([loc])
            cexs, _ = self.symstates.check(dinvsFalse, inps)
            if loc not in cexs:
                mlog.error("{}: cannot generate enough traces".format(loc))
                return

            newInps = inps.myupdate(cexs, self.inp_decls.names)
            newTraces = self.get_traces(newInps, traces)
            assert newTraces[loc]
            mlog.debug("obtain {} new traces".format(len(newTraces[loc])))
            newExprs = newTraces[loc].instantiate(
                template, n_eqts_needed - len(exprs))

            for expr in newExprs:
                assert expr not in exprs
                exprs.add(expr)

        return exprs

    def getInitTraces(self, loc, deg, traces, inps, rate):
        "Initial loop to obtain (random) traces to bootstrap eqt solving"

        assert deg >= 1, deg
        assert isinstance(rate, float) and rate >= 0.1, rate

        if self.useRandInit:
            whileF, whileFName = self.while_rand, "random"
        else:
            whileF, whileFName = self.while_symstates, "symstates"
        mlog.debug("{}: gen init inps using {} (curr inps {}, traces {})"
                   .format(loc, whileFName, len(inps), len(traces)))

        terms, template, uks, n_eqts_needed = Miscs.init_terms(
            self.inv_decls[loc].names, deg, rate)
        exprs = whileF(loc, template, n_eqts_needed, inps, traces)

        # if cannot generate sufficient traces, adjust degree
        while (not exprs):
            if deg < 2:
                return  # cannot generate enough traces

            deg = deg - 1
            mlog.info("Reduce polynomial degree to {}, terms {}, uks {}"
                      .format(deg, len(terms), len(uks)))
            terms, template, uks, n_eqts_needed = Miscs.init_terms(
                self.inv_decls[loc].names, deg, rate)
            exprs = whileF(loc, template, n_eqts_needed, inps, traces)

        return template, uks, exprs

    def infer(self, loc, template, uks, exprs, dtraces, inps):
        assert isinstance(loc, str) and loc, loc
        assert Miscs.is_expr(template), template
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

            newEqts = Miscs.solve_eqts(exprs, uks, template)
            unchecks = [eqt for eqt in newEqts if eqt not in cache]

            if not unchecks:
                mlog.debug("{}: no new results -- break".format(loc))
                break

            mlog.debug('{}: {} candidates:\n{}'.format(
                loc, len(newEqts), '\n'.join(map(str, newEqts))))

            mlog.debug("{}: check {} unchecked ({} candidates)"
                       .format(loc, len(unchecks), len(newEqts)))

            dinvs = DInvs.mk(loc, Invs(map(EqtInv, unchecks)))
            cexs, dinvs = self.symstates.check(dinvs, inps=None)

            if cexs:
                newCexs.append(cexs)

            [eqts.add(inv) for inv in dinvs[loc] if not inv.is_disproved]
            [cache.add(inv.inv) for inv in dinvs[loc]
             if inv.stat is not None]

            if loc not in cexs:
                mlog.debug("{}: no disproved candidates -- break".format(loc))
                break

            cexs = Traces.extract(cexs[loc])
            cexs = cexs.padZeros(set(self.inv_decls[loc].names))
            exprs_ = cexs.instantiate(template, None)
            mlog.debug("{}: {} new cex exprs".format(loc, len(exprs_)))
            exprs.extend(exprs_)

        return eqts, newCexs
