"""
CEGIR alg for inferring equalities
"""
import pdb
import sympy

import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs, MP

from data.traces import Inps, Traces, DTraces
from data.inv.invs import Invs, DInvs
import data.inv.eqt
import infer.base

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Infer(infer.base.Infer):
    def __init__(self, symstates, prog):
        super().__init__(symstates, prog)
        self.use_rand_init = False  # use symstates or random to get init inps

    def gen(self, deg, traces, inps):
        assert deg >= 1, deg
        assert isinstance(traces, DTraces) and traces, traces
        assert isinstance(inps, Inps), inps

        locs = traces.keys()
        # first obtain enough traces
        tasks = [
            (loc, self._get_init_traces(loc, deg, traces, inps, settings.EQT_RATE))
            for loc in locs
        ]
        tasks = [(loc, tcs) for loc, tcs in tasks if tcs]

        # then solve/prove in parallel
        def f(tasks):
            return [
                (loc, self._infer(loc, template, uks, exprs, traces, inps))
                for loc, (template, uks, exprs) in tasks
            ]

        wrs = MP.run_mp("find eqts", tasks, f, settings.DO_MP)

        # put results together
        dinvs = DInvs()
        for loc, (eqts, cexs) in wrs:
            new_inps = inps.merge(cexs, self.inp_decls.names)
            mlog.debug(
                f"{loc}: got {len(eqts)} eqts, {len(new_inps)} new inps")
            if eqts:
                mlog.debug("\n".join(map(str, eqts)))

            dinvs[loc] = Invs(eqts)

        return dinvs

    # PRIVATE
    def add_exprs(cls, template, n_eqts_needed, traces, exprs):
        assert traces
        mlog.debug(f"got {len(traces)} new traces")
        new_exprs = traces.instantiate(template, n_eqts_needed - len(exprs))
        for expr in new_exprs:
            assert expr not in exprs
            exprs.add(expr)

    def _while_rand(self, loc, ts, uks, n_eqts_needed, inps, traces):
        """
        repeatedly get more inps using random method
        """
        template = sum(t*u for t, u in zip(ts, uks))
        exprs = traces[loc].instantiate(template, n_eqts_needed)

        doRand = True
        while n_eqts_needed > len(exprs):
            new_traces = {}
            mlog.debug(
                f"{loc}: need more traces ({len(exprs)} eqts, "
                f"need >= {n_eqts_needed}, inps {len(inps)})"
            )
            if doRand:
                rInps = self.prog.gen_rand_inps(n_eqts_needed - len(exprs))
                mlog.debug(f"gen {len(rInps)} random inps")
                rInps = inps.merge(rInps, self.inp_decls.names)
                if rInps:
                    new_traces = self.get_traces(rInps, traces)

            if loc not in new_traces:
                doRand = False

                dinvsFalse = DInvs.mk_false_invs([loc])
                cexs, _ = self.symstates.check(dinvsFalse, inps)

                # cannot find new inputs
                if loc not in cexs:
                    mlog.debug(
                        f"{loc}: cannot find new inps ({len(inps)} curr inps)")
                    return

                new_inps = inps.merge(cexs, self.inp_decls.names)
                new_traces = self.get_traces(new_inps, traces)

                # cannot find new traces (new inps do not produce new traces)
                if loc not in new_traces:
                    mlog.debug(
                        f"{loc}: cannot find new traces "
                        f"(new inps {len(new_inps)}, "
                        f"curr traces {len(traces[loc]) if loc in traces else 0})"
                    )
                    return

            self.add_exprs(template, n_eqts_needed, new_traces[loc], exprs)

        return exprs

    def _while_symstates(self, loc, template, n_eqts_needed, inps, traces):
        """
        repeated get more traces using the symstates (e.g., Klee)
        """
        assert isinstance(loc, str), loc
        assert n_eqts_needed >= 1, n_eqts_needed

        exprs = traces[loc].instantiate(template, n_eqts_needed)
        while n_eqts_needed > len(exprs):
            mlog.debug(
                f"{loc}: need more traces ({len(exprs)} eqts, need >= {n_eqts_needed})"
            )
            dinvsFalse = DInvs.mk_false_invs([loc])
            cexs, _, _ = self.symstates.check(dinvsFalse, inps)

            if loc not in cexs:
                mlog.error(f"{loc}: cannot generate enough traces")
                return

            new_inps = inps.merge(cexs, self.inp_decls.names)
            new_traces = self.get_traces(new_inps, traces)

            self.add_exprs(template, n_eqts_needed, new_traces[loc], exprs)

        return exprs

    def _get_init_traces(self, loc, deg, traces, inps, rate):
        "Initial loop to obtain (random) traces to bootstrap eqt solving"

        assert deg >= 1, deg
        assert isinstance(rate, float) and rate >= 0.1, rate

        if self.use_rand_init:
            whileF, whileFName = self._while_rand, "random"
        else:
            whileF, whileFName = self._while_symstates, "symstates"
        mlog.debug(
            f"{loc}: gen init inps using {whileFName} "
            f"(curr inps {len(inps)}, traces {len(traces)})"
        )
        ts, uks, n_eqts_needed = Miscs.init_terms(
            self.inv_decls[loc].names, deg, rate)

        exprs = whileF(loc, ts, uks, n_eqts_needed, inps, traces)

        # if cannot generate sufficient traces, adjust degree
        while not exprs:
            if deg < 2:
                return  # cannot generate enough traces

            deg = deg - 1
            mlog.info(
                f"Reduce polynomial degree to {deg}, terms {len(ts)}, uks {len(uks)}"
            )
            ts, uks, n_eqts_needed = Miscs.init_terms(
                self.inv_decls[loc].names, deg, rate
            )
            exprs = whileF(loc, ts, uks, n_eqts_needed, inps, traces)

        return ts, uks, exprs

    def _infer(self, loc, ts, uks, exprs, dtraces, inps):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(ts, list), ts
        assert isinstance(uks, list), uks
        assert len(ts) == len(uks), (ts, uks)
        assert isinstance(exprs, set) and exprs, exprs
        assert isinstance(dtraces, DTraces) and dtraces, dtraces
        assert isinstance(inps, Inps) and inps, inps

        template = sum(t*u for t, u in zip(ts, uks))
        cache = set()
        eqts = set()  # results
        exprs = list(exprs)

        new_cexs = []
        curIter = 0

        while True:
            curIter += 1
            mlog.debug(f"{loc}, iter {curIter} infer using {len(exprs)} exprs")
            new_eqts = Miscs.solve_eqts(exprs, ts, uks)
            unchecks = [eqt for eqt in new_eqts if eqt not in cache]

            if not unchecks:
                mlog.debug(f"{loc}: no new results -- break")
                break

            mlog.debug(
                "{}: {} candidates:\n{}".format(
                    loc, len(new_eqts), "\n".join(map(str, new_eqts))
                )
            )

            mlog.debug(
                f"{loc}: check {len(unchecks)} unchecked ({len(new_eqts)} candidates)"
            )

            dinvs = DInvs.mk(loc, Invs(list(map(data.inv.eqt.Eqt, unchecks))))
            cexs, dinvs = self.check(dinvs, None)
            if cexs:
                new_cexs.append(cexs)

            [eqts.add(inv) for inv in dinvs[loc] if not inv.is_disproved]
            [cache.add(inv.inv) for inv in dinvs[loc] if inv.stat is not None]

            if loc not in cexs:
                mlog.debug(f"{loc}: no disproved candidates -- break")
                break

            cexs = Traces.extract(cexs[loc])
            cexs = cexs.padzeros(set(self.inv_decls[loc].names))
            exprs_ = cexs.instantiate(template, None)
            mlog.debug(f"{loc}: {len(exprs_)} new cex exprs")
            exprs.extend(exprs_)

        return eqts, new_cexs

    @classmethod
    def gen_from_traces(cls, deg, traces, symbols):
        assert isinstance(traces, Traces), traces

        mydeg = deg
        eqts = []
        while not eqts and mydeg:
            ts, uks, n_eqts_needed = Miscs.init_terms(
                symbols.names, mydeg, settings.EQT_RATE
            )

            if len(traces) < len(uks):
                mydeg = mydeg - 1
                mlog.warning(
                    f"{len(traces)} traces < {len(uks)} uks, reducing to deg {mydeg}")
                continue

            template = sum(t*u for t, u in zip(ts, uks))
            exprs = list(traces.instantiate(template, n_eqts_needed))
            if len(exprs) < len(uks):
                mydeg = mydeg - 1
                mlog.warning(
                    f"{len(exprs)} exprs < {len(uks)} uks, reducing deg to {mydeg}")
                continue

            eqts = Miscs.solve_eqts(exprs, ts, uks)
            if not eqts:
                mydeg = mydeg - 1
                mlog.warning(f"NO EQTS RESULTS, reducing deg to {mydeg}")

        return [data.inv.eqt.Eqt(eqt)for eqt in eqts]
