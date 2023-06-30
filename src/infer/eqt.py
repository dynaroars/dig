"""
CEGIR alg for inferring equalities
"""
import pdb
import sympy
from beartype import beartype

import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs, MP

import data.traces
import infer.inv
import infer.infer

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class Eqt(infer.inv.Inv):

    @beartype
    def __init__(self, eqt:sympy.Equality, stat=None)->None:
        assert eqt.rhs == 0, eqt

        super().__init__(eqt, stat)

    @beartype
    @property
    def mystr(self) -> str:
        return f"{self.inv.lhs} == {self.inv.rhs}"


class Infer(infer.infer._CEGIR):

    @beartype
    @classmethod
    def gen_from_traces(cls, deg:int,
                        traces:data.traces.Traces, symbols) -> list[Eqt]:

        mydeg = deg
        eqts = []
        while not eqts and mydeg:
            ts, uks, n_eqts_needed = Miscs.init_terms(
                symbols.names, mydeg, settings.EQT_RATE
            )

            if len(traces) < len(uks) and False:
                mydeg = mydeg - 1
                mlog.warning(
                    f"{len(traces)} traces < {len(uks)} uks, reducing to deg {mydeg}")
                continue

            template = sum(t*u for t, u in zip(ts, uks))
            exprs = list(traces.instantiate(template, n_eqts_needed))
            if len(exprs) < len(uks) and False:
                mydeg = mydeg - 1
                mlog.warning(
                    f"{len(exprs)} exprs < {len(uks)} uks, reducing deg to {mydeg}")
                continue

            eqts = Miscs.solve_eqts(exprs, ts, uks)
            if not eqts:
                mydeg = mydeg - 1
                mlog.warning(f"NO EQTS RESULTS, reducing deg to {mydeg}")

        return [Eqt(eqt)for eqt in eqts]

    @beartype
    def gen(self, deg:int) -> tuple[infer.inv.DInvs, data.traces.DTraces] :
        assert deg >= 1, deg

        locs = self.prog.locs
        inps = data.traces.Inps()
        dtraces = data.traces.DTraces.mk(locs)

        # first obtain enough traces
        tasks = [
            (loc, self._get_init_traces(loc, deg, dtraces, inps, settings.EQT_RATE))
            for loc in locs
        ]
        tasks = [(loc, tcs) for loc, tcs in tasks if tcs]

        # then solve/prove in parallel
        def f(tasks):
            return [
                (loc, self._infer(loc, template, uks, exprs))
                for loc, (template, uks, exprs) in tasks
            ]

        wrs = MP.run_mp("find eqts", tasks, f, settings.DO_MP)

        # put results together
        dinvs = infer.inv.DInvs()
        for loc, eqts in wrs:
            mlog.debug(f"{loc}: got {len(eqts)} eqts")
            if eqts:
                mlog.debug("\n".join(map(str, eqts)))

            dinvs[loc] = infer.inv.Invs(eqts)

        return dinvs, dtraces

    # PRIVATE
    
    @beartype
    @classmethod
    def _add_exprs(cls, template, 
                   n_eqts_needed: int, traces: data.traces.Traces, exprs) -> None:
    
        mlog.debug(f"got {len(traces)} new traces")
        new_exprs = traces.instantiate(template, n_eqts_needed - len(exprs))
        for expr in new_exprs:
            assert expr not in exprs
            exprs.add(expr)
    
    @beartype
    def _while(self, loc: str, 
               ts: list[int | sympy.core.symbol.Symbol|sympy.core.power.Pow | sympy.core.mul.Mul], 
               uks: list[sympy.core.symbol.Symbol], 
               n_eqts_needed: int, inps:data.traces.Inps, 
               traces: data.traces.DTraces):
        """
        repeatedly get more inps using random method
        """
        template = sum(t*u for t, u in zip(ts, uks))
        exprs = traces[loc].instantiate(template, n_eqts_needed)

        do_rand = True
        while n_eqts_needed > len(exprs):
            new_traces = {}
            mlog.debug(
                f"{loc}: need more traces ({len(exprs)} eqts, "
                f"need >= {n_eqts_needed}, inps {len(inps)})"
            )
            if do_rand:
                r_inps = self.prog.gen_rand_inps(n_eqts_needed - len(exprs))
                mlog.debug(f"gen {len(r_inps)} random inps")
                r_inps = inps.merge(r_inps, self.inp_decls.names)
                if r_inps:
                    new_traces = self.get_traces(r_inps, traces)

            if loc not in new_traces:
                do_rand = False

                dinvsFalse = infer.inv.DInvs.mk_false_invs([loc])
                cexs, _ = self.symstates.check(dinvsFalse, inps)

                # cannot find new inputs
                if loc not in cexs:
                    mlog.debug(
                        f"{loc}: cannot find new inps (currently has {len(inps)} inps)")
                    return

                new_inps = inps.merge(cexs, self.inp_decls.names)
                new_traces = self.get_traces(new_inps, traces)

                # cannot find new traces (new inps do not produce new traces)
                if loc not in new_traces:
                    mlog.debug(
                        f"{loc}: cannot find new traces (need {n_eqts_needed}) "
                        f"(new inps {len(new_inps)}, "
                        f"curr traces {len(traces[loc]) if loc in traces else 0})"
                    )
                    return

            self._add_exprs(template, n_eqts_needed, new_traces[loc], exprs)

        return exprs

    @beartype
    def _get_init_traces(self, loc: str, deg: int,
                         dtraces: data.traces.DTraces,
                         inps: data.traces.Inps, rate: float) -> tuple[list, list[sympy.core.symbol.Symbol], set] | None:
        """
        Initial loop to obtain (random) traces to bootstrap eqt solving
        """

        assert deg >= 1, deg
        assert rate >= 0.1, rate

        mlog.debug(
            f"{loc}: generate random initial inps "
            f"(curr inps {len(inps)}, traces {dtraces[loc]})"
        )

        ts, uks, n_eqts_needed = Miscs.init_terms(
            self.inv_decls[loc].names, deg, rate)

        exprs = self._while(loc, ts, uks, n_eqts_needed, inps, dtraces)

        # if cannot generate sufficient traces, adjust degree
        while not exprs:
            if deg <= 1:
                mlog.warn(f"deg {deg}, unable to generate sufficient traces")
                return  # cannot generate enough traces

            deg = deg - 1
            mlog.info(
                f"Reduce polynomial degree to {deg}, terms {len(ts)}, uks {len(uks)}"
            )
            ts, uks, n_eqts_needed = Miscs.init_terms(
                self.inv_decls[loc].names, deg, rate
            )
            exprs = self._while(loc, ts, uks, n_eqts_needed, inps, dtraces)
                
        return ts, uks, exprs

    @beartype
    def _infer(self, loc: str, 
               ts: list[int | sympy.core.symbol.Symbol | sympy.core.power.Pow | sympy.core.mul.Mul], 
               uks: list[sympy.core.symbol.Symbol], 
               exprs: set[sympy.Expr]) -> set:
        
        assert loc, loc
        assert len(ts) == len(uks), (ts, uks)
        assert exprs, exprs

        template = sum(t*u for t, u in zip(ts, uks))
        cache = set()
        eqts = set()  # results
        exprs = list(exprs)

        curIter = 0

        while True:
            curIter += 1
            mlog.debug(f"{loc}, iter {curIter} infer using {len(exprs)} exprs")
            new_eqts = Miscs.solve_eqts(exprs, ts, uks)
            unchecks = [eqt for eqt in new_eqts if eqt not in cache]

            if not unchecks:
                mlog.debug(f"{loc}: no new results -- break")
                break

            new_eqts = infer.inv.Invs(list(map(Eqt, unchecks)))

            mlog.debug(
                f"{loc}: {len(new_eqts)} candidates: {'; '.join(map(str, new_eqts))}")

            mlog.debug(
                f"{loc}: check {len(unchecks)} unchecked ({len(new_eqts)} candidates)"
            )

            dinvs = infer.inv.DInvs.mk(loc, new_eqts)
            cexs, dinvs = self.check(dinvs, None)

            [eqts.add(inv) for inv in dinvs[loc] if not inv.is_disproved]
            [cache.add(inv.inv) for inv in dinvs[loc] if inv.stat is not None]

            if loc not in cexs:
                mlog.debug(f"{loc}: no disproved candidates -- break")
                break

            cexs = data.traces.Traces.extract(cexs[loc])
            cexs = cexs.padzeros(set(self.inv_decls[loc].names))
            exprs_ = cexs.instantiate(template, None)
            mlog.debug(f"{loc}: {len(exprs_)} new cex exprs")
            exprs.extend(exprs_)

        return eqts
