"""
Analyze Dig's results
"""
from dataclasses import dataclass
import random
from collections import defaultdict
from pathlib import Path
from statistics import median_low
from typing import Any, ClassVar

import helpers.vcommon as CM
import infer.inv
import settings
from helpers.miscs import Miscs


mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


@dataclass(slots=True)
class Result:
    resultfile: ClassVar[str] = 'result'
    filename: Any
    seed: float
    dinvs: Any
    dtraces: Any
    time_d: dict

    def __post_init__(self):
        assert isinstance(self.time_d, dict) and self.time_d, self.time_d

    def save(self, todir):
        assert todir.is_dir(), todir

        CM.vsave(todir / self.resultfile, self)

    @classmethod
    def load(cls, fromdir):
        assert isinstance(fromdir, Path) and fromdir.is_dir(), fromdir

        return CM.vload(fromdir / cls.resultfile)


class AResult(Result):
    def __init__(self, result):
        super().__init__(result.filename, result.seed, result.dinvs,
                         result.dtraces, result.time_d)

    def analyze(self):
        self.V, self.D, self.T, self.NL = self.analyze_dinvs(self.dinvs)

    @classmethod
    def analyze_dinvs(cls, dinvs):
        """
        Get max vars, terms, deg from invs
        """
        vss = []
        maxdegs = []
        ntermss = []

        for inv in dinvs.invs:
            vs, maxdeg, nterms = cls.analyze_inv(inv)
            vss.append(vs)
            maxdegs.append(maxdeg)
            ntermss.append(nterms)

            # print(inv, vs, maxdeg, nterms)
        vss = {str(v) for vs in vss for v in vs}
        nvs = len(vss)
        maxdeg = max(maxdegs)
        nterms = max(ntermss)

        nnonlinears = len([d for d in maxdegs if d >= 2])

        return nvs, maxdeg, nterms, nnonlinears

    @classmethod
    def analyze_inv(cls, inv):
        """
        return the # of variables, max deg, and number of terms
        """
        import infer.mp
        import infer.congruence

        match inv:
            case infer.mp.MMP():
                vs = inv.term.symbols
                maxdeg = 1
                nterms = 2
            case infer.congruence.Congruence():
                vs = inv.inv.a.free_symbols
                maxdeg = Miscs.get_max_deg(inv.inv.a)
                nterms = len(inv.inv.a.args) or 1
            case infer.inv.FalseInv():
                vs = set()
                maxdeg = 0
                nterms = 0
            case _ if getattr(inv, "inv", None) == 0:
                vs = set()
                maxdeg = 0
                nterms = 0
            case _:
                p = getattr(inv, "inv", inv)
                if hasattr(p, "is_Relational") and p.is_Relational:
                    vs = p.free_symbols
                    maxdeg = Miscs.get_max_deg(p.lhs)
                    nterms = len(p.lhs.args) or 1
                else:
                    vs = getattr(p, "free_symbols", set())
                    maxdeg = 1
                    nterms = len(getattr(p, "args", [])) or 1

        return vs, maxdeg, nterms


class Results:
    def __init__(self, prog, results):
        assert isinstance(prog, str), prog
        assert isinstance(results, list) and results, results
        assert all(isinstance(r, AResult) for r in results), results

        self.prog = prog
        self.results = results

    def start(self, f):
        rs = self.results
        for r in rs:
            r.analyze()

        nruns = len(rs)
        nlocs = f(len(r.dinvs) for r in rs)
        V = f(r.V for r in rs)
        T = f(r.T for r in rs)
        D = f(r.D for r in rs)
        NL = f(r.NL for r in rs)

        invtypss = [r.dinvs.typ_ctr for r in rs]
        invtypss_str, inv_counts = self.analyze_dicts(invtypss, f, 'invs')

        time_d = defaultdict(list)
        for r in rs:
            for t in r.time_d:
                time_d[t].append(r.time_d[t])
        time_s = ', '.join(f"{t} {f(time_d[t]):.1f}s" for t in time_d)

        print(f"* prog {self.prog} locs {nlocs}; "
              f"{invtypss_str} V {V} T {T} D {D}; NL {NL} ({D}) ;")

        print(f"-> time {time_s}")

        if nruns > 1:
            print(f"runs {nruns}")
        elif nruns == 1:
            print(f"rand seed {rs[0].seed}, "
                  f"test {random.randint(0, 100)}")
            # print(rs[0].dinvs.__str__(print_stat=False))

        return {
            "prog": self.prog,
            "nruns": nruns,
            "locs": nlocs,
            "V": V,
            "T": T,
            "D": D,
            "NL": NL,
            "inv_counts": inv_counts,
            "times": {t: f(time_d[t]) for t in time_d},
            "total_time": f(time_d["total"]) if "total" in time_d else 0.0,
        }

    @classmethod
    def analyze_dicts(cls, ds, f, label):
        ks = set(k for d in ds for k in d)
        dd = defaultdict(list)
        for d in ds:
            for k in ks:
                try:
                    dd[k].append(d[k])
                except KeyError:
                    dd[k].append(0)

        assert all(len(dd[k]) == len(ds) for k in dd), dd

        s = []
        sizs = []
        computed = {}

        for k in sorted(dd):
            t = f(dd[k])
            computed[k] = t
            if isinstance(k, tuple):
                assert len(k) == 2
                from_, to_ = k
                k_str = f"{from_}->{to_}"
            else:
                k_str = str(k)
            s.append((k, k_str, t))
            sizs.append(t)

        s_str = ', '.join(f"{k_str}: {f(dd[k])}" for k, k_str, t in s)
        res_str = f"{label} {sum(sizs)} ({s_str})" if label else f"({s_str})"
        return res_str, computed


class Analysis:
    def __init__(self, benchmark_dir, args=None):
        assert benchmark_dir.is_dir(), benchmark_dir

        self.benchmark_dir = benchmark_dir.resolve()
        self.args = args

    def start(self):

        results_d = defaultdict(list)

        def load1(prog, resultdir):
            try:
                result = Result.load(resultdir)
                if prog:
                    results_d[prog].append(result)
                else:
                    results_d[result.filename.stem].append(result)

            except FileNotFoundError as ex:
                mlog.error(ex)
                pass

        def load2(dir_):
            for d in dir_.iterdir():
                if d.is_dir():
                    load1(dir_.stem, d)

        # rusult for a single run
        if (self.benchmark_dir / Result.resultfile).is_file():
            load1(None, self.benchmark_dir)

        # results for multiple runs (of a program)
        elif any((d / Result.resultfile).is_file()
                 for d in self.benchmark_dir.iterdir() if d.is_dir()):
            load2(self.benchmark_dir)

        else:  # results for multiple program
            for d in self.benchmark_dir.iterdir():
                if d.is_dir():
                    load2(d)

        summaries = []
        for prog in sorted(results_d):
            results = [AResult(r) for r in results_d[prog] if r.dinvs.siz]
            if not results:
                mlog.warning(f"no results for {prog}")
                continue
            stats = Results(prog, results)
            summary = stats.start(median_low)
            summaries.append(summary)
        return summaries
