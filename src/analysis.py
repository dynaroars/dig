"""
Analyze Dig's results
"""
import sys
import shutil
import time
import random
import pdb
from collections import Counter, defaultdict, namedtuple
from statistics import mean, median_low
from pathlib import Path
import argparse

import settings
from helpers.miscs import Miscs, MP
import helpers.vcommon as CM

import infer.inv
# import infer.mp

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)

CheckSolverCalls = namedtuple("CheckSolverCalls", ("stat"))
CheckDepthChanges = namedtuple("CheckDepthChanges", ("prop v1 d1 v2 d2"))
MaxSolverCalls = namedtuple("MaxSolverCalls", ("stat"))
MaxDepthChanges = namedtuple("MaxDepthChanges", "prop v1 d1 v2 d2")


class Result:
    resultfile = 'result'

    def __init__(self, filename, seed,
                 dinvs, dtraces, inps,
                 stats,
                 time_d):

        assert isinstance(time_d, dict) and time_d, time_d

        self.filename = filename
        self.seed = seed
        self.dinvs = dinvs
        self.dtraces = dtraces
        self.inps = inps
        self.stats = stats
        self.time_d = time_d

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
                         result.dtraces, result.inps, result.stats,
                         result.time_d)

        self.check_solvercalls = [
            s for s in self.stats if isinstance(s, CheckSolverCalls)]

        self.check_depthchanges = [
            s for s in self.stats if isinstance(s, CheckDepthChanges)]

        self.max_solvercalls = [
            s for s in self.stats if isinstance(s, MaxSolverCalls)]

        self.max_depthchanges = [
            s for s in self.stats if isinstance(s, MaxDepthChanges)]

        # print(len(self.check_solvercalls), self.check_solvercalls)

    def analyze(self):
        self.V, self.D, self.T, self.NL = self.analyze_dinvs(self.dinvs)

        def get_inv_typ(inv):
            assert inv is not None, inv
            return inv.__class__.__name__

        def get_change(x, y, as_str=True):
            if as_str:
                x = str(x)
                y = str(y)
            else:
                x = -1 if x is None else x
                y = -1 if y is None else y
            return (x, y)

        self.check_solvercalls_ctr = Counter(
            str(x.stat) for x in self.check_solvercalls)

        self.check_changevals_ctr = Counter(
            get_change(x.v1, x.v2, as_str=True)
            for x in self.check_depthchanges
            if not isinstance(x.prop, infer.inv.FalseInv))

        self.check_changedepths_ctr = Counter(
            get_change(x.d1, x.d2, as_str=False)
            for x in self.check_depthchanges
            if not isinstance(x.prop, infer.inv.FalseInv))

        self.max_solvercalls_ctr = Counter(
            str(x.stat) for x in self.max_solvercalls)

        self.max_changevals_ctr = Counter(
            get_change(x.v1, x.v2, as_str=True) for x in self.max_depthchanges
            if not isinstance(x.prop, infer.inv.FalseInv))

        self.max_changedepths_ctr = Counter(
            get_change(x.d1, x.d2, as_str=False)
            for x in self.max_depthchanges
            if not isinstance(x.prop, infer.inv.FalseInv))

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
        vss = set(str(v) for vs in vss for v in vs)
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

        # if isinstance(inv, infer.inv.prepost.PrePost):
        #     mlog.warning("Not very accurate for PREPOST")
        #     vs = []
        #     maxdegs = 1
        #     nterms = 1
        if isinstance(inv, infer.mp.MMP):
            vs = inv.term.symbols
            maxdeg = 1
            nterms = 2
        else:
            p = inv.inv
            vs = p.free_symbols
            assert p.is_Relational, p
            maxdeg = Miscs.get_max_deg(p.lhs)
            nterms = len(p.lhs.args)

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
        _ = [r.analyze() for r in rs]

        nruns = len(rs)
        nlocs = f(len(r.dinvs) for r in rs)
        V = f(r.V for r in rs)
        T = f(r.T for r in rs)
        D = f(r.D for r in rs)
        NL = f(r.NL for r in rs)

        invtypss = [r.dinvs.typ_ctr for r in rs]
        invtypss = self.analyze_dicts(invtypss, f, 'invs')

        check_solvercallss = [r.check_solvercalls_ctr for r in rs]
        check_solvercallss = self.analyze_dicts(
            check_solvercallss, f, '')

        check_changedepthss = [r.check_changedepths_ctr for r in rs]
        check_changedepthss = self.analyze_dicts(
            check_changedepthss, f, 'change depths')

        check_changevalss = [r.check_changevals_ctr for r in rs]
        check_changevalss = self.analyze_dicts(
            check_changevalss, f, 'change vals')

        max_solvercallss = [r.max_solvercalls_ctr for r in rs]
        max_solvercallss = self.analyze_dicts(
            max_solvercallss, f, '')

        max_changedepthss = [r.max_changedepths_ctr for r in rs]
        max_changedepthss = self.analyze_dicts(
            max_changedepthss, f, 'change depths')

        max_changevalss = [r.max_changevals_ctr for r in rs]
        max_changevalss = self.analyze_dicts(
            max_changevalss, f, 'change vals')

        time_d = defaultdict(list)
        for r in rs:
            for t in r.time_d:
                time_d[t].append(r.time_d[t])
        time_s = ', '.join("{} {:.1f}s".format(t, f(time_d[t]))
                           for t in sorted(time_d))

        print(f"* prog {self.prog} locs {nlocs}; "
              f"{invtypss} V {V} T {T} D {D}; NL {NL} ({D}) ;")

        print(f"-> time {time_s}")

        if settings.DO_SOLVER_STATS:
            print(
                f"-> checks {check_solvercallss} {check_changedepthss} {check_changevalss}")

            print(f"-> max {max_solvercallss} {max_changedepthss}")
            # , max_changevalss

        if nruns > 1:
            print(f"runs {nruns}")
        elif nruns == 1:
            print(f"rand seed {rs[0].seed}, "
                  f"test {random.randint(0, 100)}")
            # print(rs[0].dinvs.__str__(print_stat=False))

    @ classmethod
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

        for k in sorted(dd):
            t = f(dd[k])
            if isinstance(k, tuple):
                assert len(k) == 2
                from_, to_ = k
                k_str = f"{from_}->{to_}"
            else:
                k_str = str(k)
            s.append((k, k_str, t))
            sizs.append(t)

        s = ', '.join(f"{k_str}: {f(dd[k])}" for k, k_str, t in s)
        return f"{label} {sum(sizs)} ({s})"


class Benchmark:
    TIMEOUT = settings.BENCHMARK_TIMEOUT

    def __init__(self, inp, args):
        assert isinstance(inp, Path), inp
        assert isinstance(args, argparse.Namespace), args

        self.inp = inp
        self.args = args

    def valid_file(cls, f):
        return f.is_file() and f.suffix in {'.c', '.java'}

    def start(self):
        inp = self.inp
        args = self.args

        bfiles = []
        if self.valid_file(inp):
            # benchmark single file
            bfiles = [inp]
            bstr = inp.stem  # CohenDiv
        elif inp.is_dir():
            # benchmark all files in dir
            bfiles = sorted(f for f in inp.iterdir() if self.valid_file(f))
            bstr = str(inp.resolve()).replace('/', '_')   # /benchmark/nla
        else:
            mlog.error(f"something wrong with {inp}")
            sys.exit(1)
        ntimes = args.benchmark_times

        toruns = []
        if args.benchmark_dir:
            benchmark_dir = Path(args.benchmark_dir).resolve()
            assert benchmark_dir.is_dir(), benchmark_dir
        else:
            import tempfile
            prefix = f"bm_dig{ntimes}{bstr}_"
            benchmark_dir = Path(tempfile.mkdtemp(
                dir=settings.tmpdir, prefix=prefix))

        self.benchmark_dir = benchmark_dir

        # compute which runs have to do in case there are some existing runs
        self.toruns = []
        myruns = set(range(ntimes))
        for i, f in enumerate(bfiles):
            bmdir = benchmark_dir / f.stem
            if bmdir.is_dir():  # if there's some previous runs
                succruns = self.get_success_runs(bmdir)
                remainruns = list(myruns - succruns)
                if not remainruns:
                    mlog.info(f"{f} ran, results in {bmdir}")
                else:
                    mlog.info(
                        f"{f} in {bmdir} needs {len(remainruns)} more runs")
            else:
                remainruns = list(myruns)

            if remainruns:
                toruns.append((f, bmdir, remainruns))

            self.toruns = toruns

        opts = settings.setup(None, args)
        self.CMD = (f"timeout {self.TIMEOUT} python3 -O dig.py {opts} "
                    "{filename} -seed {seed} -tmpdir {tmpdir}")

        import os
        for i, (f, bdir, remainruns) in enumerate(self.toruns):
            if not bdir.is_dir():
                bdir.mkdir()

            for j, seed in enumerate(sorted(remainruns)):
                mlog.info(f"## file {i+1}/{len(self.toruns)}, run {j+1}/{len(remainruns)}, "
                          f"seed {seed}, {time.strftime('%c')}: {f}")
                try:
                    CMD = self.CMD.format(filename=f, seed=seed, tmpdir=bdir)
                    os.system(CMD)
                except Exception as ex:
                    mlog.error(f"Something wrong. Exiting!\n{ex}")

        mlog.info(f"benchmark result dir: {self.benchmark_dir}")

    def get_success_runs(self, rundir):
        assert rundir.is_dir(), rundir

        runs = set()
        for rd in rundir.iterdir():
            if not rd.is_dir():
                mlog.warning(f"Unexpected file {rd}")
                continue

            if (rd / Result.resultfile).is_file():
                # Dig_2_dxmdlf4y
                runi = int(rd.stem.split('_')[1])
                runs.add(runi)
            else:
                mlog.debug(f"deleting incomplete run {rd}")
                shutil.rmtree(rd)

        return runs


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

        for prog in sorted(results_d):
            results = [AResult(r) for r in results_d[prog] if r.dinvs.siz]
            if not results:
                mlog.warning(f"no results for {prog}")
                continue
            stats = Results(prog, results)
            stats.start(median_low)
            # stats.analyze(mean)
