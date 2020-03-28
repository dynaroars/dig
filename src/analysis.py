"""
Analyze and print Dig's results
"""
import time
import random
import pdb
from collections import Counter, defaultdict
from statistics import mean, median
from pathlib import Path

import sage.all

import settings
import helpers.vcommon as CM

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Result:
    resultfile = 'result'

    def __init__(self, filename, seed,
                 dinvs, dtraces, inps,
                 solver_calls,
                 depth_changes,
                 t_time):

        self.filename = filename
        self.seed = seed
        self.dinvs = dinvs
        self.dtraces = dtraces
        self.inps = inps
        self.solver_calls = solver_calls
        self.depth_changes = depth_changes
        self.t_time = t_time

    def analyze(self):
        self.solver_calls_ctr = Counter(
            str(stat) for stat, is_succ in self.solver_calls)

        self.change_stats_ctr = Counter(
            self.get_inv_typ(inv)
            for inv, stat0, depth0, stat1, depth1 in self.depth_changes)

        self.change_typs_ctr = Counter(
            self.get_change(stat0, stat1)
            for inv, stat0, depth0, stat1, depth1 in self.depth_changes)

        self.change_depths_ctr = Counter(
            self.get_change(depth0, depth1)
            for inv, stat0, depth0, stat1, depth1 in self.depth_changes)

    def save(self, todir):
        assert todir.is_dir(), todir
        CM.vsave(todir / self.resultfile, self)

    @classmethod
    def load(cls, fromdir):
        assert isinstance(fromdir, Path) and fromdir.is_dir(), fromdir

        return CM.vload(fromdir / cls.resultfile)

    @classmethod
    def get_inv_typ(cls, inv):
        try:
            return inv.__class__.__name__
        except AttributeError:
            assert inv is None
            print('W: unknown inv type: {}'.format(inv))
            return "Unknown"

    @classmethod
    def get_change(cls, x, y):
        return "{}->{}".format(x, y)


class Stats:
    def __init__(self, prog, results):
        assert isinstance(prog, str), prog
        assert isinstance(results, list) and results, results
        assert all(isinstance(r, Result) for r in results), results

        self.prog = prog
        self.results = results

    @classmethod
    def analyze_dicts(cls, ds, f, label):
        ks = [k for d in ds for k in d]
        dd = defaultdict(list)
        for d in ds:
            for k in ks:
                try:
                    dd[k].append(d[k])
                except KeyError:
                    dd[k].append(0)

            dd['siz'].append(sum(v for v in d.values()))

        s = ', '.join('{} {}'.format(k, f(dd[k]))
                      for k in sorted(dd) if k != 'siz')
        return '{} {} ({})'.format(label, f(dd['siz']), s)

    def analyze2(self, f):
        invtypss = [r.dinvs.typ_ctr for r in self.results]
        solver_callss = [r.solver_calls_ctr for r in self.results]
        change_statss = [r.change_stats_ctr for r in self.results]
        change_typss = [r.change_typs_ctr for r in self.results]
        change_depthss = [r.change_depths_ctr for r in self.results]
        ss = [
            self.analyze_dicts(invtypss, f, 'invtyps'),
            self.analyze_dicts(solver_callss, f, 'solver calls'),
            self.analyze_dicts(change_statss, f, 'change stats'),
            self.analyze_dicts(change_typss, f, 'change typs'),
            self.analyze_dicts(change_depthss, f, 'change depths'),
        ]

        return ', '.join(ss)

    def analyze(self, f):
        rs = self.results
        _ = [r.analyze() for r in rs]

        ss = [
            "prog {}".format(self.prog),
            "runs {}".format(len(rs)),
            "locs {}".format(f(len(r.dinvs) for r in rs)),
            "traces {}".format(f(r.dinvs.siz for r in rs)),
            "inps {}".format(
                f(len(r.inps) if r.inps else 0 for r in rs)),
            "time {:.2f}s".format(f(r.t_time for r in rs)),
            self.analyze2(f)
        ]

        print('**', ', '.join(s for s in ss if s))
        if len(rs) == 1:
            print("rand seed {}, test ({}, {})".format(
                rs[0].seed, random.randint(0, 100), sage.all.randint(0, 100)))
            print(rs[0].dinvs.__str__(print_stat=False))


class Benchmark:
    def __init__(self, bdir, args=None):
        assert bdir.is_dir(), bdir

        self.bdir = bdir.resolve()
        self.args = args

    def run(self, run_f):
        ntimes = self.args.benchmark_times
        assert ntimes >= 1, ntimes

        benchmark_dir = Path(self.args.benchmark_dir).resolve()
        if not benchmark_dir:
            import tempfile
            prefix = str(self.bdir).replace('/', '_')
            prefix = "dig_bm{}_".format(prefix)
            benchmark_dir = Path(tempfile.mkdtemp(
                dir=settings.tmpdir, prefix=prefix))
        else:
            assert benchmark_dir.is_dir(), benchmark_dir

        settings.norm = True  # don't remove result dir

        mlog.info("Running each file in {} {} times. Result stored in {}".format(
            self.bdir, ntimes, benchmark_dir))

        fs = sorted(f for f in self.bdir.iterdir() if f.is_file())

        for i, f in enumerate(fs):
            bmdir = benchmark_dir / f.stem
            if bmdir.is_dir():
                mlog.warning("{} 'exists', skip '{}'".format(bmdir, f))
                continue
            else:
                settings.tmpdir = bmdir
                settings.tmpdir.mkdir()

            dig = run_f(f, self.args)
            for j in range(ntimes):
                mlog.info("## file {}/{}, run {}/{}. {}: {}".format(
                    i+1, len(fs), j+1, ntimes, time.strftime("%c"), f))

                dig.start(seed=j, maxdeg=self.args.maxdeg)

        mlog.info("benchmark result dir: {}".format(rdir))

    def analyze(self):

        results_d = defaultdict(list)

        def load1(prog, resultdir):
            try:
                results_d[prog].append(Result.load(resultdir))
            except FileNotFoundError as ex:
                mlog.error(ex)
                pass

        def load2(dir_):
            _ = [load1(dir_.stem, d) for d in dir_.iterdir() if d.is_dir()]

        # single result
        if (self.bdir / Result.resultfile).is_file():
            result = Result.load(self.bdir)
            results_d[result.filename.stem].append(result)

        elif any((d / Result.resultfile).is_file()
                 for d in self.bdir.iterdir() if d.is_dir()):

            load2(self.bdir)
        else:
            _ = [load2(d) for d in self.bdir.iterdir() if d.is_dir()]

        for prog in sorted(results_d):
            mlog.info("analyzing {}".format(prog))
            stats = Stats(prog, results_d[prog])
            stats.analyze(median)
            # stats.analyze(mean)
