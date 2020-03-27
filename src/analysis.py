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

    def save(self, todir):
        assert todir.is_dir(), todir
        CM.vsave(todir / self.resultfile, self)

    @classmethod
    def load(cls, fromdir):
        assert isinstance(fromdir, Path) and fromdir.is_dir(), fromdir

        return CM.vload(fromdir / cls.resultfile)

    @property
    def nlocs(self):
        return len(self.dinvs)

    @property
    def ninvs(self):
        return self.dinvs.siz

    @property
    def invtyps(self):
        return self.dinvs.typ_ctr

    def str_of_dict(self, d):
        return "{} ({})".format(
            sum(d[k] for k in d),
            ', '.join('{} {}'.format(k, d[k]) for k in sorted(d)))

    def analyze_symstates(self):

        solver_calls = Counter(str(stat)
                               for stat, is_succ in self.solver_calls)

        def get_inv_typ(inv):
            # assert inv is None or isinstance(inv, Inv), inv
            try:
                return inv.__class__.__name__
            except AttributeError:
                assert inv is None
                print('W: unknown inv type: {}'.format(inv))
                return "Unknown"

        def get_change(x, y):
            return "{}->{}".format(x, y)

        change_stats = Counter(get_inv_typ(inv)
                               for inv, stat0, depth0, stat1, depth1 in self.depth_changes)
        # unsat->sat
        change_typs = Counter(get_change(stat0, stat1)
                              for inv, stat0, depth0, stat1, depth1 in self.depth_changes)
        # 9->10, 10->11
        change_depths = Counter(get_change(depth0, depth1)
                                for inv, stat0, depth0, stat1, depth1 in self.depth_changes)

        return solver_calls, change_stats, change_typs, change_depths

        # solver_calls_s = "solver calls {}".format(
        #     self.str_of_dict(solver_calls))
        # change_stats_s = "stats {}".format(self.str_of_dict(change_stats))
        # change_typs_s = "change typs {}".format(self.str_of_dict(change_typs))
        # change_depths_s = "change depths {}".format(
        #     self.str_of_dict(change_depths))

        # ss = [solver_calls_s, change_stats_s, change_typs_s, change_depths_s]
        # return ', '.join(ss)

    # def analyze(self):
    #     inv_typs = ', '.join('{} {}'.format(self.invtyps[t], t)
    #                          for t in sorted(self.invtyps))

    #     symstates_s = self.analyze_symstates()

    #     ss = [  # "file {}".format(dig.filename),
    #         "locs {}".format(len(self.dinvs)),
    #         "invs {} ({})".format(self.dinvs.siz, inv_typs),
    #         "traces {}".format(self.dtraces.siz),
    #         "inps {}".format(len(self.inps) if self.inps else 0),
    #         "time {:.2f}s".format(self.t_time),
    #         symstates_s,
    #         "rand seed {}, test ({}, {})".format(
    #             self.seed, random.randint(0, 100), sage.all.randint(0, 100))
    #     ]
    #     print("***",  ', '.join(s for s in ss if s))
    #     print(self.dinvs.__str__(print_stat=False))


class Stats:
    def __init__(self, prog, results):
        assert isinstance(prog, str), prog
        assert isinstance(results, list) and results, results
        assert all(isinstance(r, Result) for r in results), results

        self.prog = prog
        self.results = results

    @classmethod
    def mk_str(cls, d, f, msg=None, do_len=False):
        s = ', '.join('{} {}'.format(k, f(d[k])) for k in sorted(d))

        ss = []
        if msg:
            ss.append(msg)
        if do_len:
            print(list(d.values()))
            ss.append(sum(v if isinstance(v, (int, float)) else len(v)
                          for v in d.values()))

        if ss:
            return '{} ({})'.format(' '.join(map(str, ss)), s)
        else:
            return s

    @classmethod
    def mk_dict(cls, d1, d2):
        for k in d2:
            d1[k].append(d2[k])

    def analyze_invtyps(self, f):
        invtyps_d = defaultdict(list)
        for result in self.results:
            self.mk_dict(invtyps_d, result.invtyps)
        return self.mk_str(invtyps_d, f)

    def analyze_symstates(self, f):

        solver_calls_d = defaultdict(list)
        change_stats_d = defaultdict(list)
        change_typs_d = defaultdict(list)
        change_depths_d = defaultdict(list)
        for result in self.results:
            solver_calls, change_stats, change_typs, change_depths = result.analyze_symstates()

            self.mk_dict(solver_calls_d, solver_calls)
            self.mk_dict(change_stats_d, change_stats)
            self.mk_dict(change_typs_d, change_typs)
            self.mk_dict(change_depths_d, change_depths)

        ss = [
            self.mk_str(solver_calls_d, f, 'solver calls', do_len=True),
            self.mk_str(change_stats_d, f, 'change stats', do_len=True),
            self.mk_str(change_typs_d, f, 'change typs', do_len=True),
            self.mk_str(change_depths_d, f, 'change depths', do_len=True),
        ]
        return ', '.join(ss)

    def analyze(self, f):
        rs = self.results

        symstates_s = self.analyze_symstates(f)
        ss = [
            "prog {}".format(self.prog),
            "runs {}".format(len(rs)),
            "locs {}".format(f(r.nlocs for r in rs)),
            "invs {} ({})".format(
                f(r.ninvs for r in rs), self.analyze_invtyps(f)),
            "traces {}".format(f(r.dinvs.siz for r in rs)),
            "inps {}".format(
                f(len(r.inps) if r.inps else 0 for r in rs)),
            "time {:.2f}s".format(f(r.t_time for r in rs)),
            symstates_s
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

        import tempfile
        prefix = str(self.bdir).replace('/', '_')
        prefix = "dig_bm{}_".format(prefix)
        rdir = Path(tempfile.mkdtemp(dir=settings.tmpdir, prefix=prefix))

        settings.norm = True  # don't remove result dir

        mlog.info("Running each file in {} {} times. Result stored in {}".format(
            self.bdir, ntimes, rdir))

        fs = sorted(f for f in self.bdir.iterdir() if f.is_file())

        for i, f in enumerate(fs):
            settings.tmpdir = rdir / f.stem
            settings.tmpdir.mkdir()

            dig = run_f(f, self.args)
            for j in range(ntimes):
                mlog.info("## file {}/{}, run {}/{}. {}: {}".format(
                    i+1, len(fs), j+1, ntimes, time.strftime("%c"), f))

                dig.start(seed=j, maxdeg=self.args.maxdeg)

        mlog.info("benchmark result dir: {}".format(rdir))

    def analyze(self):
        results_d = defaultdict(list)

        # single result
        if (self.bdir / Result.resultfile).is_file():
            result = Result.load(self.bdir)
            results_d[result.filename.stem].append(result)
        else:
            for d in self.bdir.iterdir():
                for f in d.iterdir():
                    try:
                        results_d[d.name].append(Result.load(f))
                    except FileNotFoundError:
                        pass

        for d in sorted(results_d):
            stats = Stats(d, results_d[d])
            stats.analyze(median)
            # stats.analyze(mean)
