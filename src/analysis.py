"""
Analyze and print Dig's results
"""
import shutil
import time
import random
import pdb
from collections import Counter, defaultdict, namedtuple
from statistics import mean, median
from pathlib import Path

import sage.all

import settings
import helpers.vcommon as CM
import data.inv

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class CheckSolverCalls(namedtuple("CheckSolverCalls", ("stat",))):
    pass


class CheckDepthChanges(namedtuple("CheckDepthChanges", ("prop", "v1", "d1", "v2", "d2"))):
    pass


class MaxSolverCalls(namedtuple("MaxSolverCalls", ("stat",))):
    pass


class MaxDepthChanges(namedtuple("MaxDepthChanges", ("prop", "v1", "d1", "v2", "d2"))):
    pass


class Result:
    resultfile = 'result'

    def __init__(self, filename, seed,
                 dinvs, dtraces, inps,
                 stats,
                 t_time):

        self.filename = filename
        self.seed = seed
        self.dinvs = dinvs
        self.dtraces = dtraces
        self.inps = inps

        self.solver_calls = [
            stat for stat in stats if isinstance(stat, CheckSolverCalls)]
        self.depth_changes = [
            stat for stat in stats if isinstance(stat, CheckDepthChanges)]

        self.t_time = t_time

    @classmethod
    def get_degs(cls, p):
        if p.operands():
            degs = []
            for p_ in p.operands():
                deg = sum(p_.degree(v) for v in p_.variables())
                degs.append(deg)
            return degs
        else:  # x
            assert len(p.variables()) == 1, p
            return [1]

    @classmethod
    def analyze_inv(cls, inv):
        """
        return the # of variables, max deg, and number of terms
        """
        if isinstance(inv, data.inv.prepost.PrePost):
            mlog.warning("Not very accurate for PREPOST")
            vs = []
            degs = [1]
            nterms = 1
        elif isinstance(inv, data.inv.mp.MP):
            vs = inv.term.symbols
            degs = [1]
            nterms = 1
        else:
            p = inv.inv
            vs = p.variables()
            degs = cls.get_degs(p.lhs())
            nterms = p.lhs().number_of_operands()

        return vs, max(degs), nterms

    @classmethod
    def analyze_dinvs(cls, dinvs):
        """
        Get max vars, terms, deg, mainly for eqts
        """

        vss = []
        maxdegs = []
        ntermss = []

        for inv in dinvs.invs:
            nvs, maxdeg, nterms = cls.analyze_inv(inv)
            vss.append(nvs)
            maxdegs.append(maxdeg)
            ntermss.append(nterms)

        nvs = len(set(v for vs in vss for v in vs))
        maxdeg = max(maxdegs)
        nterms = max(ntermss)
        return nvs, maxdeg, nterms

    def analyze(self):

        self.V, self.D, self.T = self.analyze_dinvs(self.dinvs)

        def get_inv_typ(inv):
            assert inv is not None, inv
            return inv.__class__.__name__

        def get_change(x, y):
            return "{}->{}".format(x, y)

        self.solver_calls_ctr = Counter(
            str(stat) for stat, is_succ in self.solver_calls)

        self.change_stats_ctr = Counter(
            get_change(stat0, stat1)
            for inv, stat0, depth0, stat1, depth1 in self.depth_changes
            if not isinstance(inv, data.inv.invs.FalseInv)
        )

        self.change_typs_ctr = Counter(
            get_inv_typ(inv)
            for inv, stat0, depth0, stat1, depth1 in self.depth_changes
            if not isinstance(inv, data.inv.invs.FalseInv)
        )

        self.change_depths_ctr = Counter(
            get_change(depth0, depth1)
            for inv, stat0, depth0, stat1, depth1 in self.depth_changes
            if not isinstance(inv, data.inv.invs.FalseInv)
        )

    def save(self, todir):
        assert todir.is_dir(), todir
        CM.vsave(todir / self.resultfile, self)

    @classmethod
    def load(cls, fromdir):
        assert isinstance(fromdir, Path) and fromdir.is_dir(), fromdir

        return CM.vload(fromdir / cls.resultfile)


class Stats:
    def __init__(self, prog, results):
        assert isinstance(prog, str), prog
        assert isinstance(results, list) and results, results
        assert all(isinstance(r, Result) for r in results), results

        self.prog = prog
        self.results = results

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
        for k in sorted(dd):
            t = f(dd[k])
            s.append((k, t))
            sizs.append(t)

        s = ', '.join('{} {}'.format(k, f(dd[k]))
                      for k, t in s)

        return '{} {} ({})'.format(label, sum(sizs), s)

    def analyze2(self, f):
        invtypss = [r.dinvs.typ_ctr for r in self.results]
        solver_callss = [r.solver_calls_ctr for r in self.results]
        change_statss = [r.change_stats_ctr for r in self.results]
        change_typss = [r.change_typs_ctr for r in self.results]
        change_depthss = [r.change_depths_ctr for r in self.results]
        ss = [
            self.analyze_dicts(invtypss, f, 'invs'),
            self.analyze_dicts(solver_callss, f, 'solver calls'),
            self.analyze_dicts(change_statss, f, 'change stats'),
            self.analyze_dicts(change_typss, f, 'change typs'),
            self.analyze_dicts(change_depthss, f, 'change depths'),
        ]

        return ', '.join(ss)

    def start(self, f):
        rs = self.results
        _ = [r.analyze() for r in rs]
        VTD = "{},{},{}".format(f(r.V for r in rs), f(
            r.T for r in rs), f(r.D for r in rs))
        ss = [
            "prog {}".format(self.prog),
            "runs {}".format(len(rs)),
            "locs {}".format(f(len(r.dinvs) for r in rs)),
            "VTD {}".format(VTD),
            "traces {}".format(f(r.dtraces.siz for r in rs)),
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
    TIMEOUT = 900  # seconds

    def __init__(self, inp, args):
        assert isinstance(inp, Path), inp
        assert isinstance(args, dict)

        self.inp = inp
        self.args = args

    def start(self):
        inp = self.inp
        args = self.args

        if inp.is_file():
            # benchmark single file
            bfiles = [inp]
            bstr = inp.stem  # CohenDiv
        else:
            assert inp.is_dir(), inp
            # benchmark all files in dir
            bfiles = sorted(f for f in inp.iterdir() if f.is_file())
            bstr = str(inp.resolve()).replace('/', '_')   # /benchmark/nla

        ntimes = args.benchmark_times

        toruns = []
        if args.benchmark_dir:
            benchmark_dir = Path(args.benchmark_dir).resolve()
            assert benchmark_dir.is_dir(), benchmark_dir
        else:
            import tempfile
            prefix = "dig_bm{}{}_".format(ntimes, bstr)
            benchmark_dir = Path(tempfile.mkdtemp(
                dir=settings.tmpdir, prefix=prefix))

        self.benchmark_dir = benchmark_dir

        # compute which runs we have to do (in case there are some existing runs)
        myruns = set(range(ntimes))
        for i, f in enumerate(bfiles):
            bmdir = benchmark_dir / f.stem
            if bmdir.is_dir():  # if there's some previous runs
                succruns = self.get_success_runs(bmdir)
                remainruns = list(myruns - succruns)
                if not remainruns:
                    mlog.info(
                        "{} ran, results in {}".format(f, bmdir))
                else:
                    mlog.info("{} in {} needs {} more runs".format(
                        f, bmdir, len(remainruns)))
            else:
                remainruns = list(myruns)

            if remainruns:
                toruns.append((f, bmdir, remainruns))

            self.toruns = toruns

        opts = settings.setup(None, args)
        self.CMD = "timeout {timeout} sage -python -O dig.py {opts} ".format(
            timeout=self.TIMEOUT, opts=opts) \
            + "{filename} -seed {seed} -tmpdir {tmpdir}"

        import os
        for i, (f, bdir, remainruns) in enumerate(self.toruns):
            if not bdir.is_dir():
                bdir.mkdir()

            for j, seed in enumerate(sorted(remainruns)):
                mlog.info("## file {}/{}, run {}/{}, seed {}, {}: {}".format(
                    i+1, len(self.toruns), j+1, len(remainruns), seed, time.strftime("%c"), f))
                try:
                    CMD = self.CMD.format(filename=f, seed=seed, tmpdir=bdir)
                    os.system(CMD)
                except Exception as ex:
                    mlog.error("Something wrong. Exiting!\n{}".format(ex))

        mlog.info("benchmark result dir: {}".format(self.benchmark_dir))

    def get_success_runs(self, rundir):
        assert rundir.is_dir(), rundir

        runs = set()
        for rd in rundir.iterdir():
            if not rd.is_dir():
                mlog.warning('Unexpected file {}'.format(rd))

            if (rd / Result.resultfile).is_file():
                # Dig_2_dxmdlf4y
                runi = int(rd.stem.split('_')[1])
                runs.add(runi)
            else:
                mlog.debug('deleting incomplete run {}'.format(rd))
                shutil.rmtree(rd)

        return runs


class Analysis:
    def __init__(self, bdir, args=None):
        assert bdir.is_dir(), bdir

        self.bdir = bdir.resolve()
        self.args = args

    def start(self):

        results_d = defaultdict(list)

        def load1(prog, resultdir):
            try:
                results_d[prog].append(Result.load(resultdir))
            except FileNotFoundError as ex:
                mlog.error(ex)
                pass

        def load2(dir_):
            for d in dir_.iterdir():
                if d.is_dir():
                    load1(dir_.stem, d)

        # single result
        if (self.bdir / Result.resultfile).is_file():
            result = Result.load(self.bdir)
            results_d[result.filename.stem].append(result)

        elif any((d / Result.resultfile).is_file()
                 for d in self.bdir.iterdir() if d.is_dir()):

            load2(self.bdir)
        else:
            for d in self.bdir.iterdir():
                if d.is_dir():
                    load2(d)

        for prog in sorted(results_d):
            if not results_d[prog]:
                continue
            stats = Stats(prog, results_d[prog])
            stats.start(median)
            # stats.analyze(mean)
