from abc import ABCMeta, abstractmethod
import pdb
import random
import time
from pathlib import Path

import sage.all

import settings
from helpers.miscs import Miscs
import helpers.vcommon as CM

from data.prog import Prog
from data.traces import Inps, DTraces
from data.inv.invs import DInvs, Invs
from analysis import Result, Benchmark
import data.symstates
DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Dig(metaclass=ABCMeta):

    def __init__(self, filename):
        mlog.info("analyze '{}'".format(filename))
        self.filename = filename

    @abstractmethod
    def start(self, seed):
        self.seed = seed
        random.seed(seed)
        sage.all.set_random_seed(seed)
        mlog.debug("set seed to: {} (test {} {})".format(
            seed, random.randint(0, 100), sage.all.randint(0, 100)))

    def get_auto_deg(self, maxdeg):
        maxvars = max(self.inv_decls.values(), key=lambda d: len(d))
        deg = Miscs.get_auto_deg(maxdeg, len(maxvars), settings.MAX_TERM)
        return deg

    def sanitize(self, dinvs, dtraces):
        if not dinvs.siz:
            return dinvs

        msg = "test {} invs using {} traces".format(
            dinvs.siz, dtraces.siz)
        mlog.debug(msg)
        st = time.time()
        dinvs = dinvs.test(dtraces)
        mlog.info("{} ({:.2f}s)".format(msg, time.time() - st))

        if not dinvs.siz:
            return dinvs

        msg = "simplify {} invs".format(dinvs.siz)
        mlog.debug(msg)
        mlog.debug("{}".format(dinvs.__str__(
            print_stat=True, print_first_n=20)))
        st = time.time()
        dinvs = dinvs.simplify(self.inv_decls.use_reals)
        mlog.info("{} ({:.2f}s)".format(msg, time.time() - st))
        return dinvs


class DigSymStates(Dig):
    EQTS = "eqts"
    IEQS = "ieqs"
    MINMAX = "minmax"
    PREPOSTS = "preposts"

    def __init__(self, filename):
        super().__init__(filename)

    def start(self, seed, maxdeg):
        assert maxdeg is None or maxdeg >= 1, maxdeg

        super().start(seed)
        self.tmpdir = self.get_tmpdir()

        self.set_mysrc()
        self.inp_decls = self.mysrc.inp_decls
        self.inv_decls = self.mysrc.inv_decls

        self.prog = Prog(self.exe_cmd, self.inp_decls, self.inv_decls)
        self.use_rand_init = True

        self.symstates = None
        if settings.DO_SS:
            self.symstates = self.get_symbolic_states()

            # remove locations with no symbolic states
            for loc in self.inv_decls:
                if loc not in self.symstates.ss:
                    mlog.warning('{}: no symbolic states. Skip'.format(loc))
                    self.inv_decls.pop(loc)

        self.locs = self.inv_decls.keys()

        mlog.info('infer invs at {} locs: {}'.format(
            len(self.locs), ', '.join(self.locs)))

        st = time.time()

        dinvs = DInvs()
        dtraces = DTraces.mk(self.locs)
        inps = Inps()
        statss = []

        if settings.DO_EQTS:
            self.infer(self.EQTS, dinvs, statss,
                       lambda: self.infer_eqts(maxdeg, dtraces, inps))

        if settings.DO_IEQS:
            self.infer(self.IEQS, dinvs, statss,
                       lambda: self.infer_ieqs(dtraces, inps))

        if settings.DO_MINMAXPLUS:
            self.infer(self.MINMAX, dinvs, statss,
                       lambda: self.infer_minmax(dtraces, inps))

        dinvs = self.sanitize(dinvs, dtraces)

        if dinvs.n_eqs and settings.DO_PREPOSTS:
            self.infer('preposts', dinvs, statss,
                       lambda: self.infer_preposts(dinvs, dtraces))

        self.postprocess(dinvs, dtraces, inps, statss, time.time() - st)

    def postprocess(self, dinvs, dtraces, inps, statss, t_time):
        """
        Save and analyze result
        Clean up tmpdir
        """

        result = Result(self.filename, self.seed,
                        dinvs, dtraces, inps,
                        statss, t_time)

        result.save(self.tmpdir)
        Benchmark(self.tmpdir, args=None).analyze()

        if settings.DO_RMTMP:
            import shutil
            shutil.rmtree(self.tmpdir)
            mlog.debug("clean up: rm -rf {}".format(self.tmpdir))
        else:
            tracefile = self.tmpdir / settings.TRACE_DIR / 'all.tcs'
            dtraces.vwrite(self.inv_decls, tracefile)
            mlog.info("tmpdir: {}".format(self.tmpdir))

    def infer(self, typ, dinvs, statss, f):
        assert typ in {self.EQTS, self.IEQS, self.MINMAX, self.PREPOSTS}, typ
        mlog.debug("infer '{}' at {} locs".format(typ, len(self.locs)))

        st = time.time()
        new_invs, stats = f()
        statss.extend(stats)

        if new_invs.siz:
            mlog.info("found {} {} ({:.2f}s)".format(
                new_invs.siz, typ, time.time() - st))

            dinvs.merge(new_invs)
            mlog.debug('{}'.format(dinvs.__str__(
                print_stat=True, print_first_n=20)))

    def infer_eqts(self, maxdeg, dtraces, inps):
        from cegir.eqt import CegirEqts
        solver = CegirEqts(self.symstates, self.prog)
        solver.use_rand_init = self.use_rand_init

        # determine degree
        auto_deg = self.get_auto_deg(maxdeg)
        return solver.gen(auto_deg, dtraces, inps)

    def infer_ieqs(self, dtraces, inps):
        from cegir.ieqs import CegirIeqs
        solver = CegirIeqs(self.symstates, self.prog)
        return solver.gen(dtraces, inps)

    def infer_minmax(self, dtraces, inps):
        from cegir.binsearch import CegirBinSearch
        solver = CegirBinSearch(self.symstates, self.prog)
        return solver.gen(dtraces, inps)

    def infer_preposts(self, dinvs, dtraces):
        from cegir.prepost import CegirPrePost
        solver = CegirPrePost(self.symstates, self.prog)
        return solver.gen(dinvs, dtraces)

    def get_tmpdir(self):
        import tempfile
        tmpdir = Path(tempfile.mkdtemp(
            dir=settings.tmpdir, prefix="dig_{}_".format(hash(self.seed))))
        return tmpdir


class DigSymStatesJava(DigSymStates):

    def set_mysrc(self):
        from helpers.src import Java as mysrc
        self.mysrc = mysrc(self.filename, self.tmpdir)

    def get_symbolic_states(self):
        symstates = data.symstates.SymStatesJava(
            self.inp_decls, self.inv_decls)
        symstates.compute(
            self.filename, self.mysrc.mainQ_name,
            self.mysrc.funname, self.mysrc.symexedir)
        return symstates

    @property
    def exe_cmd(self):
        return settings.Java.JAVA_RUN(
            tracedir=self.mysrc.tracedir, funname=self.mysrc.funname)


class DigSymStatesC(DigSymStates):

    def set_mysrc(self):
        from helpers.src import C as mysrc
        self.mysrc = mysrc(self.filename, self.tmpdir)

    def get_symbolic_states(self):
        symstates = data.symstates.SymStatesC(
            self.inp_decls, self.inv_decls)
        symstates.compute(
            self.mysrc.symexefile, self.mysrc.mainQ_name,
            self.mysrc.funname, self.mysrc.symexedir)
        return symstates

    @property
    def exe_cmd(self):
        return settings.C.C_RUN(exe=self.mysrc.traceexe)


class DigTraces(Dig):
    def __init__(self, tracefile, test_tracefile):
        assert tracefile.is_file(), tracefile
        assert test_tracefile is None or test_tracefile.is_file()

        super().__init__(tracefile)
        self.inv_decls, self.dtraces = DTraces.vread(tracefile)

        if test_tracefile:
            _, self.test_dtraces = DTraces.vread(test_tracefile)

    def start(self, seed, maxdeg):
        assert maxdeg is None or maxdeg >= 1, maxdeg

        super().start(seed)
        self.tmpdir = self.get_tmpdir()

        st = time.time()

        tasks = []
        for loc in self.dtraces:
            symbols = self.inv_decls[loc]
            traces = self.dtraces[loc]
            if settings.DO_EQTS:
                def _f():
                    return self.infer_eqts(maxdeg, symbols, traces)
                tasks.append((loc, _f))

            if settings.DO_IEQS:
                def _f():
                    return self.infer_ieqs(symbols, traces)
                tasks.append((loc, _f))

        def f(tasks):
            rs = [(loc, _f()) for loc, _f in tasks]
            return rs
        wrs = Miscs.run_mp("dynamic inference", tasks, f)

        statss = []
        dinvs = DInvs()
        for loc, invs, stats in wrs:
            statss.extend(stats)
            for inv in invs:
                dinvs.add(loc, inv)

        if self.test_dtraces:
            new_traces = self.dtraces.merge(self.test_dtraces)
            mlog.debug('added {} test traces'.format(new_traces.siz))

        dinvs = self.sanitize(dinvs, self.dtraces)
        # Analysis(self, dinvs, self.dtraces, None, time.time() - st).doit()

    def infer_eqts(self, maxdeg, symbols, traces):
        import data.inv.eqt

        auto_deg = self.get_auto_deg(maxdeg)
        terms, template, uks, n_eqts_needed = Miscs.init_terms(
            symbols.names, auto_deg, settings.EQT_RATE)
        exprs = list(traces.instantiate(template, n_eqts_needed))
        eqts = Miscs.solve_eqts(exprs, uks, template)
        return [data.inv.eqt.Eqt(eqt) for eqt in eqts]

    def infer_ieqs(self, symbols, traces):
        import data.inv.oct
        maxV = settings.OCT_MAX_V
        minV = -1*maxV

        oct_siz = 2
        terms = Miscs.get_terms_fixed_coefs(symbols.sageExprs, oct_siz)
        octs = []
        for t in terms:
            upperbound = max(traces.myeval(t))
            if upperbound > maxV or upperbound < minV:
                continue
            octs.append(t <= upperbound)
        octs = [data.inv.oct.Oct(oct) for oct in octs]
        return octs
