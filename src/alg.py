from abc import ABCMeta, abstractmethod
import pdb
import random
from pathlib import Path
import time

import sage.all

import settings
from helpers.miscs import Miscs
import helpers.vcommon as CM


from data.prog import Prog
from data.traces import Inps, DTraces
from data.inv.invs import DInvs, Invs
DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Dig(metaclass=ABCMeta):

    def __init__(self, filename):
        if not isinstance(filename, Path):
            filename = Path(filename)

        if not filename.is_file():
            mlog.error("'{}' is not a valid file!".format(filename))
            exit(1)

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

    def print_results(self, dinvs, dtraces, inps, st):
        result = ("*** '{}', {} locs, "
                  "{} invs ({}), {} traces, {} inps, "
                  "time {:.2f}s, rand seed {}, test {} {}:\n{}")

        print(result.format(
            self.filename, len(dinvs),
            dinvs.siz,
            ', '.join('{} {}'.format(dinvs.typ_ctr[t], t)
                      for t in sorted(dinvs.typ_ctr)),
            dtraces.siz,
            len(inps) if inps else 0,
            time.time() - st,
            self.seed,
            random.randint(0, 100),
            sage.all.randint(0, 100),
            dinvs.__str__(print_stat=False)))


class DigSymStates(Dig):
    def __init__(self, filename):
        super().__init__(filename)

        self.set_mysrc()
        self.inp_decls = self.mysrc.inp_decls
        self.inv_decls = self.mysrc.inv_decls

        self.prog = Prog(self.exe_cmd, self.inp_decls, self.inv_decls)
        self.set_symbolic_states()

        # remove locations with no symbolic states
        invalid_locs = [loc for loc in self.inv_decls
                        if loc not in self.symstates.ss]

        for loc in invalid_locs:
            mlog.warning('{}: no symbolic states. Skip'.format(loc))
            self.inv_decls.pop(loc)

        self.locs = self.inv_decls.keys()

        self.use_rand_init = True

    def start(self, seed, maxdeg):
        assert maxdeg is None or maxdeg >= 1, maxdeg

        super().start(seed)

        mlog.info('infer invs at {} locs: {}'.format(
            len(self.locs), ', '.join(self.locs)))

        st = time.time()

        dinvs = DInvs()
        dtraces = DTraces.mk(self.locs)
        inps = Inps()

        # # BEGIN TESTING
        # m = sage.all.var("m")
        # tCtr = sage.all.var("tCtr")
        # import data.inv.eqt as Eqt
        # import data.inv.oct as Oct
        # dinvs['vtrace1_post'] = Invs({
        #     Oct.Oct(m - tCtr <= 4),
        #     Eqt.Eqt(m*tCtr ** 2 - tCtr ** 3 + 3*m*tCtr +
        #             2*tCtr ** 2 - 10*m + 25*tCtr - 50 == 0),
        #     Eqt.Eqt(m ** 2*tCtr - tCtr ** 3 + 5*m ** 2 + 3*m*tCtr +
        #             2*tCtr ** 2 + 15*m + 25*tCtr - 50 == 0),
        #     Oct.Oct(-tCtr <= 5)})
        # self.infer('preposts', dinvs,
        #            lambda: self.infer_preposts(dinvs, dtraces))
        # DBG()
        # # END TESTING
        if settings.DO_EQTS:
            self.infer('eqts', dinvs, lambda: self.infer_eqts(
                maxdeg, dtraces, inps))

        if settings.DO_IEQS or settings.DO_MINMAXPLUS:
            self.infer('ieqs', dinvs, lambda: self.infer_ieqs(dtraces, inps))

        dinvs = self.sanitize(dinvs, dtraces)

        if dinvs.n_eqs and settings.DO_PREPOSTS:
            self.infer('preposts', dinvs,
                       lambda: self.infer_preposts(dinvs, dtraces))

        self.print_results(dinvs, dtraces, inps, st)

        if settings.DO_RMTMP:
            import shutil
            mlog.debug("clean up: rm -rf {}".format(self.tmpdir))
            shutil.rmtree(self.tmpdir)
        else:
            tracefile = self.tmpdir / settings.TRACE_DIR / 'all.tcs'
            dtraces.vwrite(self.inv_decls, tracefile)
            mlog.info("tmpdir: {}".format(self.tmpdir))

        return dinvs, dtraces

    def infer(self, typ, dinvs, f):
        mlog.debug("infer '{}' at {} locs".format(typ, len(self.locs)))

        st = time.time()
        new_invs = f()
        if new_invs.siz:
            mlog.info("found {} {} ({:.2f}s)".format(
                new_invs.siz, typ, time.time() - st))

            dinvs.merge(new_invs)
            mlog.debug('{}'.format(dinvs.__str__(
                print_stat=True, print_first_n=20)))

    def infer_eqts(self, maxdeg, dtraces, inps):
        from cegir.eqt import CegirEqt
        solver = CegirEqt(self.symstates, self.prog)
        solver.use_rand_init = self.use_rand_init

        # determine degree
        auto_deg = self.get_auto_deg(maxdeg)
        return solver.gen(auto_deg, dtraces, inps)

    def infer_ieqs(self, dtraces, inps):
        from cegir.binsearch import CegirBinSearch
        solver = CegirBinSearch(self.symstates, self.prog)
        return solver.gen(dtraces, inps)

    def infer_preposts(self, dinvs, dtraces):
        from cegir.prepost import CegirPrePost
        solver = CegirPrePost(self.symstates, self.prog)
        return solver.gen(dinvs, dtraces)

    @property
    def tmpdir(self):
        try:
            return self._tmpdir
        except AttributeError:
            import tempfile
            self._tmpdir = Path(tempfile.mkdtemp(
                dir=settings.tmpdir, prefix="Dig_"))
            return self._tmpdir


class DigSymStatesJava(DigSymStates):
    def set_mysrc(self):
        from helpers.src import Java as mysrc
        self.mysrc = mysrc(self.filename, self.tmpdir)

    def set_symbolic_states(self):
        from data.symstates import SymStatesJava
        self.symstates = SymStatesJava(self.inp_decls, self.inv_decls)
        self.symstates.compute(
            self.filename, self.mysrc.mainQ_name,
            self.mysrc.funname, self.mysrc.symexedir)

    @property
    def exe_cmd(self):
        return settings.Java.JAVA_RUN(
            tracedir=self.mysrc.tracedir, funname=self.mysrc.funname)


class DigSymStatesC(DigSymStates):

    def set_mysrc(self):
        from helpers.src import C as mysrc
        self.mysrc = mysrc(self.filename, self.tmpdir)

    def set_symbolic_states(self):
        from data.symstates import SymStatesC
        self.symstates = SymStatesC(self.inp_decls, self.inv_decls)
        self.symstates.compute(
            self.mysrc.symexefile, self.mysrc.mainQ_name,
            self.mysrc.funname, self.mysrc.symexedir)

    @property
    def exe_cmd(self):
        return settings.C.C_RUN(exe=self.mysrc.traceexe)


class DigTraces(Dig):
    def __init__(self, tracefiles):
        tracefiles = tracefiles.split()
        assert len(tracefiles) == 1 or len(tracefiles) == 2, tracefiles

        tracefile = Path(tracefiles[0])

        super().__init__(tracefile)
        self.inv_decls, self.dtraces = DTraces.vread(tracefile)

        self.test_dtraces = None
        if len(tracefiles) == 2:
            test_tracefile = Path(tracefiles[1])
            _, self.test_dtraces = DTraces.vread(test_tracefile)

    def start(self, seed, maxdeg):
        assert maxdeg is None or maxdeg >= 1, maxdeg

        super().start(seed)

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

        dinvs = DInvs()
        for loc, invs in wrs:
            for inv in invs:
                dinvs.add(loc, inv)

        if self.test_dtraces:
            new_traces = self.dtraces.merge(self.test_dtraces)
            mlog.debug('added {} test traces'.format(new_traces.siz))

        dinvs = self.sanitize(dinvs, self.dtraces)
        self.print_results(dinvs, self.dtraces, None, st)
        return dinvs, None

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
