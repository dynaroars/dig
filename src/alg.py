from abc import ABCMeta, abstractmethod
import pdb
import random
import time
from pathlib import Path
import psutil
import os

import sage.all

import settings
from helpers.miscs import Miscs
import helpers.vcommon as CM

import data.prog
from data.traces import Inps, DTraces
from data.inv.invs import DInvs, Invs
import data.symstates
DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


def killtree(pid, including_parent=True):
    parent = psutil.Process(pid)
    for child in parent.children(recursive=True):
        mlog.warning(f"Terminate child {child}")
        child.terminate()

    if including_parent:
        mlog.warning(f"Terminate parent {parent}")
        parent.terminate()


class Dig(metaclass=ABCMeta):
    def __init__(self, filename):
        mlog.info("analyze '{}'".format(filename))
        self.filename = filename
        self.time_d = {}  # time results

    @abstractmethod
    def start(self, seed, maxdeg):
        self.seed = seed
        random.seed(seed)
        sage.all.set_random_seed(seed)
        mlog.debug("set seed to {} (test {} {})".format(
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

        if settings.DO_SIMPLIFY:
            try:
                self.symstates.get_solver_stats()
            except AttributeError:
                # DigTraces does not have symbolic states
                pass

            msg = "simplify {} invs".format(dinvs.siz)
            mlog.debug(msg)
            mlog.debug("{}".format(dinvs.__str__(
                print_stat=True, print_first_n=20)))
            st1 = time.time()
            dinvs = dinvs.simplify(self.inv_decls.use_reals)
            mlog.info("{} ({:.2f}s)".format(msg, time.time() - st1))

        self.time_d['simplify'] = time.time() - st

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
        st = time.time()

        super().start(seed, maxdeg)

        assert settings.tmpdir.is_dir()
        import tempfile
        prefix = hash(self.seed)
        self.tmpdir = Path(tempfile.mkdtemp(
            dir=settings.tmpdir, prefix="dig_{}_".format(prefix)))
        self.tmpdir_del = self.tmpdir / "delete_me"
        self.tmpdir_del.mkdir()

        self.mysrc = self.mysrc_cls(self.filename, self.tmpdir_del)
        self.inp_decls = self.mysrc.inp_decls
        self.inv_decls = self.mysrc.inv_decls

        self.prog = data.prog.Prog(
            self.exe_cmd, self.inp_decls, self.inv_decls)
        self.use_rand_init = True

        self.symstates = None
        if settings.DO_SS:
            st = time.time()
            self.symstates = self.get_symbolic_states()
            et = time.time() - st
            mlog.info("compute symbolic states ({:.2f}s)".format(et))
            self.time_d['symbolic_states'] = et

            # remove locations with no symbolic states
            for loc in list(self.inv_decls.keys()):
                if loc not in self.symstates:
                    mlog.warning('{}: no symbolic states. Skip'.format(loc))
                    self.inv_decls.pop(loc)

        self.locs = self.inv_decls.keys()

        mlog.info('infer invs at {} locs: {}'.format(
            len(self.locs), ', '.join(self.locs)))

        dinvs = DInvs()
        dtraces = DTraces.mk(self.locs)
        inps = Inps()

        if settings.DO_EQTS:
            self.infer(self.EQTS, dinvs,
                       lambda: self.infer_eqts(maxdeg, dtraces, inps))

        if settings.DO_IEQS:
            self.infer(self.IEQS, dinvs,
                       lambda: self.infer_ieqs(dtraces, inps))

        if settings.DO_MINMAXPLUS:
            self.infer(self.MINMAX, dinvs,
                       lambda: self.infer_minmax(dtraces, inps))

        dinvs = self.sanitize(dinvs, dtraces)

        if dinvs.n_eqs and settings.DO_PREPOSTS:
            self.infer('preposts', dinvs,
                       lambda: self.infer_preposts(dinvs, dtraces))

        et = time.time() - st
        self.time_d['total'] = et

        print("{}\nrun time {:.2f}s, result dir: {}".format(
            dinvs, et, self.tmpdir))

        self.postprocess(dinvs, dtraces, inps)

    def postprocess(self, dinvs, dtraces, inps):
        """
        Save and analyze result
        Clean up tmpdir
        """
        # clean up
        import shutil
        shutil.rmtree(self.tmpdir_del)

        # analyze and save results
        from analysis import Result, Analysis

        self.symstates.get_solver_stats()
        result = Result(self.filename, self.seed,
                        dinvs, dtraces, inps,
                        self.symstates.solver_stats_,
                        self.time_d)
        result.save(self.tmpdir)
        Analysis(self.tmpdir).start()
        mlog.info("tmpdir: {}".format(self.tmpdir))

    def infer(self, typ, dinvs, f):
        assert typ in {self.EQTS, self.IEQS, self.MINMAX, self.PREPOSTS}, typ
        mlog.debug("infer '{}' at {} locs".format(typ, len(self.locs)))

        st = time.time()
        new_invs = f()  # get invs

        if new_invs.siz:
            et = time.time() - st
            self.time_d[typ] = et
            mlog.info("found {} {} ({:.2f}s)".format(
                new_invs.siz, typ, et))

            dinvs.merge(new_invs)
            mlog.debug('{}'.format(dinvs.__str__(
                print_stat=True, print_first_n=20)))

    def my_infer_eqts(self, solver, auto_deg, dtraces, inps, timeout):
        from queue import Empty
        from multiprocessing import Process, Queue

        self.symstates.get_solver_stats()

        def wprocess(auto_deg, dtraces, inps, myQ):
            dinvs = solver.gen(auto_deg, dtraces, inps)
            myQ.put((dinvs, dtraces, inps))
            myQ.close()
            myQ.join_thread()

        is_timeout = False
        mlog.warning(f"### BEGIN my_infer_eqts")
        Q = Queue()
        worker = Process(target=wprocess, args=(auto_deg, dtraces, inps, Q))
        worker.start()

        try:
            dinvs, _dtraces, _inps = Q.get(timeout=timeout)
        except Empty:
            is_timeout = True

        mlog.warning(f"### AFTER Queue get is_timeout={is_timeout}")
        worker.join(timeout=1)
        if worker.is_alive():
            killtree(worker.pid)
            worker.terminate()
            is_timeout = True
        worker.join()
        mlog.warning(f"### AFTER 2nd JOIN  ec={worker.exitcode}")
        worker.close()

        if is_timeout:
            dinvs = DInvs()
            self.symstates.reset_solver_stats()
        else:
            dtraces, inps = _dtraces, _inps

        return dinvs, dtraces, inps, is_timeout

    def my_infer_eqts2(self, solver, auto_deg, dtraces, inps):

        timeout = settings.EQT_SOLVER_TIMEOUT
        maxct = settings.EQT_SOLVER_TIMEOUT_MAXTRIES
        ct = 0
        while True:
            dinvs, dtraces, inps, is_timeout = self.my_infer_eqts(
                solver, auto_deg, dtraces, inps, timeout)
            if is_timeout is False or ct >= maxct:
                break
            ct += 1
            mlog.warning('eqt solving, try {}/{} using timeout {}'.format(
                ct, maxct, timeout))

        return dinvs

    def infer_eqts(self, maxdeg, dtraces, inps):
        import infer.eqt
        solver = infer.eqt.Infer(self.symstates, self.prog)
        solver.use_rand_init = self.use_rand_init

        # determine degree
        auto_deg = self.get_auto_deg(maxdeg)

        dinvs = self.my_infer_eqts2(solver, auto_deg, dtraces, inps)
        #dinvs = solver.gen(auto_deg, dtraces, inps)
        return dinvs

    def infer_ieqs(self, dtraces, inps):
        import infer.opt
        solver = infer.opt.Ieq(self.symstates, self.prog)
        return solver.gen(dtraces)

    def infer_minmax(self, dtraces, inps):
        import infer.opt
        solver = infer.opt.MP(self.symstates, self.prog)
        return solver.gen(dtraces)

    def infer_preposts(self, dinvs, dtraces):
        import infer.prepost
        solver = infer.prepost.Infer(self.symstates, self.prog)
        return solver.gen(dinvs, dtraces)

    def get_symbolic_states(self):
        symstates = data.symstates.SymStates(self.inp_decls, self.inv_decls)
        symstates.compute(self.symstatesmaker_cls,
                          self.symexefile, self.mysrc.mainQ_name,
                          self.mysrc.funname, self.mysrc.symexedir)
        return symstates


class DigSymStatesJava(DigSymStates):

    @property
    def mysrc_cls(self):
        return data.prog.Java

    @property
    def symstatesmaker_cls(self):
        return data.symstates.SymStatesMakerJava

    @property
    def symexefile(self):
        return self.filename

    @property
    def exe_cmd(self):
        return settings.Java.JAVA_RUN(
            tracedir=self.mysrc.tracedir, funname=self.mysrc.funname)


class DigSymStatesC(DigSymStates):

    @property
    def mysrc_cls(self):
        return data.prog.C

    @property
    def symstatesmaker_cls(self):
        return data.symstates.SymStatesMakerC

    @property
    def symexefile(self):
        return self.mysrc.symexefile

    @property
    def exe_cmd(self):
        return settings.C.C_RUN(exe=self.mysrc.traceexe)


class DigTraces(Dig):
    def __init__(self, tracefile, test_tracefile):
        assert tracefile.is_file(), tracefile
        assert test_tracefile is None or test_tracefile.is_file()

        super().__init__(tracefile)
        self.inv_decls, self.dtraces = DTraces.vread(tracefile)
        for t in self.dtraces.values():
            print(type(t))
            print(t.maxdeg)
        DBG()
        if test_tracefile:
            _, self.test_dtraces = DTraces.vread(test_tracefile)

    def start(self, seed, maxdeg):
        assert maxdeg is None or maxdeg >= 1, maxdeg

        super().start(seed, maxdeg)

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
        wrs = Miscs.run_mp("(pure) dynamic inference", tasks, f)

        dinvs = DInvs()
        for loc, invs in wrs:
            for inv in invs:
                dinvs.add(loc, inv)

        try:
            new_traces = self.dtraces.merge(self.test_dtraces)
            mlog.debug('added {} test traces'.format(new_traces.siz))
        except AttributeError:
            # no test traces
            pass

        dinvs = self.sanitize(dinvs, self.dtraces)
        print(dinvs)

    def infer_eqts(self, maxdeg, symbols, traces):
        auto_deg = self.get_auto_deg(maxdeg)
        terms, template, uks, n_eqts_needed = Miscs.init_terms(
            symbols.names, auto_deg, settings.EQT_RATE)
        exprs = list(traces.instantiate(template, n_eqts_needed))
        from multiprocessing import Process, Queue

        def wprocess(exprs, uks, template, myQ):
            rs = Miscs.solve_eqts(exprs, uks, template)
            myQ.put(rs)
        Q = Queue()
        worker = Process(target=wprocess, args=(exprs, uks, template, Q))
        worker.start()
        worker.join(timeout=1)
        worker.teminate()

        if worker.exitcode is None:
            mlog.error("timeout!")

        eqts = Q.get()

        #eqts = Miscs.solve_eqts(exprs, uks, template)
        import data.inv.eqt
        return [data.inv.eqt.Eqt(eqt) for eqt in eqts]

    def infer_ieqs(self, symbols, traces):
        maxV = settings.IUPPER
        minV = -1*maxV

        terms = Miscs.get_terms_fixed_coefs(
            symbols.sageExprs, settings.ITERMS, settings.ICOEFS,
        )
        ieqs = []
        for t in terms:
            upperbound = max(traces.myeval(t))
            if upperbound > maxV or upperbound < minV:
                continue
            ieqs.append(t <= upperbound)

        import data.inv.oct
        ieqs = [data.inv.oct.Oct(ieq) for ieq in ieqs]
        return ieqs
