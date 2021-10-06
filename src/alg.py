from abc import ABCMeta, abstractmethod
import itertools
import pdb
import random
import time
from pathlib import Path
import psutil
import os
from threading import Thread

import settings

from helpers.miscs import Miscs, MP
import helpers.vcommon as CM

import data.prog
from data.traces import Inps, DTraces
from data.inv.invs import DInvs, Invs
import data.symstates

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Dig(metaclass=ABCMeta):
    def __init__(self, filename):
        mlog.info(f"analyze '{filename}'")
        self.filename = filename
        self.time_d = {}  # time results

    @abstractmethod
    def start(self, seed, maxdeg):
        self.seed = seed
        random.seed(seed)
        mlog.debug(
            f"set seed to {seed} "
            f"(test {random.randint(0, 100)})"
        )

    def get_auto_deg(self, maxdeg):
        assert maxdeg is None or maxdeg >= 1, maxdeg

        maxvars = max(self.inv_decls.values(), key=lambda d: len(d))
        deg = Miscs.get_auto_deg(maxdeg, len(maxvars), settings.MAX_TERM)
        return deg

    def sanitize(self, dinvs, dtraces):
        if not dinvs.siz:
            return dinvs

        msg = f"test {dinvs.siz} invs using {dtraces.siz} traces"
        mlog.debug(msg)
        st = time.time()
        dinvs = dinvs.test(dtraces)
        mlog.info(f"{msg} ({time.time() - st:.2f}s)")

        if not dinvs.siz:
            return dinvs

        if settings.DO_SIMPLIFY:
            try:
                self.symstates.get_solver_stats()
            except AttributeError:
                # DigTraces does not have symbolic states
                pass

            msg = f"simplify {dinvs.siz} invs"
            mlog.debug(msg)
            mlog.debug(dinvs.__str__(print_stat=True, print_first_n=20))
            st1 = time.time()
            dinvs = dinvs.simplify()
            mlog.info(f"{msg} ({time.time() - st1:.2f}s)")

        self.time_d["simplify"] = time.time() - st

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
        self.tmpdir = Path(
            tempfile.mkdtemp(dir=settings.tmpdir, prefix=f"dig_{prefix}_")
        )
        self.tmpdir_del = self.tmpdir / "delete_me"
        self.tmpdir_del.mkdir()

        self.mysrc = self.mysrc_cls(self.filename, self.tmpdir_del)
        self.inp_decls = self.mysrc.inp_decls
        self.inv_decls = self.mysrc.inv_decls

        self.prog = data.prog.Prog(
            self.exe_cmd, self.inp_decls, self.inv_decls)
        self.use_rand_init = True

        self.locs = self.inv_decls.keys()

        self.symstates = None
        if settings.DO_SS:
            st = time.time()
            self.symstates = self.get_symbolic_states()
            et = time.time() - st
            mlog.info(
                f"got symbolic states at {len(self.locs)} locs: ({et:.2f}s)"
            )

            self.time_d["symbolic_states"] = et

            # remove locations with no symbolic states
            for loc in list(self.inv_decls.keys()):
                if loc not in self.symstates:
                    mlog.warning(f"{loc}: no symbolic states. Skip")
                    self.inv_decls.pop(loc)

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
            self.infer("preposts", dinvs,
                       lambda: self.infer_preposts(dinvs, dtraces))

        et = time.time() - st
        self.time_d["total"] = et

        # print(f"{dinvs}\nrun time {et:.2f}s, result dir: {self.tmpdir}")

        self.cleanup(dinvs, dtraces, inps)

        if settings.WRITE_VTRACES:
            tracefile = self.tmpdir/"alltraces.csv"
            dtraces.vwrite(self.inv_decls, tracefile)
            mlog.info(f"traces written to {tracefile}")

        print(f"tmpdir: {self.tmpdir}")

    def cleanup(self, dinvs, dtraces, inps):
        """
        Save and analyze result
        Clean up tmpdir
        """
        # clean up
        import shutil

        shutil.rmtree(self.tmpdir_del)

        # analyze and save results
        from analysis import Result, Analysis

        result = Result(
            self.filename,
            self.seed,
            dinvs,
            dtraces,
            inps,
            self.symstates.solver_stats_,
            self.time_d,
        )
        result.save(self.tmpdir)
        Analysis(self.tmpdir).start()  # output stats

    def infer(self, typ, dinvs, f):
        assert typ in {self.EQTS, self.IEQS, self.MINMAX, self.PREPOSTS}, typ
        mlog.debug(f"infer '{typ}' at {len(self.locs)} locs")

        st = time.time()
        new_invs = f()  # get invs

        if new_invs.siz:
            et = time.time() - st
            self.time_d[typ] = et
            mlog.info(f"found {new_invs.siz} {typ} ({et:.2f}s)")

            dinvs.merge(new_invs)
            mlog.debug(dinvs.__str__(print_stat=True, print_first_n=20))

    def infer_eqts(self, maxdeg, dtraces, inps):
        import infer.eqt

        solver = infer.eqt.Infer(self.symstates, self.prog)
        solver.use_rand_init = self.use_rand_init

        auto_deg = self.get_auto_deg(maxdeg)  # determine degree
        dinvs = solver.gen(auto_deg, dtraces, inps)
        return dinvs

    def infer_ieqs(self, dtraces, inps):
        import infer.opt
        return infer.opt.Ieq(self.symstates, self.prog).gen(dtraces)

    def infer_minmax(self, dtraces, inps):
        import infer.opt
        return infer.opt.MMP(self.symstates, self.prog).gen(dtraces)

    def infer_preposts(self, dinvs, dtraces):
        import infer.prepost
        return infer.prepost.Infer(self.symstates, self.prog).gen(dinvs, dtraces)

    def get_symbolic_states(self):
        symstates = data.symstates.SymStates(self.inp_decls, self.inv_decls)
        symstates.compute(
            self.symstatesmaker_cls,
            self.symexefile,
            self.mysrc.mainQ_name,
            self.mysrc.funname,
            self.mysrc.symexedir,
        )
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
            tracedir=self.mysrc.tracedir, funname=self.mysrc.funname
        )


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

        if test_tracefile:
            _, self.test_dtraces = DTraces.vread(test_tracefile)

    def start(self, seed, maxdeg):
        assert maxdeg is None or maxdeg >= 1, maxdeg

        super().start(seed, maxdeg)
        mlog.debug(f"got {self.dtraces.siz} traces\n{self.dtraces}")
        tasks = []
        for loc in self.dtraces:
            symbols = self.inv_decls[loc]
            traces = self.dtraces[loc]

            if symbols.array_only:
                if settings.DO_ARRAYS:
                    import infer.nested_array

                    def _f():
                        return infer.nested_array.Infer.gen_from_traces(traces)
                    tasks.append((loc, _f))
            else:
                if settings.DO_EQTS:
                    import infer.eqt
                    try:
                        autodeg
                    except NameError:
                        autodeg = self.get_auto_deg(maxdeg)

                    def _f():
                        return infer.eqt.Infer.gen_from_traces(autodeg, traces, symbols)
                    tasks.append((loc, _f))

                if settings.DO_IEQS:
                    import infer.opt

                    def _f():
                        return infer.opt.Ieq.gen_from_traces(traces, symbols)
                    tasks.append((loc, _f))

        def f(tasks):
            rs = [(loc, _f()) for loc, _f in tasks]
            return rs

        wrs = MP.run_mp("(pure) dynamic inference", tasks, f, settings.DO_MP)

        dinvs = DInvs()
        for loc, invs in wrs:
            for inv in invs:
                dinvs.add(loc, inv)

        try:
            new_traces = self.dtraces.merge(self.test_dtraces)
            mlog.debug(f"added {new_traces.siz} test traces")
        except AttributeError:
            pass  # no test traces

        dinvs = self.sanitize(dinvs, self.dtraces)
        print(dinvs)
