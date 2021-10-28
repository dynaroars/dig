import abc
import itertools
import pdb
import random
import time
from pathlib import Path
import settings

from helpers.miscs import Miscs, MP
import helpers.vcommon as CM

import data.prog
import data.symstates
import data.traces

import infer.inv
import infer.nested_array
import infer.eqt
import infer.oct
import infer.mp
import infer.congruence

DBG = pdb.set_trace

mlog = CM.getLogger(__name__, settings.logger_level)


class Dig(metaclass=abc.ABCMeta):
    def __init__(self, filename):
        mlog.info(f"analyzing '{filename}'")
        self.filename = filename
        self.time_d = {}  # time results

    def doit(seed, maxdeg: int) -> infer.inv.DInvs:
        pass

    @abc.abstractmethod
    def start(self, seed, maxdeg: int):
        self.seed = seed
        random.seed(seed)
        mlog.debug(
            f"set seed to {seed} "
            f"(test {random.randint(0, 100)})"
        )

    def get_auto_deg(self, maxdeg):
        maxvars = max(self.inv_decls.values(), key=lambda d: len(d))
        deg = Miscs.get_auto_deg(maxdeg, len(maxvars), settings.MAX_TERM)
        return deg

    def sanitize(self, dinvs, dtraces):
        if not dinvs.siz:
            return dinvs

        msg = f"check {dinvs.siz} invs using {dtraces.siz} traces"
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
            mlog.debug(dinvs.__str__(print_stat=False, print_first_n=20))
            st1 = time.time()
            dinvs = dinvs.simplify()
            mlog.info(f"{msg} ({time.time() - st1:.2f}s)")

        self.time_d["simplify"] = time.time() - st

        return dinvs


class DigSymStates(Dig, metaclass=abc.ABCMeta):
    EQTS = "eqts"
    IEQS = "ieqs"
    MINMAX = "minmax"
    CONGRUENCE = "congruence"
    PREPOSTS = "preposts"

    def __init__(self, filename):
        super().__init__(filename)

    def start(self, seed, maxdeg):

        if not(maxdeg is None or maxdeg >= 1):
            raise ValueError(f"maxdeg has invalid value {maxdeg}")

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

        if not settings.DO_SS:  # use traces from running the program on random inputs
            rinps = self.prog.gen_rand_inps(n_needed=settings.N_RAND_INPS)
            inps = data.traces.Inps().merge(rinps, self.inp_decls.names)
            mlog.debug(f"gen {len(inps)} random inps")
            if not inps:
                return

            assert isinstance(inps, data.traces.Inps), inps
            dtraces = self.prog.get_traces(inps)
            if not dtraces:
                return

            digtraces = DigTraces(
                self.filename, self.inv_decls, dtraces, test_dtraces=None)

            digtraces.start(self.seed, maxdeg)
            return

        st = time.time()
        self.symstates = self.get_symbolic_states()
        et = time.time() - st
        self.locs = self.inv_decls.keys()
        mlog.info(
            f"got symbolic states at {len(self.locs)} locs: ({et:.2f}s)"
        )

        self.time_d["symbolic_states"] = et

        # remove locations with no symbolic states
        for loc in list(self.inv_decls.keys()):
            if loc not in self.symstates:
                mlog.warning(f"{loc}: no symbolic states. Skip")
                self.inv_decls.pop(loc)

        dinvs = infer.inv.DInvs()
        dtraces = data.traces.DTraces.mk(self.locs)
        inps = data.traces.Inps()

        if settings.DO_EQTS:
            self._infer(self.EQTS, dinvs,
                        lambda: self._infer_eqts(maxdeg, dtraces, inps))

        if settings.DO_CONGRUENCES:
            self._infer(self.CONGRUENCE, dinvs,
                        lambda: self._infer_congruence(dtraces, inps))

        if settings.DO_IEQS:
            self._infer(self.IEQS, dinvs,
                        lambda: self._infer_ieqs(dtraces))

        if settings.DO_MINMAXPLUS:
            self._infer(self.MINMAX, dinvs,
                        lambda: self._infer_minmax(dtraces))

        dinvs = self.sanitize(dinvs, dtraces)

        et = time.time() - st
        self.time_d["total"] = et

        self.cleanup(dinvs, dtraces, inps)

        if settings.WRITE_VTRACES:
            tracefile = self.tmpdir/"alltraces.csv"
            dtraces.vwrite(self.inv_decls, tracefile)
            mlog.info(f"traces written to {tracefile}")

        print(f"tmpdir: {self.tmpdir}")
        return dinvs

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

    def _infer(self, typ, dinvs, f):
        assert typ in {self.EQTS, self.IEQS, self.MINMAX,
                       self.CONGRUENCE, self.PREPOSTS}, typ
        mlog.debug(f"infer '{typ}' at {len(self.locs)} locs")

        st = time.time()
        new_invs = f()  # get invs

        if new_invs.siz:
            et = time.time() - st
            self.time_d[typ] = et
            mlog.info(f"found {new_invs.siz} {typ} ({et:.2f}s)")

            dinvs.merge(new_invs)
            mlog.debug(dinvs.__str__(print_stat=True, print_first_n=20))

    def _infer_eqts(self, maxdeg, dtraces, inps):
        solver = infer.eqt.Infer(self.symstates, self.prog)

        auto_deg = self.get_auto_deg(maxdeg)  # determine degree

        dinvs = solver.gen(auto_deg, dtraces, inps)
        return dinvs

    def _infer_ieqs(self, dtraces):
        return infer.oct.Infer(self.symstates, self.prog).gen(dtraces)

    def _infer_minmax(self, dtraces):
        return infer.mp.Infer(self.symstates, self.prog).gen(dtraces)

    def _infer_congruence(self, dtraces, inps):
        return infer.congruence.Infer(self.symstates, self.prog).gen(dtraces, inps)

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
    def __init__(self, filename, inv_decls, dtraces, test_dtraces):
        super().__init__(filename)

        self.inv_decls = inv_decls
        self.dtraces = dtraces
        if test_dtraces:
            self.test_dtraces = test_dtraces

    def start(self, seed, maxdeg):
        assert maxdeg is None or maxdeg >= 1, maxdeg

        super().start(seed, maxdeg)
        mlog.debug(f"got {self.dtraces.siz} traces\n{self.dtraces}")

        # run everything in parallel
        tasks = []
        for loc in self.dtraces:
            if self.inv_decls[loc].array_only:
                if settings.DO_ARRAYS:
                    # import infer.nested_array

                    def _f(l):
                        return infer.nested_array.Infer.gen_from_traces(self.dtraces[l])
                    tasks.append((loc, _f))
            else:
                if settings.DO_EQTS:
                    try:
                        autodeg
                    except NameError:
                        autodeg = self.get_auto_deg(maxdeg)

                    def _f(l):
                        return infer.eqt.Infer.gen_from_traces(autodeg, self.dtraces[l], self.inv_decls[l])
                    tasks.append((loc, _f))

                if settings.DO_IEQS:
                    def _f(l):
                        return infer.oct.Infer.gen_from_traces(self.dtraces[l], self.inv_decls[l])
                    tasks.append((loc, _f))

                if settings.DO_MINMAXPLUS:
                    def _f(l):
                        return infer.mp.Infer.gen_from_traces(self.dtraces[l], self.inv_decls[l])
                    tasks.append((loc, _f))

                if settings.DO_CONGRUENCES:
                    def _f(l):
                        return infer.congruence.Infer.gen_from_traces(self.dtraces[l], self.inv_decls[l])
                    tasks.append((loc, _f))

        def f(tasks):
            rs = [(loc, _f(loc)) for loc, _f in tasks]
            return rs

        wrs = MP.run_mp("(pure) dynamic inference", tasks, f, settings.DO_MP)

        dinvs = infer.inv.DInvs()
        for loc, invs in wrs:
            for inv in invs:
                dinvs.add(loc, inv)

        try:
            new_traces = self.dtraces.merge(self.test_dtraces)
            mlog.debug(f"added {new_traces.siz} test traces")
        except AttributeError:
            pass  # no test traces

        dinvs = self.sanitize(dinvs, self.dtraces)
        return dinvs

    # @classmethod
    # def infer_tasks(dtraces, inv_decls, cond, f) -> list:
    #     return [(loc, _f) for loc in dtraces if cond]

    # @classmethod
    # def infer_nested_array_tasks(dtraces, inv_decls) -> list:
    #     tasks = []
    #     for loc in dtraces:
    #         if inv_decls[loc].array_only and settings.DO_ARRAYS:
    #             import infer.nested_array

    #             def _f(l):
    #                 return infer.nested_array.Infer.gen_from_traces(dtraces[l])
    #             tasks.append((loc, _f))
    #     return tasks

    # @classmethod
    # def infer_eqt_tasks(cls, dtraces, inv_decls) -> None:
    #     tasks = []
    #     if not settings.DO_EQTS:
    #         return tasks

    #     try:
    #         autodeg
    #     except NameError:
    #         autodeg = cls.get_auto_deg(inv_decls, maxdeg)

    #     import infer.eqt

    #     def _f(l):
    #         return infer.eqt.Infer.gen_from_traces(autodeg, dtraces[l], inv_decls[l])

    #     return [(loc, _f) for loc in dtraces if not inv_decls[loc].array_only]

    # @classmethod
    # def infer_ieq_tasks(cls, dtraces, inv_decls) -> None:
    #     def _f(l):
    #         return infer.oct.Infer.gen_from_traces(dtraces[l], inv_decls[l])

    #     return cls.infer_tasks(dtraces, inv_decls, not)

    #     return [(loc, _f) for loc in dtraces if not inv_decls[loc].array_only]

    # @classmethod
    # def infer_minmaxplus_tasks(cls, dtraces, inv_decls) -> None:
    #     tasks = []
    #     if not settings.DO_MINMAXPLUS:
    #         return tasks

    #     import infer.mp
    #     for loc in dtraces:
    #         if not inv_decls[loc].array_only:

    #             def _f(l):
    #                 return infer.mp.Infer.gen_from_traces(dtraces[l], inv_decls[l])
    #             tasks.append((loc, _f))
    #     return tasks

    # @classmethod
    # def infer_congruence_tasks(cls, dtraces, inv_decls) -> None:
    #     tasks = []
    #     if not settings.DO_CONGRUENCES:
    #         return tasks

    #     import infer.congruence
    #     for loc in dtraces:
    #         if not inv_decls[loc].array_only:
    #             def _f(l):
    #                 return infer.congruence.Infer.gen_from_traces(self.dtraces[l], self.inv_decls[l])
    #             tasks.append((loc, _f))

    #     return tasks

    # @classmethod
    # def infer_ieqs_tasks(cls, dtraces, inv_decls) -> None:
    #     tasks = []
    #     for loc in dtraces:
    #         if not inv_decls[loc].array_only and settings.DO_EQTS:

    @classmethod
    def mk(cls, tracefile, test_tracefile):
        assert tracefile.is_file(), tracefile
        assert test_tracefile is None or test_tracefile.is_file()

        inv_decls, dtraces = data.traces.DTraces.vread(tracefile)

        test_dtraces = None
        if test_tracefile:
            _, test_dtraces = data.traces.DTraces.vread(test_tracefile)

        return cls(tracefile, inv_decls, dtraces, test_dtraces)
