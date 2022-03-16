import abc
import pdb
import random
import time
from pathlib import Path
import settings
import sys

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

mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class Dig(metaclass=abc.ABCMeta):
    EQTS = "eqts"
    IEQS = "ieqs"
    MINMAX = "minmax"
    CONGRUENCE = "congruence"
    PREPOSTS = "preposts"

    def __init__(self, filename):
        mlog.info(f"analyzing '{filename}'")
        self.filename = filename
        self.time_d = {}  # time results

    @abc.abstractmethod
    def start(self, seed, maxdeg: int):
        self.seed = seed
        random.seed(seed)
        mlog.debug(
            f"set seed to {seed} "
            f"(test {random.randint(0, 100)})"
        )

    def get_auto_deg(self, maxdeg):
        maxvars = max(self.inv_decls.values(), key=len)
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

    def __init__(self, filename):
        super().__init__(filename)

    def start(self, seed, maxdeg):

        if not(maxdeg is None or maxdeg >= 1):
            raise ValueError(f"maxdeg has invalid value {maxdeg}")

        super().start(seed, maxdeg)

        assert settings.TMPDIR.is_dir()
        import tempfile

        prefix = hash(self.seed)
        self.tmpdir = Path(
            tempfile.mkdtemp(dir=settings.TMPDIR, prefix=f"dig_{prefix}_")
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

            dinvs = digtraces.start(self.seed, maxdeg)

        else:  #use symbolic states
            st = time.time()
            self.symstates = self.get_symbolic_states()
            et = time.time() - st
            self.time_d["symbolic_states"] = et

            self.locs = self.prog.locs
            # remove locations with no symbolic states
            for loc in list(self.prog.locs):
                if loc not in self.symstates:
                    mlog.warning(f"{loc}: no symbolic states. Skip")
                    self.inv_decls.pop(loc)
            
            mlog.info(f"got symbolic states in {et:.2f}s")

            tasks = []
            if settings.DO_EQTS:
                def f():
                    return self._infer(self.EQTS, lambda: self._infer_eqts(maxdeg))
                tasks.append(f)

            if settings.DO_IEQS:
                def f():
                    return self._infer(self.IEQS, self._infer_ieqs)
                tasks.append(f)

            if settings.DO_MINMAXPLUS:
                def f():
                    return self._infer(self.MINMAX, self._infer_minmax)
                tasks.append(f)

            def f(tasks):
                rs = [_f() for _f in tasks]
                return rs

            wrs = MP.run_mp("symbolic inference", tasks, f, settings.DO_MP)

            dinvs = infer.inv.DInvs()
            dtraces = data.traces.DTraces.mk(self.locs)

            for typ, (dinvs_, dtraces_), et in wrs:
                self.time_d[typ] = et
                dinvs.merge(dinvs_)
                if dtraces_:
                    dtraces.merge(dtraces_)

            dinvs = self.sanitize(dinvs, dtraces)

            self.time_d["total"] = time.time() - st
            self.cleanup(dinvs, dtraces)

        if settings.WRITE_VTRACES:
            tracefile = Path(settings.WRITE_VTRACES)
            dtraces.vwrite(self.inv_decls, tracefile)
            mlog.info(f"{dtraces.siz} traces written to {tracefile}")

        print(f"tmpdir: {self.tmpdir}")
        return dinvs

    def cleanup(self, dinvs, dtraces):
        """
        Save and analyze result
        Clean up tmpdir
        """
        # clean up
        # import shutil
        # shutil.rmtree(self.tmpdir_del)

        # analyze and save results
        from analysis import Result, Analysis

        result = Result(
            self.filename,
            self.seed,
            dinvs,
            dtraces,
            self.symstates.solver_stats_,
            self.time_d,
        )
        result.save(self.tmpdir)
        Analysis(self.tmpdir).start()  # output stats

    def _infer(self, typ, f):
        assert typ in {self.EQTS, self.IEQS, self.MINMAX,
                       self.CONGRUENCE, self.PREPOSTS}, typ
        mlog.debug(f"infer '{typ}' at {len(self.locs)} locs")

        st = time.time()

        dinvs, dtraces = f()  # get invs
        et = time.time() - st
        if dinvs.siz:
            mlog.info(f"got {dinvs.siz} {typ} in {et:.2f}s")
            mlog.debug(dinvs.__str__(print_stat=True, print_first_n=20))

        return typ, (dinvs, dtraces),  et

    def _infer_eqts(self, maxdeg):
        dinvs, dtraces = infer.eqt.Infer(
            self.symstates, self.prog).gen(self.get_auto_deg(maxdeg))
        return dinvs, dtraces

    def _infer_ieqs(self):
        return infer.oct.Infer(self.symstates, self.prog).gen(), None

    def _infer_minmax(self):
        return infer.mp.Infer(self.symstates, self.prog).gen(), None

    def get_symbolic_states(self):
        symstates = data.symstates.SymStates(self.inp_decls, self.inv_decls)

        if settings.READ_SSTATES:
            sstatesfile = Path(settings.READ_SSTATES)
            symstates.vread(sstatesfile)
            mlog.info(f"symstates read from '{sstatesfile}'")
        else:
            symstates.compute(
                self.symstatesmaker_cls,
                self.symexefile,
                self.mysrc.mainQ_name,
                self.mysrc.funname,
                self.mysrc.symexedir,
            )
            mlog.info(
                f"got {symstates.siz} symstates for {len(symstates)} locs"
            )

            if settings.WRITE_SSTATES:
                sstatesfile = Path(settings.WRITE_SSTATES)
                symstates.vwrite(sstatesfile)
                mlog.info(f"symstates written to '{sstatesfile}'")
                sys.exit(0)

        return symstates


class DigSymStatesJava(DigSymStates):
    mysrc_cls = data.prog.Java
    symstatesmaker_cls = data.symstates.SymStatesMakerJava

    @property
    def symexefile(self):
        return self.filename

    @property
    def exe_cmd(self):
        return settings.Java.JAVA_RUN(
            tracedir=self.mysrc.tracedir, funname=self.mysrc.funname
        )


class DigSymStatesC(DigSymStates):
    mysrc_cls = data.prog.C
    symstatesmaker_cls = data.symstates.SymStatesMakerC

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
        mlog.info(
            f"got {self.dtraces.siz} traces over {len(self.dtraces)} locs")
        mlog.debug(f"{self.dtraces}")

        tasks = (self._nested_arrays_tasks() + self._eqts_tasks(maxdeg) + self._ieqs_tasks() +
                 self._minmax_tasks() + self._congruences_tasks())

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

    def _nested_arrays_tasks(self):
        def _f(l):
            return infer.nested_array.Infer.gen_from_traces(self.dtraces[l])

        def _g(l):
            return self.inv_decls[l].array_only
        return self._mk_tasks(settings.DO_ARRAYS, _g,  _f)

    def _eqts_tasks(self, maxdeg):
        autodeg = self.get_auto_deg(maxdeg)

        def _f(l):
            return infer.eqt.Infer.gen_from_traces(autodeg, self.dtraces[l], self.inv_decls[l])

        def _g(l):
            return not self.inv_decls[l].array_only
        return self._mk_tasks(settings.DO_EQTS, _g, _f)

    def _ieqs_tasks(self):
        def _f(l):
            return infer.oct.Infer.gen_from_traces(self.dtraces[l], self.inv_decls[l])

        def _g(l):
            return not self.inv_decls[l].array_only
        return self._mk_tasks(settings.DO_IEQS, _g,  _f)

    def _minmax_tasks(self):
        def _f(l):
            return infer.mp.Infer.gen_from_traces(self.dtraces[l], self.inv_decls[l])

        def _g(l):
            return not self.inv_decls[l].array_only
        return self._mk_tasks(settings.DO_MINMAXPLUS, _g, _f)

    def _congruences_tasks(self):
        def _f(l):
            return infer.congruence.Infer.gen_from_traces(self.dtraces[l], self.inv_decls[l])

        def _g(l):
            return not self.inv_decls[l].array_only
        return self._mk_tasks(settings.DO_CONGRUENCES, _g,  _f)

    def _mk_tasks(self, cond1, cond2, _f):
        if not cond1:
            return []
        return [(loc, _f) for loc in self.dtraces if cond2(loc)]

    @classmethod
    def mk(cls, tracefile, test_tracefile):
        assert tracefile.is_file(), tracefile
        assert test_tracefile is None or test_tracefile.is_file()

        inv_decls, dtraces = data.traces.DTraces.vread(tracefile)

        test_dtraces = None
        if test_tracefile:
            _, test_dtraces = data.traces.DTraces.vread(test_tracefile)

        return cls(tracefile, inv_decls, dtraces, test_dtraces)
