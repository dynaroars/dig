import shlex
import itertools
import random
from pathlib import Path
import pdb
from collections import namedtuple
import subprocess

import sage.all

import settings
from helpers.miscs import MP
from helpers.z3utils import Z3
import helpers.vcommon as CM

import data.traces

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Prog:
    def __init__(self, exe_cmd, inp_decls, inv_decls):
        assert isinstance(exe_cmd, str), exe_cmd
        assert isinstance(inp_decls, Symbs), inp_decls  # I x, I y
        assert isinstance(inv_decls, DSymbs), inv_decls

        self.exe_cmd = exe_cmd
        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self._cache = {}  # inp -> traces (str)

    # PUBLIC METHODS
    def get_traces(self, inps):
        """
        front end to obtain traces from inps
        """
        assert isinstance(inps, data.traces.Inps), inps

        traces = self._get_traces_mp(inps)
        traces = itertools.chain.from_iterable(traces.values())
        traces = data.traces.DTraces.parse(traces, self.inv_decls)
        assert all(loc in self.inv_decls for loc in traces), traces.keys()
        return traces

    def gen_rand_inps(self, n_needed=1):
        assert n_needed >= 1, n_needed
        try:
            valid_ranges = self._valid_ranges
            inps = set()
        except AttributeError:
            mlog.debug("compute valid input ranges")
            valid_ranges, inps = self._get_valid_inp_ranges()
            self._valid_ranges = valid_ranges

        if inps:
            return inps

        while len(inps) < n_needed:
            old_siz = len(inps)
            for inp_range in valid_ranges:
                myinp = self._get_inp_from_range(inp_range)
                inps.add(myinp)

            if len(inps) == old_siz:
                mlog.debug(f"can't gen new rand inps (current {len(inps)})")
                break
        return inps

    # PRIVATE METHODS
    def _get_traces(self, inp):
        assert isinstance(inp, data.traces.Inp), inp

        inp_ = (v if isinstance(v, int) or v.is_integer() else v.n()
                for v in inp.vs)
        inp_ = " ".join(map(str, inp_))
        cmd = f"{self.exe_cmd} {inp_}"
        mlog.debug(cmd)

        # do not check cmd status, could get error status due to incorrect input
        cp = subprocess.run(shlex.split(cmd), capture_output=True, text=True)
        traces = cp.stdout.splitlines()
        return traces

    def _get_traces_mp(self, inps):
        """
        run program on inps and obtain traces in parallel
        return {inp: traces}
        """
        assert isinstance(inps, data.traces.Inps), inps

        tasks = [inp for inp in inps if inp not in self._cache]

        def f(tasks):
            return [(inp, self._get_traces(inp)) for inp in tasks]

        wrs = MP.run_mp("get traces", tasks, f, settings.DO_MP)

        for inp, traces in wrs:
            assert inp not in self._cache
            self._cache[inp] = traces

        return {inp: self._cache[inp] for inp in inps}

    def _get_valid_inp_ranges(self):

        dr = {}  # Inp => range
        di = {}  # Inp => inp
        inp_ranges = self._get_inp_ranges(len(self.inp_decls))
        for inp_range in inp_ranges:
            inp = self._get_inp_from_range(inp_range)
            myInp = data.traces.Inp(self.inp_decls.names, inp)
            dr[myInp] = inp_range
            di[myInp] = inp

        myInps = data.traces.Inps(di.keys())
        mytraces = self._get_traces_mp(myInps)

        valid_ranges, valid_inps = set(), set()
        for myInp in mytraces:
            if mytraces[myInp]:
                valid_ranges.add(dr[myInp])
                valid_inps.add(di[myInp])
            else:
                mlog.debug(f"inp range {dr[myInp]} invalid")

        return valid_ranges, valid_inps

    @classmethod
    def _get_inp_from_range(cls, inp_range):
        return tuple(random.randrange(ir[0], ir[1]) for ir in inp_range)

    @classmethod
    def _get_inp_ranges(cls, n_inps):
        small = 0.10
        large = 1 - small
        maxV = settings.INP_MAX_V
        rinps = [(0, int(maxV * small)), (int(maxV * large), maxV)]
        if n_inps <= settings.INP_RANGE_V:
            # consider some ranges for smaller #'s of inps
            tiny = 0.05
            rinps.extend([(0, int(maxV * tiny))])

        # [((0, 30), (0, 30)), ((0, 30), (270, 300)), ...]
        rinps_i = itertools.product(*itertools.repeat(rinps, n_inps))
        return rinps_i


class Symb(namedtuple("Symb", ("name", "typ"))):
    """
    Symbolic variable and its type,
    e.g., (x, 'I') means x is an integer
    """

    @property
    def is_real(self):
        try:
            return self._is_real
        except AttributeError:
            self._is_real = self.typ in {"D", "F"}
            return self._is_real

    def __str__(self):
        return f"{self.typ} {self.name}"

    @property
    def sageExpr(self):
        try:
            return self._sageExpr
        except AttributeError:
            self._sageExpr = sage.all.var(self.name)
            return self._sageExpr

    @property
    def expr(self):
        try:
            return self._expr
        except AttributeError:
            self._expr = Z3.parse(str(self.sageExpr))
            return self._expr


class Symbs(tuple):
    def __new__(cls, ss):
        assert ss, ss
        assert all(isinstance(s, Symb) for s in ss), ss
        return super(Symbs, cls).__new__(cls, ss)

    def __str__(self):
        return ", ".join(map(str, self))

    @property
    def names(self):
        return tuple(s.name for s in self)

    @property
    def typs(self):
        return tuple(s.typ for s in self)

    @property
    def sageExprs(self):
        return tuple(s.sageExpr for s in self)

    @property
    def exprs(self):
        try:
            return self._exprs
        except AttributeError:
            self._exprs = [s.expr for s in self]
            return self._exprs

    @classmethod
    def mk(cls, s):
        """
        I x , D y .. ->  {x: int, y: double}
        """
        assert isinstance(s, str), s

        cs = (x.split() for x in s.split(",") if x.strip())
        symbs = [Symb(k.strip(), t.strip()) for t, k in cs]
        return cls(symbs)


# inv_decls = {loc: Symbs}


class DSymbs(dict):
    pass


class Src:
    def __init__(self, filename, tmpdir):
        assert filename.is_file(), filename
        assert tmpdir.is_dir(), tmpdir

        filename, basename, funname = self.check(filename, tmpdir)

        tracedir = self.mkdir(tmpdir / settings.TRACE_DIR)
        tracefile = tracedir / basename
        symexedir = self.mkdir(tmpdir / settings.SYMEXE_DIR)
        symexefile = symexedir / basename

        cmd = self.instrument_cmd(
            filename=filename, tracefile=tracefile, symexefile=symexefile
        )
        try:
            cp = subprocess.run(
                shlex.split(cmd), capture_output=True, check=True, text=True
            )
        except subprocess.CalledProcessError as ex:
            ex_cmd = " ".join(ex.cmd)
            mlog.error(f"cmd '{ex_cmd}' gives error\n{ex.stderr}")
            raise

        inp_decls, inv_decls, mainQ_name = self.parse_type_info(cp.stdout)

        self.filename, self.basename, self.funname = filename, basename, funname
        self.tracedir, self.tracefile = tracedir, tracefile
        self.symexedir, self.symexefile = symexedir, symexefile
        self.inp_decls, self.inv_decls, self.mainQ_name = (
            inp_decls,
            inv_decls,
            mainQ_name,
        )

    def parse_type_info(self, msg):
        # vtrace2: I x, I y, I q, I r,
        # vtrace1: I q, I r, I a, I b, I x, I y,
        # mainQ_cohendiv: I x, I y,
        lines = [
            l.split(":")
            for l in msg.split("\n")
            if settings.MAINQ_FUN in l or settings.TRACE_INDICATOR in l
        ]

        lines = [(fun.strip(), Symbs.mk(sstyps)) for fun, sstyps in lines]

        # mainQ
        inp_decls = [
            (fun, symbs) for fun, symbs in lines if fun.startswith(settings.MAINQ_FUN)
        ]
        assert len(inp_decls) == 1

        inp_decls = inp_decls[0]
        mainQ_name, inp_decls = inp_decls[0], inp_decls[1]
        inv_decls = DSymbs(
            [
                (fun, symbs)
                for fun, symbs in lines
                if fun.startswith(settings.TRACE_INDICATOR)
            ]
        )

        return (
            inp_decls,
            inv_decls,
            mainQ_name,
        )

    def mkdir(self, d):
        assert not d.exists(), d
        d.mkdir()
        return d


class Java(Src):
    def check(self, filename, tmpdir):
        basename = Path(filename.name)  # c.class
        funname = basename.stem  # c

        if basename.suffix == ".java":
            cmd = settings.Java.COMPILE(filename=filename, tmpdir=tmpdir)
            try:
                cp = subprocess.run(
                    shlex.split(cmd), capture_output=True, check=True, text=True
                )
            except subprocess.CalledProcessError as ex:
                mlog.error(
                    "cmd '{}' gives error\n{}".format(
                        " ".join(ex.cmd), ex.stderr)
                )
                raise
            filename = (tmpdir / funname).with_suffix(".class")
            basename = Path(filename.name)

        return filename, basename, funname

    @property
    def instrument_cmd(self):
        return settings.Java.INSTRUMENT


class C(Src):
    def __init__(self, filename, tmpdir):
        super().__init__(filename, tmpdir)

        self.traceexe = self.tracefile.with_suffix(".exe")
        self.compile_test(self.tracefile, self.traceexe)

    def check(self, filename, tmpdir):
        basename = Path(filename.name)
        funname = basename.stem
        self.compile_test(filename, tmpdir / f"{funname}.exe")
        return filename, basename, funname

    @classmethod
    def compile_test(cls, filename, out):
        cmd = settings.C.COMPILE(filename=filename, tmpfile=out)
        subprocess.run(shlex.split(cmd), check=True)
        assert out.is_file(), out

    @property
    def instrument_cmd(self):
        return settings.C.INSTRUMENT
