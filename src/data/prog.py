"""
Modelling a program, including running the program on inputs and 
collecting traces
"""

import abc
import shlex
import itertools
import random
from pathlib import Path
import pdb
from collections import namedtuple
import subprocess

import sympy

import settings
from helpers.miscs import MP
from helpers.z3utils import Z3
import helpers.vcommon as CM

import data.traces

from beartype import beartype
from beartype.typing import Set, Tuple, List

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)

class Symb(namedtuple("Symb", ("name", "typ"))):
    """
    Symbolic variable and its type,
    e.g., (x, 'I') means x is an integer
    """

    @property
    def is_array(self):
        return self.typ == "array"

    @property
    def is_real(self):
        return self.typ in {"D", "F"}

    @beartype
    def __str__(self) -> str:
        return f"{self.typ} {self.name}"

    @property
    def symbolic(self):
        try:
            ret = self._symbolic
            return ret
        except AttributeError:
            self._symbolic = sympy.Symbol(self.name)
            return self._symbolic

    @property
    def expr(self):
        try:
            ret = self._expr
            return ret
        except AttributeError:
            self._expr = Z3.parse(str(self.symbolic))
            return self._expr


class Symbs(tuple):
    def __new__(cls, ss):
        assert ss, ss
        assert all(isinstance(s, Symb) for s in ss), ss
        return super(Symbs, cls).__new__(cls, ss)

    def __str__(self):
        return "; ".join(map(str, self))

    @property
    def array_only(self):
        return all(s.is_array for s in self)

    @property
    def names(self):
        return tuple(s.name for s in self)

    @property
    def typs(self):
        return tuple(s.typ for s in self)

    @property
    def symbolic(self):
        return tuple(s.symbolic for s in self)
 
    @property
    def exprs(self):
        try:
            ret = self._exprs
            return ret
        except AttributeError:
            self._exprs = [s.expr for s in self]
            return self._exprs 


    @classmethod
    def mk(cls, ls):
        """
        I x , D y .. ->  {x: int, y: double}

        x , y .. ->  {x: int, y: double}
        """
        assert isinstance(ls, list), ls
        symbs = []
        for x in ls:
            x = x.strip()
            if not x:
                continue
            vs = x.split()
            assert len(vs) == 2, vs  # I, x
            t, k = vs[0], vs[1]
            symbs.append(Symb(k, t))
        return cls(symbs)


# inv_decls = {loc: Symbs}
class DSymbs(dict):
    pass

class Prog:
    @beartype
    def __init__(self, exe_cmd:str, inp_decls:Symbs, inv_decls:DSymbs) -> None:
        self.exe_cmd = exe_cmd
        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self._cache = {}  # inp -> traces (str)

    @beartype
    @property
    def locs(self): 
        return self.inv_decls.keys()

    # PUBLIC METHODS
    
    @beartype
    def get_traces(self, inps: data.traces.Inps) -> data.traces.DTraces:
        """
        front end to obtain traces from inps
        """
        traces = self._get_traces_mp(inps)
        traces = itertools.chain.from_iterable(traces.values())
        traces = data.traces.DTraces.parse(traces, self.inv_decls)
        assert all(loc in self.inv_decls for loc in traces), traces.keys()
        return traces

    @beartype
    def gen_rand_inps(self, n_needed:int=1) -> Set[Tuple]:
        assert n_needed >= 1, n_needed
        try:
            valid_ranges = self._valid_ranges
            inps = set()
        except AttributeError:
            valid_ranges, inps = self._get_valid_inp_ranges()
            self._valid_ranges = valid_ranges

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
    @beartype
    def _get_traces(self, inp:data.traces.Inp) -> List[str]:
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
            my_inp = data.traces.Inp(self.inp_decls.names, inp)
            dr[my_inp] = inp_range
            di[my_inp] = inp

        my_inps = data.traces.Inps(di.keys())
        mytraces = self._get_traces_mp(my_inps)

        valid_ranges, valid_inps = set(), set()
        for my_inp in mytraces:
            if mytraces[my_inp]:
                valid_ranges.add(dr[my_inp])
                valid_inps.add(di[my_inp])
            else:
                mlog.debug(f"inp range {dr[my_inp]} invalid")

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



class Src(metaclass=abc.ABCMeta):

    @beartype
    def __init__(self, filename:Path, tmpdir:Path) -> None:
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

    @abc.abstractmethod
    def check(self, filename, tmpdir):
        pass

    @classmethod
    def parse_type_info(cls, msg):
        # vtrace2; I x; I y; I q; I r
        # vtrace1; I q; I r; I a; I b; I x; I y
        # mainQ_cohendiv; I x; I y,
        
        mainQ_name = None
        inp_decls = None
        inv_decls = []

        for l in msg.split("\n"):
            if not (settings.MAINQ_FUN in l or settings.TRACE_INDICATOR in l):
                continue
            contents = l.split(';')  # ['vtraceX', 'I x', 'I y']

            symbs = Symbs.mk(contents[1:])
            if contents[0].startswith(settings.MAINQ_FUN):
                mainQ_name = contents[0]
                inp_decls = symbs
            else:
                assert contents[0].startswith(
                    settings.TRACE_INDICATOR), contents
                inv_decls.append((contents[0], symbs))
        inv_decls = DSymbs(inv_decls)

        return inp_decls, inv_decls, mainQ_name,

    def mkdir(self, d):
        assert not d.exists(), d
        d.mkdir()
        return d


class Java(Src):
    instrument_cmd = settings.Java.INSTRUMENT

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


class C(Src):
    instrument_cmd = settings.C.INSTRUMENT

    @beartype
    def __init__(self, filename:Path, tmpdir:Path) -> None:
        super().__init__(filename, tmpdir)

        self.traceexe = self.tracefile.with_suffix(".exe")
        self._compile_test(self.tracefile, self.traceexe)

    @beartype
    def check(self, filename:Path, tmpdir:Path) -> Tuple[Path,Path,str]:
        basename = Path(filename.name)
        funname = basename.stem
        self._compile_test(filename, tmpdir / f"{funname}.exe")
        return filename, basename, funname

    @beartype
    @classmethod
    def _compile_test(cls, filename:Path, out:Path) -> None:
        cmd = settings.C.COMPILE(filename=filename, tmpfile=out)
        subprocess.run(shlex.split(cmd), check=True)
        assert out.is_file(), out


