import itertools
import random
import pdb
from collections import namedtuple
import sage.all

import settings
import helpers.vcommon as CM
from helpers.miscs import Miscs, Z3
from data.traces import Inp, Inps, DTraces

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Prog(object):
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
        assert isinstance(inps, Inps), inps

        traces = self._get_traces_mp(inps)
        traces = itertools.chain.from_iterable(traces.itervalues())
        traces = DTraces.parse(traces, self.inv_decls)
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

        if not inps:
            while len(inps) < n_needed:
                old_siz = len(inps)
                for inp_range in valid_ranges:
                    myinp = self._get_inp_from_range(inp_range)
                    inps.add(myinp)

                if len(inps) == old_siz:
                    mlog.warn("can't gen new random inps")
                    break
        return inps

    # PRIVATE METHODS
    def _get_traces(self, inp):
        assert isinstance(inp, Inp), inp

        inp_ = (v if isinstance(v, int) or v.is_integer() else v.n()
                for v in inp.vs)
        inp_ = ' '.join(map(str, inp_))
        cmd = "{} {}".format(self.exe_cmd, inp_)
        mlog.debug(cmd)
        traces, _ = CM.vcmd(cmd)
        traces = traces.splitlines()
        return traces

    def _get_traces_mp(self, inps):
        """
        run program on inps and obtain traces in parallel
        return {inp: traces}
        """
        assert isinstance(inps, Inps), inps

        tasks = [inp for inp in inps if inp not in self._cache]

        def f(tasks):
            return [(inp, self._get_traces(inp)) for inp in tasks]
        wrs = Miscs.run_mp("get traces", tasks, f)

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
            myInp = Inp(self.inp_decls.names, inp)
            dr[myInp] = inp_range
            di[myInp] = inp

        myInps = Inps(di.keys())
        mytraces = self._get_traces_mp(myInps)

        valid_ranges, valid_inps = set(), set()
        for myInp in mytraces:
            if mytraces[myInp]:
                valid_ranges.add(dr[myInp])
                valid_inps.add(di[myInp])
            else:
                mlog.debug("inp range {} invalid".format(dr[myInp]))

        return valid_ranges, valid_inps

    @classmethod
    def _get_inp_from_range(cls, inp_range):
        return tuple(random.randrange(ir[0], ir[1]) for ir in inp_range)

    @classmethod
    def _get_inp_ranges(cls, n_inps):
        small = 0.10
        large = 1 - small
        maxV = settings.INP_MAX_V
        minV = -1 * maxV
        rinps = [(0, int(maxV * small)),
                 (int(maxV * large), maxV),
                 (int(minV * small), 0),
                 (minV, int(minV * large))]

        if n_inps <= settings.INP_RANGE_V:
            # consider some ranges for smaller #'s of inps
            tiny = 0.05
            rinps.extend([(0, int(maxV * tiny)),
                          (int(minV * tiny), 0)])

        # [((0, 30), (0, 30)), ((0, 30), (270, 300)), ...]
        rinps = itertools.product(*itertools.repeat(rinps, n_inps))
        return rinps


class Symb(namedtuple('Symb', ('name', 'typ'))):
    """
    Symbolic variable and its type,
    e.g., (x, 'I') means x is an integer
    """
    @property
    def is_real(self):
        try:
            return self._is_real
        except AttributeError:
            self._is_real = self.typ in {'D', 'F'}
            return self._is_real

    def __str__(self):
        return "{} {}".format(self.typ, self.name)

    @property
    def sageExpr(self):
        try:
            return self._sageExpr
        except AttributeError:
            self._sageExpr = sage.all.var(self.name)
            return self._sageExpr

    def expr(self, use_reals):
        try:
            return self._expr
        except AttributeError:
            self._expr = Z3.toZ3(self.sageExpr, use_reals, use_mod=False)
            return self._expr


class Symbs(tuple):
    def __new__(cls, ss):
        assert ss, ss
        assert all(isinstance(s, Symb) for s in ss), ss
        return super(Symbs, cls).__new__(cls, ss)

    def __str__(self):
        return ", ".join(map(str, self))

    @property
    def names(self): return tuple(s.name for s in self)

    @property
    def typs(self): return tuple(s.typ for s in self)

    @property
    def sageExprs(self): return tuple(s.sageExpr for s in self)

    def exprs(self, use_reals):
        try:
            return self._exprs
        except AttributeError:
            self._exprs = [s.expr(use_reals) for s in self]
            return self._exprs

    @classmethod
    def mk(cls, s):
        """
        I x , D y .. ->  {x: int, y: double}
        """
        assert isinstance(s, str), s

        cs = (x.split() for x in s.split(',') if x.strip())
        symbs = [Symb(k.strip(), t.strip()) for t, k in cs]
        return cls(symbs)

# inv_decls = {loc: Symbs}


class DSymbs(dict):
    @property
    def use_reals(self):
        try:
            return self._use_reals
        except AttributeError:
            self._use_reals = any(
                s.is_real for syms in self.itervalues() for s in syms)
            return self._use_reals
