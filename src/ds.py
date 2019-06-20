from abc import ABCMeta, abstractmethod
import itertools
import random
import pdb

import z3

import sage.all

import vcommon as CM
import settings
from miscs import Miscs, Z3

dbg = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)

"""
Data structures
"""


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
            valid_ranges, inps = self._get_valid_inp_ranges()
            self._valid_ranges = valid_ranges

        if not inps:
            while True:
                if len(inps) >= n_needed:
                    break

                for inp_range in valid_ranges:
                    inps.add(self._get_inp_from_range(inp_range))
        return inps

    # PRIVATE METHODS
    def _get_traces(self, inp):
        assert isinstance(inp, Trace), inp
        assert inp not in self._cache

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

        # mp doesn't like inp so have to use str
        mydict = {str(inp): inp for inp in inps}

        tasks = [inp for inp in inps if inp not in self._cache]

        def f(tasks):
            return [(str(inp), self._get_traces(inp)) for inp in tasks]
        wrs = Miscs.run_mp_simple("get traces", tasks, f, doMP=settings.doMP)

        for inp_str, traces in wrs:
            inp = mydict[inp_str]
            assert inp not in self._cache
            self._cache[inp] = traces

        return {inp: self._cache[inp] for inp in inps}

    def _get_valid_inp_ranges(self):

        dr = {}  # Inp => range
        di = {}  # Inp => inp
        inp_ranges = self._get_inp_ranges(len(self.inp_decls))
        for inp_range in inp_ranges:
            inp = self._get_inp_from_range(inp_range)
            myInp = Trace(self.inp_decls.names, inp)
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
                mlog.debug("inp range {} invalid".format(format(dr[myInp])))

        return valid_ranges, valid_inps

    @classmethod
    def _get_inp_from_range(cls, inp_range):
        return tuple(random.randrange(ir[0], ir[1]) for ir in inp_range)

    @classmethod
    def _get_inp_ranges(cls, n_inps):
        tiny = 0.05
        small = 0.10
        large = 1 - small
        maxV = DTraces.inpMaxV
        minV = -1 * maxV
        rinps = [(0, int(maxV * small)), (0, int(maxV * tiny)),
                 (int(maxV * large), maxV),
                 (int(minV * small), 0), (int(minV * tiny), 0),
                 (minV, int(minV * large))]

        # [((0, 30), (0, 30)), ((0, 30), (270, 300)), ...]
        rinps = list(itertools.product(*itertools.repeat(rinps, n_inps)))
        return rinps


class Symb(tuple):
    """
    Symbolic variable and its type, e.g., (x, 'I') means x is an integer
    """
    def __new__(cls, name, typ):
        assert isinstance(name, str), name
        assert isinstance(typ, str) and typ in {'D', 'F', 'I'}, typ
        return super(Symb, cls).__new__(cls, (name, typ))

    def __init__(self, name, typ):
        self.name = name
        self.typ = typ

    @property
    def isReal(self):
        try:
            return self._isReal
        except AttributeError:
            self._isReal = self.typ in {'D', 'F'}
            return self._isReal

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

    @staticmethod
    def mk(s):
        """
        double x , double y .. ->  {x: int, y: double}
        where x and y are SAGE's symbolic variables
        """
        assert isinstance(s, str), s
        cs = (x.split() for x in s.split(',') if x.strip())
        symbs = [Symb(k.strip(), t.strip()) for t, k in cs]
        cs = Symbs(symbs)
        return cs


# inv_decls = {loc: Symbs}
class DSymbs(dict):
    @property
    def use_reals(self):
        try:
            return self._use_reals
        except AttributeError:
            self._use_reals = any(
                s.isReal for syms in self.itervalues() for s in syms)
            return self._use_reals


class Trace(tuple):
    """"
    ((x, y), (3, 4))
    """
    maxVal = 100000000

    def __new__(cls, ss, vs):
        assert all(isinstance(s, str) for s in ss) and \
            isinstance(ss, tuple) and (vs, tuple) and \
            len(ss) == len(vs) and ss, (ss, vs)
        return super(Trace, cls).__new__(cls, (ss, vs))

    def __init__(self, ss, vs):
        assert all(isinstance(s, str) for s in ss) and \
            isinstance(ss, tuple) and (vs, tuple) and \
            len(ss) == len(vs) and ss, (ss, vs)

        self.ss = ss  # x,y,z
        self.vs = vs  # 1,2,3

    @property
    def mydict(self):
        # use for expression substitution
        try:
            return self._mydict
        except AttributeError:
            self._mydict = {sage.all.var(s): v for s, v
                            in zip(self.ss, self.vs) if "!" not in s}

            return self._mydict

    @property
    def mydict_str(self):
        # use for maxplus eval
        try:
            return self._mydict_str
        except AttributeError:
            self._mydict_str = {s: v for s, v in zip(self.ss, self.vs)
                                if "!" not in s}
            return self._mydict_str

    @classmethod
    def parse(cls, ss, vs):
        assert isinstance(ss, (tuple, list)), ss
        assert isinstance(vs, (tuple, list)), vs

        vs = tuple(Miscs.ratOfStr(t) for t in vs)
        return Trace(ss, vs)

    @classmethod
    def fromDict(cls, d):
        # {'y': 1, 'x': 2, 'r': 2, 'b': 2}
        ss = tuple(sorted(d))
        vs = tuple(d[s] for s in ss)
        return Trace(ss, vs)

    def myeval(self, expr):
        assert Miscs.is_expr(expr), expr
        rs = expr.subs(self.mydict)
        return rs

    def mkExpr(self, ss):
        # create z3 expression

        assert len(ss) == len(self.vs), (ss, self.vs)
        try:
            exprs = [s == v for s, v in zip(ss, self.vs)]
        except Exception:
            myvals = map(int, self.vs)
            exprs = [s == v for s, v in zip(ss, myvals)]
        return z3.And(exprs)


class Traces(set):
    def __init__(self, myset=set()):
        assert all(isinstance(t, Trace) for t in myset), myset
        super(Traces, self).__init__(myset)

    def __contains__(self, trace):
        assert isinstance(trace, Trace), trace
        return super(Traces, self).__contains__(trace)

    def add(self, trace):
        assert isinstance(trace, Trace), trace
        return super(Traces, self).add(trace)

    def myeval(self, expr):
        assert Miscs.is_expr(expr), expr
        return [trace.myeval(expr) for trace in self]

    def __str__(self, printDetails=False):
        if printDetails:
            return ", ".join(map(str, sorted(self)))
        else:
            return str(len(self))

    @classmethod
    def extract(cls, cexs, useOne=True):
        """
        cexs is a dict{inv: [dict]}
        for each disproved inv, use just 1 cex
        """

        if useOne:
            cexs = [cexs[inv][0] for inv in cexs]
        else:
            cexs = [cex for inv in cexs for cex in cexs[inv]]

        cexs = [Trace.fromDict(cex) for cex in cexs]
        cexs = Traces(cexs)
        return cexs

    @property
    def mydicts(self):
        return (trace.mydict for trace in self)

    def instantiate(self, term, nTraces):
        assert Miscs.is_expr(term), term
        assert nTraces is None or nTraces >= 1, nTraces

        if nTraces is None:
            for t in self.mydicts:
                exprs = set(term.subs(t) for t in self.mydicts)
        else:
            nTracesExtra = nTraces * settings.TRACE_MULTIPLIER
            exprs = set()
            for t in self.mydicts:
                expr = term.subs(t)
                if expr not in exprs:
                    exprs.add(expr)
                    if len(exprs) >= nTracesExtra:
                        break

            # instead of doing this, can find out the # 0's in traces
            # the more 0's , the better
            exprs = sorted(exprs, key=lambda expr: len(Miscs.getVars(expr)))
            exprs = set(exprs[:nTraces])
        return exprs

    def get_satisfying_traces(self, inv):
        return Traces([t for t in self if inv.test_single_trace(t)])

    def padZeros(self, ss):
        newTraces = Traces()
        for t in self:
            tss = set(t.ss)
            if len(tss) < len(ss):
                ss_ = ss - tss
                newss = t.ss + tuple(ss_)
                newvs = t.vs + (0,) * len(ss_)
                t = Trace(newss, newvs)
            newTraces.add(t)

        return newTraces


class Inps(Traces):
    def myupdate(self, ds, ss):
        """
        ds can be
        1. cexs = {loc:{inv: {'x': val, 'y': val}}}
        2. [cexs]
        3. [inp]
        """

        if not ds:
            return Inps()

        def f(d):
            inps = []
            for loc in d:
                for inv in d[loc]:
                    for d_ in d[loc][inv]:
                        inp = tuple(d_[s] for s in ss)
                        inps.append(inp)
            return inps

        if (isinstance(ds, list) and all(isinstance(d, dict) for d in ds)):
            newInps = [inp for d in ds for inp in f(d)]

        elif isinstance(ds, dict):
            newInps = f(ds)

        else:
            assert isinstance(ds, set) and\
                all(isinstance(d, tuple) for d in ds), ds
            newInps = [inp for inp in ds]

        newInps = [Trace(ss, inp) for inp in newInps]
        newInps = set(inp for inp in newInps if inp not in self)
        for inp in newInps:
            self.add(inp)
        return Inps(newInps)


class DTraces(dict):
    """
    {loc: Traces}
    """
    inpMaxV = settings.INP_MAX_V

    @property
    def siz(self): return sum(map(len, self.itervalues()))

    def __str__(self, printDetails=False):
        return "\n".join("{}: {}".format(loc, traces.__str__(printDetails))
                         for loc, traces in self.iteritems())

    def add(self, loc, trace):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(trace, Trace), trace

        if loc not in self:
            self[loc] = Traces()

        notIn = trace not in self[loc]
        if notIn:
            self[loc].add(trace)
        return notIn

    def update(self, traces):
        """
        Update dtraces to contain contents of self and return diffs
        """
        assert isinstance(traces, DTraces), traces

        newTraces = DTraces()
        for loc in self:
            for trace in self[loc]:
                notIn = traces.add(loc, trace)
                assert(notIn), "{} exist".format(trace)
                newTraces.add(loc, trace)
        return newTraces

    @staticmethod
    def parse(trace_str, inv_decls):
        """
        parse trace for new traces

        trace_str = ['vtrace1: 0 285 1 9 285 9 ',
        'vtrace1: 0 285 2 18 285 9 ',
        'vtrace1: 0 285 4 36 285 9 ']
        """
        assert isinstance(inv_decls, DSymbs) and inv_decls, inv_decls

        lines = [l.strip() for l in trace_str]
        lines = [l for l in lines if l]

        dtraces = DTraces()
        for l in lines:
            # 22: 8460 16 0 1 16 8460
            parts = l.split(':')
            assert len(parts) == 2, parts
            loc, tracevals = parts[0], parts[1]
            loc = loc.strip()  # 22
            ss = inv_decls[loc].names
            vs = tracevals.strip().split()
            mytrace = Trace.parse(ss, vs)
            dtraces.add(loc, mytrace)
        return dtraces

    def vwrite(self, inv_decls, tracefile):
        """
        write traces to file
        each loc will have its own file

        file 'traces_loc.csv'
        var1, var2, var3
        v1, v2, v2
        ...
        """
        assert inv_decls and isinstance(inv_decls, DSymbs), inv_decls
        assert tracefile and isinstance(tracefile, str), tracefile

        ss = []
        for loc in self:
            traces = [inv_decls[loc]]
            traces.extend([', '.join(map(str, t.vs)) for t in self[loc]])
            traces = ['{}: {}'.format(loc, t) for t in traces]
            ss.extend(traces)

        CM.vwrite(tracefile, '\n'.join(ss))

    @classmethod
    def vread(cls, tracefile):
        assert tracefile and isinstance(tracefile, str), tracefile

        trace_str = []
        # determine variable declarations for different locations
        inv_decls = DSymbs()
        for line in CM.iread_strip(tracefile):
            loc, contents = line.split(':')
            if loc not in inv_decls:
                inv_decls[loc] = Symbs.mk(contents)  # I x, I y
            else:
                trace_str.append(line.replace(',', ''))

        dtraces = DTraces.parse(trace_str, inv_decls)
        return inv_decls, dtraces
