from time import time
import pdb
from collections import namedtuple
from pathlib import Path
from collections.abc import Iterable
import typing
import sympy
import z3

import helpers.vcommon as CM
from helpers.miscs import Miscs

import data.prog
import settings

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)

class SymbsVals(typing.NamedTuple):
    ss: tuple
    vs: tuple
    """ "
    ((x, y), (3, 4))
    """

    def mk(cls, ss, vs):
        assert isinstance(ss, tuple), ss
        assert isinstance(vs, tuple), vs
        return cls (ss, vs)

    def __str__(self):
        return ",".join(f"{s}={v}" for s, v in zip(self.ss, self.vs))

    def mk_expr(self, ss):
        # create z3 expression
        assert len(ss) == len(self.vs), (ss, self.vs)
        try:
            exprs = [s == v for s, v in zip(ss, self.vs)]
        except Exception:
            exprs = [s == int(v) for s, v in zip(ss, self.vs)]
        return z3.And(exprs)


class SymbsValsSet(set):
    def __init__(self, myset=set()):
        assert all(isinstance(t, SymbsVals) for t in myset), myset
        super().__init__(myset)

    def __contains__(self, t):
        assert isinstance(t, SymbsVals), t
        return super().__contains__(t)

    def add(self, t):
        assert isinstance(t, SymbsVals), t
        return super().add(t)


class Trace(SymbsVals):
    @property
    def mydict(self):
        # use for expression substitution
        try:
            return self._mydict
        except AttributeError:
            d = {}
            for s, v in zip(self.ss, self.vs):
                if "!" in s:
                    continue
                k = str(s) if isinstance(v, Iterable) else sympy.Symbol(s)
                assert k not in d
                d[k] = v

            self._mydict = d
            return self._mydict

    @property
    def mydict_str(self):
        # use for maxplus eval
        try:
            return self._mydict_str
        except AttributeError:
            self._mydict_str = {s: v for s, v in zip(
                self.ss, self.vs) if "!" not in s}
            return self._mydict_str

    @classmethod
    def parse(cls, ss, vs):
        assert isinstance(ss, (tuple, list)), ss
        assert isinstance(vs, (tuple, list)), vs

        vs = tuple(Miscs.str2list(t) if '[' in t else Miscs.str2rat(t)
                   for t in vs)

        return Trace(ss, vs)

    @classmethod
    def fromDict(cls, d):
        # {'y': 1, 'x': 2, 'r': 2, 'b': 2}
        ss = tuple(sorted(d))
        vs = tuple(d[s] for s in ss)
        return cls(ss, vs)

    def myeval(self, expr):
        assert Miscs.is_expr(expr), expr
        rs = expr.xreplace(self.mydict)
        return rs


class Traces(SymbsValsSet):
    def __str__(self, printDetails=False):
        if printDetails:
            return ", ".join(map(str, sorted(self)))
        else:
            return str(len(self))

    def myeval(self, expr, pred=None):
        assert Miscs.is_expr(expr), expr

        if pred is None:
            return [trace.myeval(expr) for trace in self]
        else:
            return any(pred(trace.myeval(expr)) for trace in self)

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

    def instantiate(self, template, ntraces):
        assert Miscs.is_expr(template), template
        assert ntraces is None or ntraces >= 1, ntraces

        exprs = set()
        if ntraces is None:  # use everything
            exprs = set(template.xreplace(t) for t in self.mydicts)
        else:
            ntracesExtra = ntraces * settings.TRACE_MULTIPLIER
            for t in self.mydicts:

                expr = template.xreplace(t)
                if expr not in exprs:
                    exprs.add(expr)
                    if len(exprs) >= ntracesExtra:
                        break

            # instead of doing this, can find out the # 0's in traces
            # the more 0's , the better
            exprs = sorted(exprs, key=lambda expr: len(Miscs.get_vars(expr)))
            exprs = set(exprs[:ntraces])

        return exprs

    def padzeros(self, ss):
        new_traces = Traces()
        for t in self:
            tss = set(t.ss)
            if len(tss) < len(ss):
                ss_ = ss - tss
                newss = t.ss + tuple(ss_)
                newvs = t.vs + (0,) * len(ss_)
                t = Trace(newss, newvs)
            new_traces.add(t)

        return new_traces


class DTraces(dict):
    """
    {loc: Traces}
    """

    @property
    def siz(self):
        return sum(map(len, self.values()))

    def __str__(self, printDetails=False):
        return "\n".join(
            f"{loc}: {traces.__str__(printDetails)}" for loc, traces in self.items()
        )

    def add(self, loc, trace):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(trace, Trace), trace

        if loc not in self:
            self[loc] = Traces()

        not_in = trace not in self[loc]
        if not_in:
            self[loc].add(trace)
        return not_in

    def merge(self, new_traces):
        """
        add new traces and return those that are really new
        """
        new_traces_ = DTraces()
        for loc in new_traces:
            for trace in new_traces[loc]:
                not_in = self.add(loc, trace)
                if not_in:
                    new_traces_.add(loc, trace)
                else:
                    mlog.warning(f"trace {trace} exist")
        return new_traces_

    @classmethod
    def mk(cls, locs):
        assert locs
        return cls({loc: Traces() for loc in locs})

    @staticmethod
    def parse(traces, inv_decls):
        """
        parse trace for new traces
        # >>> traces = ['vtrace1; 0; 285; 1; 9; 285; 9 ', 'vtrace1; 0; 285; 2; 18; 285; 9; ', 'vtrace1; 0; 285; 4; 36; 285; 9; ']
        # >>> DTraces.parse(traces)
        """
        assert isinstance(inv_decls, data.prog.DSymbs) and inv_decls, inv_decls
        lines = [l.strip() for l in traces]
        lines = [l for l in lines if l]

        dtraces = DTraces()
        for l in lines:
            # 22; 8460; 16; 0; 1; 16; 8460;
            contents = [x.strip() for x in l.split(';')]
            contents = [x for x in contents if x]
            loc, vs = contents[0].strip(), contents[1:]
            if loc not in inv_decls:
                """
                No symbolic states for this loc, so will not
                collect concrete states here
                """
                continue
            ss = inv_decls[loc].names
            mytrace = Trace.parse(ss, vs)
            dtraces.add(loc, mytrace)

        return dtraces

    def vwrite(self, inv_decls, tracefile):
        """
        write traces to tracefile
        vtrace1; I q; I r; I a; I b; I x; I y
        vtrace1; 4; 8; 1; 4; 24; 4
        vtrace1; 16; 89; 1; 13; 297; 13
        ...
        vtrace2; I x; I y
        vtrace2; 4; 2
        vtrace2; 8; 4
        ...
        """
        assert inv_decls and isinstance(inv_decls, data.prog.DSymbs), inv_decls
        assert isinstance(
            tracefile, Path) and tracefile.suffix == ".csv", tracefile

        ss = []
        for loc in self:
            traces = [inv_decls[loc]]
            traces.extend(["; ".join(map(str, t.vs)) for t in self[loc]])
            traces = [f"{loc}; {trace}" for trace in traces]
            ss.extend(traces)

        tracefile.write_text("\n".join(ss))

    @classmethod
    def vread(cls, tracefile):
        """
        Csv format

        vtrace1; I q; I r; I a; I b; I x; I y
        vtrace1; 4; 8; 1; 4; 24; 4
        vtrace1; 16; 89; 1; 13; 297; 13
        ...
        vtrace2; I x; I y
        vtrace2; 4; 2
        vtrace2; 8; 4
        ...
        """
        assert tracefile.is_file() and tracefile.suffix == ".csv", tracefile

        import csv
        with open(tracefile) as csvfile:
            traces = []
            # determine variable declarations for different locations
            inv_decls = data.prog.DSymbs()

            myreader = csv.reader(csvfile, delimiter=';')
            for row in myreader:
                row = [field.strip() for field in row]
                if not row or row[0].startswith("#"):
                    continue
                loc, contents = row[0], row[1:]
                if loc not in inv_decls:
                    inv_decls[loc] = data.prog.Symbs.mk(contents)
                else:
                    s = f"{loc}; {';'.join(contents)}"
                    traces.append(s)

        dtraces = DTraces.parse(traces, inv_decls)
        mlog.debug(f"{dtraces} traces")
        return inv_decls, dtraces


class Inp(SymbsVals):
    pass


class Inps(SymbsValsSet):
    def merge(self, ds, ss):
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
                        try:
                            inp = tuple(d_[s] for s in ss)
                            inps.append(inp)
                        except KeyError:
                            # happens when the cex does not contain inp var
                            # e.g., when we only have symstates over
                            # non input vars
                            # see Hola 01.div.c
                            pass
            return inps

        if isinstance(ds, list) and all(isinstance(d, dict) for d in ds):
            new_inps = [inp for d in ds for inp in f(d)]

        elif isinstance(ds, dict):
            new_inps = f(ds)

        else:
            assert isinstance(ds, set) and all(
                isinstance(d, tuple) for d in ds), ds
            new_inps = [inp for inp in ds]

        new_inps = [Inp(ss, inp) for inp in new_inps]
        new_inps = set(inp for inp in new_inps if inp not in self)
        for inp in new_inps:
            self.add(inp)
        return Inps(new_inps)
