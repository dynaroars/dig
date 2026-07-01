from __future__ import annotations
import csv
import pdb
from pathlib import Path
from collections.abc import Iterable
from typing import NamedTuple
import sympy
from beartype import beartype
import z3

import helpers.vcommon as CM
from helpers.miscs import Miscs

import data.prog
import settings


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)

class SymbsVals(NamedTuple):
    ss: tuple
    vs: tuple
    """ "
    ((x, y), (3, 4))
    """
    @beartype
    @classmethod
    def mk(cls, ss: tuple, vs: tuple) -> SymbsVals:
        return cls(ss, vs)

    @beartype
    def __str__(self) -> str:
        return ",".join(f"{s}={v}" for s, v in zip(self.ss, self.vs))

    @beartype
    def mk_expr(self, ss) -> z3.ExprRef:
        # create z3 expression
        assert len(ss) == len(self.vs), (ss, self.vs)
        try:
            exprs = [s == v for s, v in zip(ss, self.vs)]
        except Exception:
            exprs = [s == int(v) for s, v in zip(ss, self.vs)]
        return z3.And(exprs)


class SymbsValsSet(set):
    
    @beartype
    def __init__(self, myset=()) -> None:
        super().__init__(myset)

    @beartype
    def __contains__(self, t: SymbsVals) -> bool:
        return super().__contains__(t)

    @beartype
    def add(self, t: SymbsVals) -> None:
        return super().add(t)


class Trace(SymbsVals):
    @property
    def mydict(self) -> dict:
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
    def mydict_str(self) -> dict:
        # use for maxplus eval
        try:
            return self._mydict_str
        except AttributeError:
            self._mydict_str = {s: v for s, v in zip(
                self.ss, self.vs) if "!" not in s}
            return self._mydict_str

    @classmethod
    def parse(cls, ss: tuple | list, vs: tuple | list,
              typs: tuple | list | None = None) -> Trace:
        assert isinstance(ss, (tuple, list)), ss
        assert isinstance(vs, (tuple, list)), vs

        if typs is None:
            typs = [None] * len(vs)

        def conv(v, t):
            if '[' in v:
                return Miscs.str2list(v)
            if t == "D":
                # real value printed by C as %.17g: read it as the exact double
                # it denotes (Rational(float(v))), not a truncated decimal, so
                # dyadic values like 2 - 2**-23 round-trip exactly and the
                # invariant still holds precisely over the traces.
                return sympy.Rational(float(v))
            return Miscs.str2rat(v)

        vs = tuple(conv(v, t) for v, t in zip(vs, typs))
        return Trace(tuple(ss), vs)

    @classmethod
    def fromDict(cls, d: dict) -> Trace:
        # {'y': 1, 'x': 2, 'r': 2, 'b': 2}
        ss = tuple(sorted(d))
        vs = tuple(d[s] for s in ss)
        return cls(ss, vs)

    def myeval(self, expr) -> sympy.Expr:
        assert Miscs.is_expr(expr), expr
        rs = expr.xreplace(self.mydict)
        return rs


class Traces(SymbsValsSet):

    @beartype
    def __str__(self, printDetails: bool=False) -> str:
        if printDetails:
            return ", ".join(map(str, sorted(self)))
        else:
            return str(len(self))

    def myeval(self, expr, pred=None) -> list | bool:
        assert Miscs.is_expr(expr), expr

        if pred is None:
            return [trace.myeval(expr) for trace in self]
        else:
            return any(pred(trace.myeval(expr)) for trace in self)

    @classmethod
    def extract(cls, cexs: dict, useOne: bool = True) -> Traces:
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
    
    @beartype
    @property
    def mydicts(self) -> Iterable[dict]:
        return (trace.mydict for trace in self)

    @beartype
    def instantiate(self, template, ntraces: int | None):  # -> set[z3.ExprRef]:
        assert Miscs.is_expr(template), template
        assert ntraces is None or ntraces >= 1, ntraces

        exprs = set()
        if ntraces is None:  # use everything
            exprs = set(template.xreplace(t) for t in self.mydicts)
        else:
            ntracesExtra = ntraces * settings.TRACE_MULTIPLIER
            # iterate in a canonical order so the subset picked by the break
            # below doesn't depend on set iteration order (hashing / PYTHONHASHSEED)
            for trace in sorted(self, key=str):
                expr = template.xreplace(trace.mydict)
                if expr not in exprs:
                    exprs.add(expr)
                    if len(exprs) >= ntracesExtra:
                        break

            # instead of doing this, can find out the # 0's in traces
            # the more 0's , the better
            # NOTE: ties deliberately stay in set order (deterministic under
            # dig.py's pinned PYTHONHASHSEED). A str tie-break groups
            # near-dependent rows into the truncated sample and measurably
            # slows eqt solving (3x on ps5/ps6).
            exprs = sorted(exprs, key=lambda expr: len(Miscs.get_vars(expr)))
            exprs = set(exprs[:ntraces])

        return exprs

    def padzeros(self, ss: set) -> Traces:
        new_traces = Traces()
        for t in self:
            tss = set(t.ss)
            if len(tss) < len(ss):
                ss_ = sorted(ss - tss)  # canonical order, not set order
                newss = t.ss + tuple(ss_)
                newvs = t.vs + (0,) * len(ss_)
                t = Trace(newss, newvs)
            new_traces.add(t)

        return new_traces


class DTraces(dict):
    """
    {loc: Traces}
    """
    @beartype
    @property
    def siz(self) -> int:
        return sum(map(len, self.values()))

    @beartype
    def __str__(self, printDetails:bool=False) -> str:
        return "\n".join(
            f"{loc}: {traces.__str__(printDetails)}" for loc, traces in self.items()
        )
    
    @beartype
    def add(self, loc: str, trace: Trace) -> bool:
        if loc not in self:
            self[loc] = Traces()

        not_in = trace not in self[loc]
        if not_in:
            self[loc].add(trace)
        return not_in

    def merge(self, new_traces: DTraces) -> DTraces:
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
                    mlog.debug(f"trace {trace} exist")
        return new_traces_

    @classmethod
    def mk(cls, locs) -> DTraces:
        assert locs
        return cls({loc: Traces() for loc in locs})

    @beartype
    @staticmethod
    def parse(traces, inv_decls) -> DTraces:
        """
        parse trace for new traces
        # >>> traces = ['vtrace1; 0; 285; 1; 9; 285; 9 ', 'vtrace1; 0; 285; 2; 18; 285; 9; ', 'vtrace1; 0; 285; 4; 36; 285; 9; ']
        # >>> DTraces.parse(traces)
        """
        assert inv_decls, inv_decls
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
            symbs = inv_decls[loc]
            ss = symbs.names
            typs = tuple(s.typ for s in symbs)
            mytrace = Trace.parse(ss, vs, typs)
            dtraces.add(loc, mytrace)

        return dtraces


    @beartype
    def vwrite(self, inv_decls, tracefile: Path) -> None:
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
        assert isinstance(tracefile, Path) and tracefile.suffix == ".csv", tracefile
            

        ss: list[str] = []
        for loc in self:
            traces = [inv_decls[loc]]
            traces.extend(["; ".join(map(str, t.vs)) for t in self[loc]])
            traces = [f"{loc}; {trace}" for trace in traces]
            ss.extend(traces)

        tracefile.write_text("\n".join(ss))

    @beartype
    @classmethod
    def vread(cls, tracefile: Path):
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
    def merge(self, ds, ss) -> Inps:
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
            new_inps = list(ds)

        new_inps = [Inp(ss, inp) for inp in new_inps]
        new_inps = {inp for inp in new_inps if inp not in self}
        for inp in new_inps:
            self.add(inp)
        return Inps(new_inps)
