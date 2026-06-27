from __future__ import annotations
import abc
from collections import Counter
from collections.abc import Iterable
from enum import Enum
import functools
from time import time
import pdb
import operator
from typing import NamedTuple

import sympy
import z3
from beartype import beartype

from helpers.miscs import Miscs, MP
from helpers.z3utils import Z3
import helpers.vcommon as CM
import settings
import data.traces


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class InvStat(str, Enum):
    PROVED = "p"
    DISPROVED = "d"
    UNKNOWN = "u"

    def __str__(self) -> str:
        return self.value


class Inv(metaclass=abc.ABCMeta):

    PROVED = InvStat.PROVED
    DISPROVED = InvStat.DISPROVED
    UNKNOWN = InvStat.UNKNOWN

    @beartype
    def __init__(self, inv: int | tuple | str | sympy.Equality | sympy.Le, stat = None) -> None:
        """
        stat = None means never been checked
        """
        assert (inv == 0 or  # FalseInv
                # Max/MinPlus
                (isinstance(inv, tuple) and (len(inv) == 2 or len(inv) == 4)) or
                (isinstance(inv, tuple) and len(inv) == 3) or  # congruence
                isinstance(inv, str) or   # Array relation
                isinstance(inv, (sympy.Equality, sympy.Le))), inv

        assert stat in {None, self.PROVED, self.DISPROVED, self.UNKNOWN}

        self.inv = inv
        if stat is None:
            self.reset_stat()
        else:
            self.stat = stat

    @property
    @abc.abstractmethod
    def mystr(self) -> str:
        pass

    def __str__(self, print_stat: bool = False) -> str:
        s = self.mystr
        if print_stat:
            s = f"{s} {self.stat}"
        return s

    def __hash__(self) -> int:
        return hash(self.inv)

    def __repr__(self) -> str:
        return repr(self.inv)

    def __eq__(self, o: object) -> bool:
        if not isinstance(o, Inv):
            return NotImplemented
        return self.inv.__eq__(o.inv)

    def __ne__(self, o: object) -> bool:
        if not isinstance(o, Inv):
            return NotImplemented
        return not self.inv.__eq__(o.inv)

    def get_stat(self) -> InvStat | None:
        return self._stat

    def set_stat(self, stat: InvStat) -> None:
        assert stat in {self.PROVED, self.DISPROVED, self.UNKNOWN}, stat
        self._stat = stat

    stat = property(get_stat, set_stat)

    def reset_stat(self) -> None:
        self._stat = None

    @beartype
    def test(self, traces: data.traces.Traces):
        return all(self.test_single_trace(trace) for trace in traces)

    @property
    def is_proved(self) -> bool:
        return self.stat == self.PROVED

    @property
    def is_disproved(self) -> bool:
        return self.stat == self.DISPROVED

    @property
    def is_unknown(self) -> bool:
        return self.stat == self.UNKNOWN

    @property
    def cinvs_category(self) -> str:
        raise NotImplementedError(f"{type(self)} must implement cinvs_category")

    def test_single_trace(self, trace: data.traces.Trace) -> bool:
        assert isinstance(trace, data.traces.Trace), trace

        # temp fix: disable traces that wih extreme large values
        # (see geo1 e.g., 435848050)
        if any(abs(x) > settings.TRACE_MAX_VAL for x in trace.vs):
            mlog.debug(f"{self}: skip trace with large val: {trace.vs}")
            return True

        try:
            return bool(self.inv.xreplace(trace.mydict))
        except ValueError:
            mlog.debug(f"{self}: failed test")
            return False

    @beartype
    @property
    def expr(self) -> z3.ExprRef:
        """
        cannot cache because z3 expr is ctype,
        not compat with multiprocessing Queue

        also, cannot save this to sel._expr
        """

        expr = Z3.parse(str(self))
        return expr


class FalseInv(Inv):
    def __init__(self, inv: int, stat: InvStat | None = None) -> None:
        assert inv == 0, inv
        super().__init__(inv, stat)

    def __str__(self, print_stat: bool = False) -> str:
        s = str(self.inv)
        if print_stat:
            s = f"{s} {self.stat}"
        return s

    @beartype
    @property
    def expr(self) -> z3.ExprRef:
        return Z3.zFalse

    @property
    def mystr(self) -> str:
        return "False"

    @property
    def cinvs_category(self) -> str:
        return 'falseinvs'

    @classmethod
    def mk(cls) -> FalseInv:
        return FalseInv(0)


class RelTerm(NamedTuple):
    """
    e.g., x + y,  x,  x + 3
    """

    term: sympy.Expr

    @classmethod
    def mk(cls, term: sympy.Expr) -> RelTerm:
        assert (
            isinstance(term, sympy.Expr)
            and not term.is_relational()
        ), term
        return cls(term)

    @property
    def symbols(self) -> set:
        return Miscs.get_vars(self.term)

    def eval_traces(self, traces: data.traces.Traces, pred=None) -> list | bool:
        return traces.myeval(self.term, pred)

    def mk_lt(self, val: int) -> sympy.Rel:
        return self._mk_rel(operator.lt, val)

    def mk_le(self, val: int) -> sympy.Rel:
        return self._mk_rel(operator.le, val)

    def mk_eq(self, val: int) -> sympy.Rel:
        return self._mk_rel(operator.eq, val)

    def _mk_rel(self, myop, val: int) -> sympy.Rel:
        """
        return myop(self.term, val), e.g., x + y <= 8
        """
        assert myop in {operator.eq, operator.le, operator.lt}, myop

        return myop(self.term, val)


class Invs(set):
    def __init__(self, invs: Iterable[Inv] = ()) -> None:
        assert all(isinstance(inv, Inv) for inv in invs), invs
        super().__init__(invs)

    @beartype
    def __contains__(self, inv:Inv) -> bool:
        return super().__contains__(inv)

    @property
    def typ_ctr(self) -> Counter:
        return Counter(inv.__class__.__name__ for inv in self)

    @property
    def cinvs(self) -> CInvs:
        return CInvs(self)

    @beartype
    def add(self, inv:Inv) -> bool:

        not_in = inv not in self
        if not_in:
            super().add(inv)
        return not_in

    def test(self, traces: data.traces.Traces) -> Invs:
        assert self, self

        def f(tasks):
            return [(inv, inv.test(traces)) for inv in tasks]

        wrs = MP.run_mp("test", list(self), f, settings.DO_MP)

        myinvs = set()
        for inv, passed in wrs:
            if passed:
                myinvs.add(inv)
            else:
                mlog.debug(f"remove {inv}")

        invs = self.__class__(myinvs)
        return invs

    def simplify(self) -> Invs:
        return self.__class__(self.cinvs.simplify())


class CInvs:
    """
    Classify invariants into their types for various simplification tasks
    """

    def __init__(self, invs: Invs):
        self.invs = invs
        self.eqts = []
        self.eqts_largecoefs = []
        self.octs = []
        self.mps = []
        self.congruences = []
        self.arr_rels = []
        self.falseinvs = []
        self.llm = []  # LLM-proposed, z3-verified invariants (neuro-symbolic)

        for inv in self.invs:
            getattr(self, inv.cinvs_category).append(inv)

    @classmethod
    def get_max_deg(cls, inv: Inv) -> int | None:
        try:
            p = inv.inv
            if p.is_Relational:
                return Miscs.get_max_deg(p.lhs)
            else:
                return None
        except AttributeError:
            return None


    def __str__(self, print_stat: bool = False, print_first_n: int | None = None,
                writeresults: bool = False) -> str:
        def mylen(x):
            return len(str(x))

        if writeresults:
            invs = (
                sorted(self.eqts + self.eqts_largecoefs, key=mylen)
                + sorted(self.octs, key=mylen)
                + sorted(self.mps, key=mylen)
                + sorted(self.congruences, key=mylen)
                + sorted(self.arr_rels, key=mylen)
                + sorted(self.falseinvs, key=mylen)
                + sorted(self.llm, key=mylen)
            )
            if print_first_n and print_first_n < len(invs):
                invs = invs[:print_first_n] + ["..."]
            parts = []
            for inv in invs:
                deg = self.get_max_deg(inv)
                s = inv if isinstance(inv, str) else inv.__str__(print_stat)
                parts.append(f"{s} {deg}")
            return '; '.join(parts)

        categories = [
            ("Eqt",        self.eqts + self.eqts_largecoefs),
            ("Oct",        self.octs),
            ("MinMax",     self.mps),
            ("Congruence", self.congruences),
            ("Array",      self.arr_rels),
            ("LLM",        self.llm),
        ]
        lines = []
        for label, invs in categories:
            if not invs:
                continue
            invs = sorted(invs, key=mylen)
            if print_first_n and print_first_n < len(invs):
                invs = invs[:print_first_n] + ["..."]
            parts = [inv.__str__(print_stat) if not isinstance(inv, str) else inv
                     for inv in invs]
            lines.append(f"  {label}: {'; '.join(parts)}")
        return '\n'.join(lines)

    def simplify(self) -> list[Inv]:
        eqts = self.eqts
        eqts_largecoefs = self.eqts_largecoefs
        octs = self.octs
        mps = self.mps
        congruences = self.congruences
        arr_rels = self.arr_rels
        falseinvs = self.falseinvs

        assert not falseinvs, falseinvs

        done = eqts_largecoefs

        # simplify eqts, e.g., to remove x - y == 0  if -x + y == 0 exists
        # grobner basis should take care of this? Apparently not
        eqts = self._simplify_slow(eqts, None, "eqts")
        done += eqts

        # simplify congruences
        congruences = self._simplify_fast(congruences, eqts, "congruences")
        congruences = self._simplify_slow(congruences, None, "congruences")

        done += congruences

        # simplify ieqs
        octs_simple, octs_not_simple = [], []
        for oct in octs:
            (octs_simple if oct.is_simple else octs_not_simple).append(oct)

        # find equality invs (==) from min/max-plus
        mps_eqt, mps_ieq = [], []
        if mps:
            import infer.mp
            mps = infer.mp.MMP.simplify(mps)
            for mp in mps:
                (mps_eqt if mp.is_eqt else mps_ieq).append(mp)

        done += mps_eqt

        mps_ieq = self._simplify_fast(
            mps_ieq, done + octs, "mps_ieq")
        octs_not_simple = self._simplify_fast(
            octs_not_simple, done + octs_simple + mps_ieq, "octs")

        done += eqts_largecoefs
        octs_mps = octs_not_simple + mps_ieq

        # simplify both mps and octs (slow), remove as much as possible
        if octs_not_simple or mps_ieq:

            def mysorted(ps):
                return sorted(ps, key=lambda p: len(Miscs.get_vars(p.inv)))

            octs_not_simple = mysorted(octs_not_simple)
            mps_ieq = mysorted(mps_ieq)

            octs_mps = self._simplify_slow(
                octs_mps,
                done + octs_simple,
                "octs+mps")

        # don't use done to simplify octs_simple because
        # nonlinear eqts will remove many useful octs
        octs_simple = self._simplify_slow(
            octs_simple, mps_eqt + octs_mps, "octs_simple")

        done += octs_simple + octs_mps + arr_rels
        return done

    @classmethod
    @functools.cache
    def _get_expr(cls, p):
        return p.expr

    @classmethod
    def _simplify_fast(cls, ps, others, msg):
        """
        Simplify given properties ps (usually a class of invs such as octs or mps)
        using the properties in others, e.g., remove p if others => p
        Note: this task is relatively fast, using multiprocessing
        """
        if len(ps) < 2 or not others:
            return ps

        st = time()
        conj = [cls._get_expr(p) for p in others]
        for p in ps:
            _ = cls._get_expr(p)

        def f(ps):
            return [p for p in ps if not Z3._imply(conj, cls._get_expr(p))]

        wrs = MP.run_mp(
            f"_simplify_fast {len(ps)} {msg}", ps, f, settings.DO_MP)

        Miscs.show_removed(f"_simplify_fast {msg}", len(
            ps), len(wrs), time() - st)
        ps = list(wrs)
        return ps

    @classmethod
    def _simplify_slow(cls, ps, others, msg):
        """
        Simplify given properties ps using properties in both ps and others
        e.g., remove g if  ps_exclude_g & others => g
        Note: this task is slow
        """

        if len(ps) < 2:
            return ps

        st = time()
        conj = [cls._get_expr(p) for p in others] if others else []
        ps_exprs = [cls._get_expr(p) for p in ps]

        def _imply(js, i):
            iexpr = ps_exprs[i]

            #assert iexpr.decl().kind() != z3.Z3_OP_EQ, iexpr
            jexprs = [ps_exprs[j] for j in js]
            ret = Z3._imply(conj + jexprs, iexpr, is_conj=True)
            #print('{} => {} ret{}'.format(jexprs, iexpr, ret))
            return ret

        results = Miscs.simplify_idxs(list(range(len(ps))), _imply)
        results = [ps[i] for i in results]
        Miscs.show_removed(f"_simplify_slow {msg}",
                           len(ps), len(results), time() - st)

        return results


class DInvs(dict):
    """
    {loc -> Invs}, Invs is a set
    """

    @beartype
    def __setitem__(self, loc, invs):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(invs, Invs), invs

        super().__setitem__(loc, invs)

    @property
    def invs(self):
        return (inv for invs in self.values() for inv in invs)

    @property
    def siz(self):
        return sum(map(len, self.values()))

    @property
    def typ_ctr(self):
        return sum([self[loc].typ_ctr for loc in self], Counter())

    @property
    def n_eqs(self):
        import infer.eqt

        return self.typ_ctr[infer.eqt.Eqt.__name__]

    def __str__(self, print_stat=False, print_first_n=None, writeresults=False):
        ss = []
        for loc in sorted(self):
            s = "; " if writeresults else f"({len(self[loc])} invs):\n"
            ss.append(f"{loc} {s}"
                      f"{self[loc].cinvs.__str__(print_stat, print_first_n, writeresults)}")

        ss = "\n".join(ss)
        return ss

    def add(self, loc, inv):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(inv, Inv), inv

        return self.setdefault(loc, Invs()).add(inv)

    def merge(self, dinvs):
        assert isinstance(dinvs, DInvs), dinvs
        for loc in dinvs:
            for inv in dinvs[loc]:
                if not inv.is_disproved:
                    self.add(loc, inv)

    def remove_disproved(self):
        dinvs = self.__class__()
        for loc in self:
            for inv in self[loc]:
                if not inv.is_disproved:
                    dinvs.add(loc, inv)
        return dinvs

    def test(self, dtraces):
        # assert isinstance(dtraces, DTraces)
        assert self.siz, self

        st = time()
        tasks = [loc for loc in self if self[loc]]

        def f(tasks):
            return [(loc, self[loc].test(dtraces[loc])) for loc in tasks]

        wrs = MP.run_mp("test_dinvs", tasks, f, settings.DO_MP)
        dinvs = DInvs()
        for loc, invs in wrs:
            if invs:
                dinvs[loc] = invs
        Miscs.show_removed("test_dinvs", self.siz, dinvs.siz, time() - st)
        return dinvs

    def update(self, dinvs):
        assert isinstance(dinvs, DInvs), dinvs
        deltas = self.__class__()
        for loc in self:
            if loc not in dinvs:
                dinvs[loc] = self[loc]
                deltas[loc] = self[loc]
            elif dinvs[loc] != self[loc]:
                new_invs = Invs()
                for inv in self[loc]:
                    if inv not in dinvs[loc]:
                        new_invs.add(inv)
                    else:
                        invs_l = list(dinvs[loc])
                        old_inv = invs_l[invs_l.index(inv)]
                        if inv.stat != old_inv.stat:
                            inv.stat = old_inv.stat
                dinvs[loc] = self[loc]
                deltas[loc] = new_invs

        return deltas

    def simplify(self):
        assert self.siz, self

        st = time()

        def f(tasks):
            return [(loc, self[loc].simplify()) for loc in tasks]

        wrs = MP.run_mp("simplify", list(self), f, settings.DO_MP)
        mlog.debug(f"done simplifying, time {time() - st}")
        dinvs = self.__class__()
        for loc, invs in wrs:
            if invs:
                dinvs[loc] = invs
        Miscs.show_removed("simplify", self.siz, dinvs.siz, time() - st)
        return dinvs

    @beartype
    @classmethod
    def mk_false_invs(cls, locs) -> 'DInvs':
        dinvs = cls()
        for loc in locs:
            dinvs.add(loc, FalseInv.mk())
        return dinvs

    @beartype
    @classmethod
    def mk(cls, loc:str, invs:Invs) -> 'DInvs':
        new_invs = cls()
        new_invs[loc] = invs
        return new_invs
