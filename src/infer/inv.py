import abc
from collections import Counter
from time import time
import pdb
import operator
from typing import NamedTuple

import sympy
import z3

from helpers.miscs import Miscs, MP
from helpers.z3utils import Z3
import helpers.vcommon as CM
import settings
import data.traces


DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Inv(metaclass=abc.ABCMeta):

    PROVED = "p"
    DISPROVED = "d"
    UNKNOWN = "u"

    def __init__(self, inv, stat=None):
        """
        stat = None means never been checked
        """
        assert (inv == 0 or  # FalseInv
                # PrePost and Max/MinPlus
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
    def mystr(self):
        pass

    def __str__(self, print_stat=False):
        s = self.mystr
        if print_stat:
            s = f"{s} {self.stat}"
        return s

    def __hash__(self):
        return hash(self.inv)

    def __repr__(self):
        return repr(self.inv)

    def __eq__(self, o):
        assert isinstance(o, Inv), o
        return self.inv.__eq__(o.inv)

    def __ne__(self, o):
        return not self.inv.__eq__(o.inv)

    def get_stat(self):
        return self._stat

    def set_stat(self, stat):
        assert stat in {self.PROVED, self.DISPROVED, self.UNKNOWN}, stat
        self._stat = stat

    stat = property(get_stat, set_stat)

    def reset_stat(self):
        self._stat = None

    def test(self, traces):
        assert isinstance(traces, data.traces.Traces), traces
        return all(self.test_single_trace(trace) for trace in traces)

    @property
    def is_proved(self):
        return self.stat == self.PROVED

    @property
    def is_disproved(self):
        return self.stat == self.DISPROVED

    @property
    def is_unknown(self):
        return self.stat == self.UNKNOWN

    def test_single_trace(self, trace):
        assert isinstance(trace, data.traces.Trace), trace

        # temp fix: disable traces that wih extreme large values
        # (see geo1 e.g., 435848050)
        if any(x > settings.TRACE_MAX_VAL for x in trace.vs):
            mlog.debug(f"{self}: skip trace with large val: {trace.vs}")
            return True

        try:
            return bool(self.inv.xreplace(trace.mydict))
        except ValueError:
            mlog.debug(f"{self}: failed test")
            return False

    @property
    def expr(self):
        """
        cannot cache because z3 expr is ctype,
        not compat with multiprocessing Queue

        also, cannot save this to sel._expr
        """
        return Z3.parse(str(self))


class FalseInv(Inv):
    def __init__(self, inv, stat=None):
        assert inv == 0, inv
        super().__init__(inv, stat)

    def __str__(self, print_stat=False):
        s = str(self.inv)
        if print_stat:
            s = f"{s} {self.stat}"
        return s

    @property
    def expr(self):
        return z3.BoolVal(False)

    @property
    def mystr(self):
        return "False"

    @classmethod
    def mk(cls):
        return FalseInv(0)


class RelTerm(NamedTuple):
    """
    e.g., x + y,  x,  x + 3
    """

    term: sympy.Expr

    @classmethod
    def mk(cls, term):
        assert (
            isinstance(term, sympy.Expr)
            and not term.is_relational()
        ), term
        return cls(term)

    @property
    def symbols(self):
        return Miscs.get_vars(self.term)

    def eval_traces(self, traces, pred=None):
        return traces.myeval(self.term, pred)

    def mk_lt(self, val):
        return self._mk_rel(operator.lt, val)

    def mk_le(self, val):
        return self._mk_rel(operator.le, val)

    def mk_eq(self, val):
        return self._mk_rel(operator.eq, val)

    def _mk_rel(self, myop, val):
        """
        return myop(self.term, val), e.g., x + y <= 8
        """
        assert myop == operator.eq or myop == operator.le or myop == operator.lt, myop

        return myop(self.term, val)


class Invs(set):
    def __init__(self, invs=set()):
        assert all(isinstance(inv, Inv) for inv in invs), invs
        super().__init__(invs)

    def __str__(self, print_stat=False, delim="\n"):
        invs = sorted(
            self, reverse=True, key=lambda inv: isinstance(inv, data.inv.eqt.Eqt)
        )
        return delim.join(inv.__str__(print_stat) for inv in invs)

    def __contains__(self, inv):
        assert isinstance(inv, Inv), inv
        return super().__contains__(inv)

    @property
    def typ_ctr(self):
        return Counter(inv.__class__.__name__ for inv in self)

    def add(self, inv):
        assert isinstance(inv, Inv), inv

        not_in = inv not in self
        if not_in:
            super().add(inv)
        return not_in

    def test(self, traces):
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

    @classmethod
    def get_expr(cls, p, exprs_d):
        if p not in exprs_d:
            exprs_d[p] = p.expr
        return exprs_d[p]

    def simplify(self):

        eqts, eqts_largecoefs, octs, mps, congruences, \
            arr_rels, falseinvs = self.classify(self)

        assert not falseinvs, falseinvs
        #assert not preposts, preposts

        exprs_d = {}

        def my_get_expr(p):
            return self.get_expr(p, exprs_d)

        # simplify eqts, e.g., to remove x - y == 0  if -x + y == 0 exists
        eqts = self._simplify_slow(eqts, None, "eqts", my_get_expr)

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

        done = eqts + mps_eqt + congruences  # don't simply these

        mps_ieq = self._simpify_fast(
            mps_ieq, done + octs, "mps_ieq", my_get_expr)
        octs_not_simple = self._simpify_fast(
            octs_not_simple, done + octs_simple + mps_ieq, "octs", my_get_expr
        )

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
                "octs+mps",
                my_get_expr,
            )

        # don't use done to simplify octs_simple because
        # nonlinear eqts will remove many useful octs
        octs_simple = self._simplify_slow(
            octs_simple, mps_eqt + octs_mps, "octs_simple", my_get_expr
        )

        done += octs_simple + octs_mps + arr_rels
        return self.__class__(done)

    @classmethod
    def _simpify_fast(cls, ps, others, msg, get_expr):
        """
        Simplify given properties ps (usually a class of invs such as octs or mps)
        using the properties in others, e.g., remove p if others => p
        Note: this task is relatively fast, using multiprocessing
        """
        if len(ps) < 2 or not others:
            return ps

        st = time()
        conj = [get_expr(p) for p in others]
        for p in ps:
            _ = get_expr(p)

        def f(ps):
            return [p for p in ps if not Z3._imply(conj, get_expr(p))]

        wrs = MP.run_mp(
            f"_simpify_fast {len(ps)} {msg}", ps, f, settings.DO_MP)

        Miscs.show_removed(f"_simpify_fast {msg}", len(
            ps), len(wrs), time() - st)
        ps = [p for p in wrs]
        return ps

    @classmethod
    def _simplify_slow(cls, ps, others, msg, get_expr):
        """
        Simplify given properties ps using properties in both ps and others
        e.g., remove g if  ps_exclude_g & others => g
        Note: this task is slow
        """

        if len(ps) < 2:
            return ps

        st = time()
        conj = [get_expr(p) for p in others] if others else []
        ps_exprs = [get_expr(p) for p in ps]

        def _imply(js, i):
            iexpr = ps_exprs[i]

            #assert iexpr.decl().kind() != z3.Z3_OP_EQ, iexpr
            jexprs = [ps_exprs[j] for j in js]
            ret = Z3._imply(conj + jexprs, iexpr, is_conj=True)
            # print('{} => {}'.format(jexprs, iexpr))
            return ret

        results = Miscs.simplify_idxs(list(range(len(ps))), _imply)
        results = [ps[i] for i in results]
        Miscs.show_removed(f"_simplify_slow {msg}",
                           len(ps), len(results), time() - st)

        return results

    @classmethod
    def classify(cls, invs):

        import infer.eqt
        import infer.oct
        import infer.mp
        import infer.congruence
        #import data.inv.prepost
        import infer.nested_array

        eqts, eqts_largecoefs, octs, mps, congruences, falseinvs = [], [], [], [], [], []
        arr_rels = []
        for inv in invs:
            mylist = None
            if isinstance(inv, infer.eqt.Eqt):
                if len(Miscs.get_coefs(inv.inv.lhs)) > 10:
                    mylist = eqts_largecoefs
                else:
                    mylist = eqts
            elif isinstance(inv, infer.oct.Oct):
                mylist = octs
            elif isinstance(inv, infer.mp.MMP):
                mylist = mps
            # elif isinstance(inv, data.inv.prepost.PrePost):
            #     mylist = preposts
            elif isinstance(inv, infer.nested_array.NestedArray):
                mylist = arr_rels
            elif isinstance(inv, infer.congruence.Congruence):
                mylist = congruences
            else:
                assert isinstance(inv, FalseInv), inv
                mylist = falseinvs

            mylist.append(inv)
        return eqts, eqts_largecoefs, octs, mps, congruences, arr_rels, falseinvs


class DInvs(dict):
    """
    {loc -> Invs}, Invs is a set
    """

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

    def __str__(self, print_stat=False, print_first_n=None):
        ss = []

        for loc in sorted(self):
            eqts, eqts_largecoefs, octs, mps, congruences, \
                arr_rels, falseinvs = self[loc].classify(self[loc])

            ss.append(f"{loc} ({len(self[loc])} invs):")

            def mylen(x):
                return len(str(x))

            invs = (
                sorted(eqts + eqts_largecoefs, key=mylen)
                + sorted(octs, key=mylen)
                + sorted(mps, key=mylen)
                + sorted(congruences, key=mylen)
                + sorted(arr_rels, key=mylen)
                + sorted(falseinvs, key=mylen)
            )

            if print_first_n and print_first_n < len(invs):
                invs = invs[:print_first_n] + ["..."]

            ss.extend(
                f"{i + 1}. {inv if isinstance(inv, str) else inv.__str__(print_stat)}"
                for i, inv in enumerate(invs)
            )

        return "\n".join(ss)

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
        dinvs = DInvs({loc: invs for loc, invs in wrs if invs})
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
        mlog.debug("done simplifying , time {}".format(time() - st))
        dinvs = self.__class__((loc, invs) for loc, invs in wrs if invs)
        Miscs.show_removed("simplify", self.siz, dinvs.siz, time() - st)
        return dinvs

    @classmethod
    def mk_false_invs(cls, locs):
        dinvs = cls()
        for loc in locs:
            dinvs.add(loc, FalseInv.mk())
        return dinvs

    @classmethod
    def mk(cls, loc, invs):
        assert isinstance(invs, Invs), invs
        new_invs = cls()
        new_invs[loc] = invs
        return new_invs
