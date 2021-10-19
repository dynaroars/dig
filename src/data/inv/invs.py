from time import time
import pdb
from collections import Counter

import z3

import settings
from helpers.miscs import Miscs, MP
from helpers.z3utils import Z3
import helpers.vcommon as CM

import data.inv.base
import data.inv.eqt
import data.inv.oct
import data.inv.mp
import data.inv.prepost
import data.inv.nested_array

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Invs(set):
    def __init__(self, invs=set()):
        assert all(isinstance(inv, data.inv.base.Inv) for inv in invs), invs
        super().__init__(invs)

    def __str__(self, print_stat=False, delim="\n"):
        invs = sorted(
            self, reverse=True, key=lambda inv: isinstance(inv, data.inv.eqt.Eqt)
        )
        return delim.join(inv.__str__(print_stat) for inv in invs)

    def __contains__(self, inv):
        assert isinstance(inv, data.inv.base.Inv), inv
        return super().__contains__(inv)

    @property
    def typ_ctr(self):
        return Counter(inv.__class__.__name__ for inv in self)

    def add(self, inv):
        assert isinstance(inv, data.inv.base.Inv), inv

        not_in = inv not in self
        if not_in:
            super().add(inv)
        return not_in

    def test(self, traces):
        # assert isinstance(traces, Traces)
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

        eqts, eqts_largecoefs, octs, mps, preposts, \
            arr_rels, falseinvs = self.classify(self)

        assert not falseinvs, falseinvs
        assert not preposts, preposts

        exprs_d = {}

        def my_get_expr(p):
            return self.get_expr(p, exprs_d)

        # simplify eqts, e.g., to remove x - y == 0  if -x + y == 0 exists
        eqts = self.simplify2(eqts, None, "eqts", my_get_expr)

        octs_simple, octs_not_simple = [], []
        for oct in octs:
            (octs_simple if oct.is_simple else octs_not_simple).append(oct)

        # find equality invs (==) from min/max-plus
        mps = data.inv.mp.MMP.simplify(mps)
        mps_eqt, mps_ieq = [], []
        for mp in mps:
            (mps_eqt if mp.is_eqt else mps_ieq).append(mp)

        done = eqts + mps_eqt  # don't simply these
        mps_ieq = self.simplify1(mps_ieq, done + octs, "mps_ieq", my_get_expr)
        octs_not_simple = self.simplify1(
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

            octs_mps = self.simplify2(
                octs_mps,
                done + octs_simple,
                "octs+mps",
                my_get_expr,
            )

        # don't use done to simplify octs_simple because
        # nonlinear eqts will remove many useful octs
        octs_simple = self.simplify2(
            octs_simple, mps_eqt + octs_mps, "octs_simple", my_get_expr
        )

        done += octs_simple + octs_mps + arr_rels
        return self.__class__(done)

    @classmethod
    def simplify1(cls, ps, others, msg, get_expr):
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

        wrs = MP.run_mp(f"simplify1 {len(ps)} {msg}", ps, f, settings.DO_MP)

        Miscs.show_removed(f"simplify1 {msg}", len(ps), len(wrs), time() - st)
        ps = [p for p in wrs]
        return ps

    @classmethod
    def simplify2(cls, ps, others, msg, get_expr):
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
        Miscs.show_removed(f"simplify2 {msg}", len(
            ps), len(results), time() - st)

        return results

    @classmethod
    def classify(cls, invs):
        eqts, eqts_largecoefs, octs, mps, preposts, falseinvs = [], [], [], [], [], []
        arr_rels = []
        for inv in invs:
            mylist = None
            if isinstance(inv, data.inv.eqt.Eqt):
                if len(Miscs.get_coefs(inv.inv.lhs)) > 10:
                    mylist = eqts_largecoefs
                else:
                    mylist = eqts
            elif isinstance(inv, data.inv.oct.Oct):
                mylist = octs
            elif isinstance(inv, data.inv.mp.MMP):
                mylist = mps
            elif isinstance(inv, data.inv.prepost.PrePost):
                mylist = preposts
            elif isinstance(inv, data.inv.nested_array.NestedArray):
                mylist = arr_rels
            else:
                assert isinstance(inv, data.inv.invs.FalseInv), inv
                mylist = falseinvs

            mylist.append(inv)
        return eqts, eqts_largecoefs, octs, mps, preposts, arr_rels, falseinvs


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
        return self.typ_ctr[data.inv.eqt.Eqt.__name__]

    def __str__(self, print_stat=False, print_first_n=None):
        ss = []

        for loc in sorted(self):
            eqts, eqts_largecoefs, octs, mps, preposts, \
                arr_rels, falseinvs = self[loc].classify(self[loc])

            ss.append(f"{loc} ({len(self[loc])} invs):")

            def mylen(x):
                return len(str(x))

            invs = (
                sorted(eqts + eqts_largecoefs, key=mylen)
                + sorted(preposts, key=mylen)
                + sorted(octs, key=mylen)
                + sorted(mps, key=mylen)
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
        assert isinstance(inv, data.inv.base.Inv), inv

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


class FalseInv(data.inv.base.Inv):
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

    @classmethod
    def mk(cls):
        return FalseInv(0)

    def test_single_trace(self, trace):
        """
        fake place holder because test_single_trace is an abstract method
        """
        return False
