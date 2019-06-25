from abc import ABCMeta, abstractmethod
from time import time
import pdb
import operator

import z3
import sage.all
from sage.all import cached_function

import helpers.vcommon as CM
import settings
from helpers.miscs import Miscs, Z3
from data.traces import Trace, Traces, DTraces

dbg = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Inv(object):
    __metaclass__ = ABCMeta

    PROVED = "p"
    DISPROVED = "d"
    UNKNOWN = "u"

    def __init__(self, inv, stat=None):
        """
        stat = None means never been checked
        """
        assert (inv == 0  # FalseInv
                or (isinstance(inv, tuple)
                    and (len(inv) == 2  # PrePost
                         or len(inv) == 4))  # Max/MinPlus
                or inv.is_relational()), inv

        assert stat in {None, Inv.PROVED, Inv.DISPROVED, Inv.UNKNOWN}

        self.inv = inv
        if stat is None:
            self.reset_stat()
        else:
            self.stat = stat

    def __hash__(self): return hash(self.inv)

    def __repr__(self): return repr(self.inv)

    def __eq__(self, o): return self.inv.__eq__(o.inv)

    def __ne__(self, o): return not self.inv.__eq__(o.inv)

    def get_stat(self):
        return self._stat

    def set_stat(self, stat):
        assert stat in {self.PROVED, self.DISPROVED, self.UNKNOWN}, stat
        self._stat = stat
    stat = property(get_stat, set_stat)

    def reset_stat(self):
        self._stat = None

    @property
    def is_ieqinv(self): return False

    @property
    def is_eqt(self): return False

    @property
    def is_mpinv(self): return False

    @property
    def is_falseinv(self): return False

    @property
    def is_prepost(self): return False

    def test(self, traces):
        assert isinstance(traces, Traces), traces
        return all(self.test_single_trace(trace) for trace in traces)

    @property
    def is_proved(self): return self.stat == self.PROVED

    @property
    def is_disproved(self): return self.stat == self.DISPROVED

    @property
    def is_unknown(self): return self.stat == self.UNKNOWN


class Invs(set):
    def __init__(self, invs=set()):
        assert all(isinstance(inv, Inv) for inv in invs), invs
        super(Invs, self).__init__(invs)

    def __str__(self, print_stat=False, delim='\n'):
        invs = sorted(self, reverse=True,
                      key=lambda inv: inv.is_eqt)
        return delim.join(inv.__str__(print_stat) for inv in invs)

    def __contains__(self, inv):
        assert isinstance(inv, Inv), inv
        return super(Invs, self).__contains__(inv)

    @property
    def n_eqs(self):
        return len([inv for inv in self if inv.is_eqt])

    # PUBLIC
    def add(self, inv):
        assert isinstance(inv, Inv), inv
        notIn = False
        if inv not in self:
            notIn = True
            super(Invs, self).add(inv)
        return notIn

    def test(self, traces):
        assert isinstance(traces, Traces)
        assert(self), self

        def f(tasks):
            return [(inv, inv.test(traces)) for inv in tasks]
        wrs = Miscs.run_mp("test", list(self), f)
        invs = self.__class__([inv for inv, passed in wrs if passed])
        return invs

    def uniqify(self, use_reals):
        assert isinstance(use_reals, bool), use_reals

        eqts, eqtsLargeCoefs, ieqs, mps, others = self._classify()
        non_mps = eqts + ieqs + others

        if non_mps and len(mps) >= 2:  # parallelizing uniqifying mps
            non_mps_exprs = [e.expr(use_reals) for e in non_mps]

            def f(mps):
                return [mp for mp in mps
                        if not Z3._imply(non_mps_exprs, mp.expr(use_reals))]
            wrs = Miscs.run_mp("uniqifying {} mps".format(len(mps)), mps, f)

            mps = [mp for mp in wrs]

        rs = self._uniq(non_mps + mps, use_reals)
        return Invs(rs + eqtsLargeCoefs)

    # PRIVATE
    @classmethod
    def _uniq(cls, invs, use_reals):
        mlog.debug("uniq {} invs".format(len(invs)))

        def _imply(i, xclude):
            me = invs[i].expr(use_reals)
            others = [invs[j].expr(use_reals) for j in xclude]
            return Z3._imply(others, me)

        rs = set(range(len(invs)))
        for i in range(len(invs)):
            if i not in rs:
                continue
            xclude = rs - {i}
            if xclude and _imply(i, xclude):
                rs = xclude
        rs = [invs[i] for i in sorted(rs)]
        return rs

    def _classify(self):
        eqts, eqtsLargeCoefs, ieqs, mps, others = [], [], [], [], []
        for inv in self:
            if inv.is_eqt:
                if len(Miscs.getCoefs(inv.inv)) > 10:
                    eqtsLargeCoefs.append(inv)
                else:
                    eqts.append(inv)
            elif inv.is_ieqinv:
                ieqs.append(inv)
            elif inv.is_mpinv:
                mps.append(inv)
            else:
                others.append(inv)
        return eqts, eqtsLargeCoefs, ieqs, mps, others


class DInvs(dict):
    """
    {loc -> Invs}  , Invs is a set
    """

    def __setitem__(self, loc, invs):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(invs, Invs), invs

        super(DInvs, self).__setitem__(loc, invs)

    @property
    def invs(self):
        return (inv for invs in self.itervalues() for inv in invs)

    @property
    def siz(self): return sum(map(len, self.itervalues()))

    @property
    def n_eqs(self): return sum(invs.n_eqs for invs in self.itervalues())

    def __str__(self, print_stat=False, print_first_n=None):
        ss = []

        for loc in sorted(self):
            eqts, ieqs, mps, others = [], [], [], []
            for inv in self[loc]:
                if inv.is_eqt:
                    eqts.append(inv)
                elif inv.is_ieqinv:
                    ieqs.append(inv)
                elif inv.is_mpinv:
                    mps.append(inv)
                else:
                    assert inv.is_falseinv or inv.is_prepost, inv

                    others.append(inv)

            ss.append("{} ({} invs):".format(loc, len(self[loc])))
            invs = sorted(eqts, reverse=True) + \
                sorted(ieqs, reverse=True) + \
                sorted(mps, reverse=True) + \
                sorted(others, reverse=True)

            if print_first_n and print_first_n < len(invs):
                invs = invs[:print_first_n] + ['...']

            ss.extend("{}. {}".format(
                i+1,
                inv if isinstance(inv, str) else inv.__str__(print_stat))
                for i, inv in enumerate(invs))

        return '\n'.join(ss)

    def add(self, loc, inv):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(inv, Inv), inv

        if loc not in self:
            self[loc] = Invs()
        return self[loc].add(inv)

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
        assert isinstance(dtraces, DTraces)
        assert(self.siz), self

        st = time()
        tasks = [loc for loc in self if self[loc]]

        def f(tasks):
            return [(loc, self[loc].test(dtraces[loc])) for loc in tasks]

        wrs = Miscs.run_mp("test_dinvs", tasks, f)
        dinvs = DInvs([(loc, invs) for loc, invs in wrs if invs])
        show_removed(self.siz, dinvs.siz, st)
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

    def uniqify(self, use_reals):
        assert isinstance(use_reals, bool), use_reals
        assert(self.siz), self

        st = time()
        tasks = list(self.keys())

        def f(tasks):
            return [(loc, self[loc].uniqify(use_reals)) for loc in tasks]
        wrs = Miscs.run_mp("uniqify", tasks, f)

        dinvs = self.__class__((loc, invs) for loc, invs in wrs if invs)
        show_removed(self.siz, dinvs.siz, st)
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
        newInvs = cls()
        newInvs[loc] = invs
        return newInvs


def show_removed(orig_siz, new_siz, st):
    assert orig_siz >= new_siz, (orig_siz, new_siz)
    n_removed = orig_siz - new_siz
    if n_removed:
        mlog.debug("removed {} invs ({}s, orig {}, new {})"
                   .format(n_removed, time() - st, orig_siz, new_siz))


class FalseInv(Inv):
    def __init__(self, inv, stat=None):
        assert inv == 0, inv
        super(FalseInv, self).__init__(inv, stat)

    def __str__(self, print_stat=False):
        s = str(self.inv)
        if print_stat:
            s = "{} {}".format(s, self.stat)
        return s

    def expr(self, _):
        return z3.BoolVal(False)

    @classmethod
    def mk(cls):
        return FalseInv(0)

    @property
    def is_falseinv(self):
        return True


class RelInv(Inv):
    __metaclass__ = ABCMeta

    def __init__(self, rel, stat=None):
        assert (rel.operator() == operator.eq or
                rel.operator() == operator.le or
                rel.operator() == operator.lt), rel

        super(RelInv, self).__init__(rel, stat)

    def __str__(self, print_stat=False):
        s = self.strOfExp(self.inv)
        if print_stat:
            s = "{} {}".format(s, self.stat)
        return s

    @cached_function
    def strOfExp(p):
        """
        -p^3 => -(p*p*p)
        n*p^4 => n*(p*p*p*p)
        ab^3 => (ab*ab*ab)
        x*y*z^3 => x*y*(z*z*z)
        """
        assert Miscs.is_expr(p), p

        def getPow(p):
            try:
                oprs = p.operands()
            except Exception:
                return []

            if p.operator() == sage.all.operator.pow:
                x, y = oprs
                pow_s = '*'.join(
                    [str(x) if x.is_symbol() else "({})".format(x)] * int(y))
                return [(str(p), '({})'.format(pow_s))]

            else:
                return [xy for o in oprs for xy in getPow(o)]

        s = str(p)
        if '^' not in s:
            return s
        rs = getPow(p)
        for (x, y) in rs:
            s = s.replace(x, y)
        return s

    def test_single_trace(self, trace):
        assert isinstance(trace, Trace), trace

        # temp fix: disable traces that wih extreme large values
        # (see geo1 e.g., 435848050)
        if any(x > trace.maxVal for x in trace.vs):
            mlog.debug("skip trace with large val: {}".format(self))
            return True

        # temp fix: disable repeating rational when testing equality
        if (self.is_eqt and
            any(not x.is_integer() and Miscs.isRepeatingRational(x)
                for x in trace.vs)):
            mlog.debug("skip trace with repeating rational {}".format(self))
            return True

        try:
            bval = self.inv.subs(trace.mydict)
            bval = bool(bval)
            return bval
        except ValueError:
            mlog.debug("{}: failed test".format(self))
            return False

    def expr(self, use_reals):
        """
        cannot make this as property because z3 expr is ctype,
        not compat with multiprocessing Queue
        """
        return Z3.toZ3(self.inv, use_reals, use_mod=False)
