from abc import ABCMeta, abstractmethod
from time import time
import pdb
import operator

import z3
import sage.all
from sage.all import cached_function

import vcommon as CM
import settings
from miscs import Miscs, Z3

from ds import Trace, Traces, DTraces
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
                or (isinstance(inv, tuple) and len(inv) == 2)  # PrePost
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

    def test(self, traces):
        assert isinstance(traces, Traces), traces
        return all(self.test_single_trace(trace) for trace in traces)

    @property
    def is_proved(self): return self.stat == self.PROVED

    @property
    def is_disproved(self): return self.stat == self.DISPROVED

    @property
    def is_unknown(self): return self.stat == self.UNKNOWN


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
        if (isinstance(self, EqtInv) and
            any(not x.is_integer() and Miscs.isRepeatingRational(x)
                for x in trace.vs)):
            mlog.debug("skip trace with repeating rational {}".format(self))
            return True

        try:
            rs = self.inv.subs(trace.mydict)
            rs = bool(rs)
        except ValueError:
            mlog.debug("{}: failed test".format(self))
            return False

        return rs

    def expr(self, use_reals):
        """
        cannot make this as property because z3 expr is ctype,
        not compat with multiprocessing Queue
        """
        return Z3.toZ3(self.inv, use_reals, useMod=False)


class EqtInv(RelInv):
    def __init__(self, eqt, stat=None):
        assert eqt.operator() == operator.eq, eqt
        super(EqtInv, self).__init__(eqt, stat)


class IeqInv(RelInv):
    def __init__(self, ieq, stat=None):
        """
        For both <=  (normal OctInvs)  or < (Precond in PrePost)
        """
        assert (ieq.operator() == operator.le or
                ieq.operator() == operator.lt), ieq

        super(IeqInv, self).__init__(ieq, stat)


class PrePostInv(Inv):
    """
    Set of Preconds  -> PostInv
    """

    def __init__(self, preconds, postcond, stat=None):
        assert isinstance(preconds, Invs), preconds
        assert isinstance(postcond, EqtInv), postcond

        super(PrePostInv, self).__init__(
            (frozenset(preconds), postcond), stat)

        self.preconds = preconds
        self.postcond = postcond

    def expr(self, use_reals):
        """
        And(preconds) -> postcond
        """
        pre = z3.And([c.expr(use_reals) for c in self.preconds])
        post = c.expr(use_reals)
        return z3.Implies(pre, post)

    def __str__(self, print_stat=False):
        return "{} => {} {}".format(
            self.preconds.__str__(delim=" & "), self.postcond, self.stat)


class Invs(set):
    def __init__(self, invs=set()):
        assert all(isinstance(inv, Inv) for inv in invs), invs
        super(Invs, self).__init__(invs)

    def __str__(self, print_stat=False, delim='\n'):
        invs = sorted(self, reverse=True,
                      key=lambda inv: isinstance(inv, EqtInv))
        return delim.join(inv.__str__(print_stat) for inv in invs)

    @property
    def n_eqs(self):
        return len([inv for inv in self if isinstance(inv, EqtInv)])

    def __contains__(self, inv):
        assert isinstance(inv, Inv), inv
        return super(Invs, self).__contains__(inv)

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

        return Invs([inv for inv in self if inv.test(traces)])

    def uniqify(self, use_reals):
        assert isinstance(use_reals, bool), use_reals

        eqts, eqtsLargeCoefs, disjs, others = [], [], [], []
        for inv in self:
            if isinstance(inv, PrePostInv):
                disjs.append(inv)
            elif isinstance(inv, EqtInv):
                if len(Miscs.getCoefs(inv.inv)) > 10:
                    eqtsLargeCoefs.append(inv)
                else:
                    eqts.append(inv)
            else:
                others.append(inv)

        invs = eqts + disjs + others
        if not invs:
            return self

        exprs = [inv.expr(use_reals) for inv in invs]
        myf = z3.And([f for f in exprs])

        simpl = z3.Tactic('ctx-solver-simplify')
        #simpl = z3.Then(z3.Tactic('simplify'), z3.Tactic('solve-eqs'))
        simpl = z3.TryFor(simpl, settings.SOLVER_TIMEOUT * 1000)
        simplifies = simpl(myf)
        simplifies = simplifies[0]
        assert len(simplifies) <= len(invs)

        d = {str(z3.simplify(f)): inv for f, inv in zip(exprs, invs)}
        simplifies_strs = [str(z3.simplify(f)) for f in simplifies]

        results, notdone = [], []
        for simplified in simplifies_strs:
            try:
                inv = d[simplified]
                results.append(inv)
                del d[simplified]
            except KeyError:
                notdone.append(simplified)

        if notdone:
            print(len(results), results)
            print(len(notdone), notdone)
            print(len(d), d)
            raise NotImplementedError("need to use smt checking in this case")

        return Invs(results + eqtsLargeCoefs)

        # disjs = sorted(disjs, key=lambda inv: inv.inv)
        # others = sorted(others, key=lambda inv: inv.inv)
        # invs = others + disjs + eqts

        # def _imply(i, xclude):
        #     me = invs[i].expr(use_reals)
        #     others = [invs[j].expr(use_reals) for j in xclude]
        #     return Z3._imply(others, me)

        # rs = set(range(len(invs)))
        # for i in range(len(invs)):
        #     if i not in rs:
        #         continue
        #     xclude = rs - {i}
        #     if xclude and _imply(i, xclude):
        #         rs = xclude

        # rs = [invs[i] for i in sorted(rs)] + eqtsLargeCoefs
        # return Invs(rs)


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

    def __str__(self, print_stat=False):
        ss = []

        for loc in sorted(self):
            eqts, ieqs, others = [], [], []
            for inv in self[loc]:
                if isinstance(inv, EqtInv):
                    eqts.append(inv)
                elif isinstance(inv, IeqInv):
                    ieqs.append(inv)
                else:
                    assert isinstance(inv, (FalseInv, PrePostInv)), inv

                    others.append(inv)

            ss.append("{} ({} invs):".format(loc, len(self[loc])))
            invs = sorted(eqts, reverse=True) + \
                sorted(ieqs, reverse=True) + \
                sorted(others, reverse=True)
            ss.extend("{}. {}".format(i+1, inv.__str__(print_stat))
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

        dinvs = [(loc, invs.test(dtraces[loc]))
                 for loc, invs in self.iteritems()]
        return DInvs([(loc, invs) for loc, invs in dinvs if invs])

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

        st = time()

        def wprocess(tasks, Q):
            rs = [(loc, self[loc].uniqify(use_reals)) for loc in tasks]
            if Q is None:
                return rs
            else:
                Q.put(rs)

        tasks = list(self.keys())
        wrs = Miscs.runMP("uniqify", tasks, wprocess, chunksiz=1,
                          doMP=settings.doMP and len(tasks) >= 2)

        dinvs = self.__class__((loc, invs) for loc, invs in wrs if invs)

        mlog.debug("uniqify: remove {} redundant invs ({}s)"
                   .format(self.siz - dinvs.siz, time() - st))
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
