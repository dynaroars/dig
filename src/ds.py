from abc import ABCMeta, abstractmethod
from time import time
import settings
from miscs import Miscs, Z3
import vcommon as CM
import z3
import sage.all
from sage.all import cached_function
import pdb
import operator
trace = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)

"""
Data structures
"""


class Prog(object):
    def __init__(self, exe_cmd, inv_decls):
        assert isinstance(exe_cmd, str), exe_cmd
        assert isinstance(inv_decls, dict), inv_decls

        self.exe_cmd = exe_cmd
        self.inv_decls = inv_decls
        self.cache = {}  # inp -> traces (str)

    def getTraces(self, inps):
        """
        Run program on inps and get traces
        """
        assert isinstance(inps, Inps) and inps, inps
        trace_str = []
        for inp in inps:
            if inp in self.cache:
                results = self.cache[inp]
            else:
                inp_ = (v if isinstance(v, int) or v.is_integer() else v.n()
                        for v in inp.vs)
                inp_ = ' '.join(map(str, inp_))
                cmd = "{} {}".format(self.exe_cmd, inp_)
                mlog.debug(cmd)
                results, _ = CM.vcmd(cmd)
                results = results.splitlines()
                self.cache[inp] = results
            trace_str.extend(results)

        traces = DTraces.parse(trace_str, self.inv_decls)

        assert all(loc in self.inv_decls for loc in traces), traces.keys()
        return traces


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
            self._expr = Z3.toZ3(self.sageExpr, use_reals, useMod=False)
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
        %%%indicator double x , double y .. ->  {x: int, y: double}
        where x and y are SAGE's symbolic variables
        """
        assert isinstance(s, str), s
        cs = (x.split() for x in s.split(',') if x.strip())
        symbs = [Symb(k.strip(), t.strip()) for t, k in cs]
        cs = Symbs(symbs)
        return cs


class Trace(tuple):
    """"
    (3, 4, (7,8))
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

    def test(self, inv):
        assert inv.is_relational()

        # temp fix: disable traces that wih extreme large values
        # (see geo1 e.g., 435848050)
        if any(x > self.maxVal for x in self.vs):
            mlog.debug("skip trace with large val: {}".format(self))
            return True

        # temp fix: disable repeating rational when testing equality
        if (isinstance(inv, EqtInv) and  # TODO:  THIS IS WRONG, inv is never EqtInv
            any(not x.is_integer() and Miscs.isRepeatingRational(x)
                for x in self.vs)):
            mlog.debug("skip trace with repeating rational {}".format(self))
            return True

        try:
            rs = self.myeval(inv)
            rs = bool(rs)
        except ValueError:
            return False

        return rs

    def myeval(self, term):
        assert Miscs.is_expr(term), term
        rs = term.subs(self.mydict)
        return rs

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

    # def test(self, inv):
    #     assert inv.is_relational(), inv
    #     for trace in self:
    #         if not trace.test(inv):
    #             return trace
    #     return None

    def myeval(self, term):
        assert Miscs.is_expr(term), term
        return [trace.myeval(term) for trace in self]

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

    @classmethod
    def parse(cls, trace_str, invdecls):
        """
        parse trace for new traces
        """
        assert isinstance(trace_str, list), trace_str
        assert isinstance(invdecls, dict) and invdecls, invdecls

        lines = [l.strip() for l in trace_str]
        lines = [l for l in lines if l]

        dtraces = DTraces()
        for l in lines:
            # 22: 8460 16 0 1 16 8460
            parts = l.split(':')
            assert len(parts) == 2, parts
            loc, tracevals = parts[0], parts[1]
            loc = loc.strip()  # 22
            ss = invdecls[loc].names
            vs = tracevals.strip().split()
            trace = Trace.parse(ss, vs)
            dtraces.add(loc, trace)
        return dtraces


class Inv(object):
    __metaclass__ = ABCMeta

    PROVED = "p"
    DISPROVED = "d"
    UNKNOWN = "u"

    def __init__(self, inv, stat=None):
        """
        stat = None means never been checked
        """
        assert inv == 0 or inv.is_relational(), inv
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
        return all(self.test_trace(trace) for trace in traces)

    @property
    def is_proved(self): return self.stat == self.PROVED

    @property
    def is_disproved(self): return self.stat == self.DISPROVED

    @property
    def is_unknown(self): return self.stat == self.UNKNOWN

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
        assert rel.operator() == operator.eq or \
            rel.operator() == operator.le, rel
        super(RelInv, self).__init__(rel, stat)

    def __str__(self, print_stat=False):
        s = Inv.strOfExp(self.inv)
        if print_stat:
            s = "{} {}".format(s, self.stat)
        return s

    def test_trace(self, trace):
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

        return True

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
        assert ieq.operator() == operator.le, ieq
        super(IeqInv, self).__init__(ieq, stat)


class PrePostInv(Inv):
    """
    Set of Preconds  -> PostInv
    """

    def __init__(self, inv, preconds, stat=None):
        assert Miscs.is_eq(inv), inv

        assert isinstance(preconds, Invs), preconds
        super(PrePostInv, self).__init__(inv, stat)

        self.preconds = preconds

    def expr(self, use_reals):
        assert not self.inv == 0, self.inv
        precond_exprs = [c.expr(use_reals) for c in self.preconds]
        not_precond_exprs = [z3.Not(c) for c in precond_exprs]
        postcond_expr = Z3.toZ3(self.inv, use_reals, useMod=False)

        expr = z3.Or(not_precond_exprs + [postcond_expr])
        return expr

    # TODO : need to print stat
    def __str__(self, print_stat=False):
        return "{} => {}".format(
            self.preconds.__str__(delim=" & ", print_stat=False), self.inv)

    def __hash__(self):
        return hash((self.inv, frozenset(self.preconds)))

    def __repr__(self):
        return repr((self.inv, frozenset(self.preconds)))

    def __eq__(self, o):
        return self.inv.__eq__(o.inv) and self.preconds.__eq__(o.preconds)

    def __ne__(self, o): return not self.__eq__(o)


class Invs(set):
    def __init__(self, invs=set()):
        assert all(isinstance(inv, Inv) for inv in invs), invs
        super(Invs, self).__init__(invs)

    def __str__(self, print_stat=False, delim='\n'):
        invs = sorted(self, reverse=True, key=lambda inv: inv.is_eq)
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

        simpl = z3.Tactic('ctx-solver-simplify')
        simplifies = simpl(z3.And([f for f in exprs]))
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

    def simplify(self, invs, use_reals):
        assert invs
        assert isinstance(invs, list), invs
        assert isinstance(use_reals, bool), use_reals


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

    # def test_traces(self, dtraces):
    #     assert(self.siz), self

    #     assert isinstance(dtraces, DTraces)

    #     dinvs = self.__class__()
    #     for loc in self:
    #         assert loc not in dinvs
    #         dinvs[loc] = Invs()
    #         for inv in self[loc]:
    #             if dtraces[loc].test(inv.inv) is None:  # all pass
    #                 dinvs[loc].add(inv)
    #             else:
    #                 mlog.debug("{}: {} failed test".format(loc, inv))

    #     for loc in dinvs:
    #         if not dinvs[loc]:
    #             del dinvs[loc]

    #     return dinvs

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
