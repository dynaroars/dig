import os.path
import sage.all
from sage.all import cached_function
import z3
import vcommon as CM
from miscs import Miscs, Z3
import settings
mlog = CM.getLogger(__name__, settings.logger_level)

"""
Data structures
"""


class Prog(object):
    def __init__(self, exeCmd, traceDir, invDecls):
        assert isinstance(exeCmd, str), exeCmd
        assert os.path.isdir(traceDir), traceDir
        assert isinstance(invDecls, dict), invDecls

        self.exeCmd = exeCmd
        self.traceDir = traceDir
        self.invDecls = invDecls

    def getTraces(self, inps):
        """
        Run program on inps and get traces
        """
        assert isinstance(inps, Inps) and inps, inps

        tcsFile = str(hash(inps.__str__(printDetails=True))
                      ).replace("-", "_") + ".tcs"
        tcsFile = os.path.join(self.traceDir, tcsFile)
        if os.path.isfile(tcsFile):
            traces = DTraces.parse(tcsFile, self.invDecls)
        else:
            for inp in inps:
                inp_ = (v if isinstance(v, int) or v.is_integer() else v.n()
                        for v in inp.vs)
                inp_ = ' '.join(map(str, inp_))
                cmd = "{} {} >> {}".format(self.exeCmd, inp_, tcsFile)
                mlog.debug(cmd)
                CM.vcmd(cmd)
            traces = DTraces.parse(tcsFile, self.invDecls)

        assert all(loc in self.invDecls for loc in traces), traces.keys()
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

    def expr(self, useReals):
        try:
            return self._expr
        except AttributeError:
            self._expr = Z3.toZ3(self.sageExpr, useReals, useMod=False)
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

    def exprs(self, useReals):
        try:
            return self._exprs
        except AttributeError:
            self._exprs = [s.expr(useReals) for s in self]
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


class _Trace(tuple):
    """"
    (3, 4, (7,8))
    """
    maxVal = 100000000

    def __new__(cls, ss, vs):
        assert all(isinstance(s, str) for s in ss) and \
            isinstance(ss, tuple) and (vs, tuple) and \
            len(ss) == len(vs) and ss, (ss, vs)
        return super(_Trace, cls).__new__(cls, (ss, vs))

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

        # VU: todo, temp fix,  disable traces that wih extreme large values
        # (see geo1 e.g., 435848050)
        if any(x > self.maxVal for x in self.vs):
            mlog.debug("skip trace with large val: {}".format(self))
            return True

        # Vu: todo, temp fix, disable repeating rational when testing equality
        if (Miscs.isEq(inv) and
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
        assert Miscs.isExpr(term), term
        rs = term.subs(self.mydict)
        return rs

    @classmethod
    def parse(cls, ss, vs):
        assert isinstance(ss, (tuple, list)), ss
        assert isinstance(vs, (tuple, list)), vs

        vs = tuple(Miscs.ratOfStr(t) for t in vs)
        return _Trace(ss, vs)

    @classmethod
    def fromDict(cls, d):
        # {'y': 1, 'x': 2, 'r': 2, 'b': 2}
        ss = tuple(sorted(d))
        vs = tuple(d[s] for s in ss)
        return _Trace(ss, vs)

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
        assert all(isinstance(t, _Trace) for t in myset), myset
        super(Traces, self).__init__(myset)

    def __contains__(self, trace):
        assert isinstance(trace, _Trace), trace
        return super(Traces, self).__contains__(trace)

    def add(self, trace):
        assert isinstance(trace, _Trace), trace
        return super(Traces, self).add(trace)

    def test(self, inv):
        assert inv.is_relational(), inv
        for trace in self:
            if not trace.test(inv):
                return trace
        return None

    def myeval(self, term):
        assert Miscs.isExpr(term), term
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

        cexs = [_Trace.fromDict(cex) for cex in cexs]
        cexs = Traces(cexs)
        return cexs

    @property
    def mydicts(self):
        return (trace.mydict for trace in self)

    def instantiate(self, term, nTraces):
        assert Miscs.isExpr(term), term
        assert nTraces is None or nTraces >= 1, nTraces

        if nTraces is None:
            for t in self.mydicts:
                exprs = set(term.subs(t) for t in self.mydicts)
        else:
            nTracesExtra = nTraces*5
            exprs = set()
            for i, t in enumerate(self.mydicts):
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
                t = _Trace(newss, newvs)
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

        newInps = [_Trace(ss, inp) for inp in newInps]
        newInps = set(inp for inp in newInps if inp not in self)
        for inp in newInps:
            self.add(inp)
        return Inps(newInps)


class DTraces(dict):
    """
    {loc: Traces}
    """
    inpMaxV = settings.inpMaxV

    @property
    def siz(self): return sum(map(len, self.itervalues()))

    def __str__(self, printDetails=False):
        return "\n".join("{}: {}".format(loc, traces.__str__(printDetails))
                         for loc, traces in self.iteritems())

    def add(self, loc, trace):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(trace, _Trace), trace

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
                _ = newTraces.add(loc, trace)
        return newTraces

    @classmethod
    def parse(cls, tracefile, invdecls):
        """
        parse trace for new traces
        """
        assert isinstance(tracefile, str), tracefile
        assert isinstance(invdecls, dict) and invdecls, invdecls

        dtraces = DTraces()
        for l in CM.iread_strip(tracefile):
            # 22: 8460 16 0 1 16 8460
            parts = l.split(':')
            assert len(parts) == 2, parts
            loc, tracevals = parts[0], parts[1]
            loc = loc.strip()  # 22
            ss = invdecls[loc].names
            vs = tracevals.strip().split()
            trace = _Trace.parse(ss, vs)
            dtraces.add(loc, trace)
        return dtraces


class Inv(object):
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
            self.resetStat()
        else:
            self.stat = stat

    @property
    def isEq(self):
        return Miscs.isEq(self.inv)

    def __str__(self, printStat=False):
        if Miscs.isExpr(self.inv):
            s = Inv.strOfExp(self.inv)
        else:
            # inv = 0
            s = str(self.inv)

        if printStat:
            s = "{} {}".format(s, self.stat)
        return s

    def __hash__(self): return hash(self.inv)

    def __repr__(self): return repr(self.inv)

    def __eq__(self, o): return self.inv.__eq__(o.inv)

    def __ne__(self, o): return not self.inv.__eq__(o.inv)

    def getStat(self): return self._stat

    def setStat(self, stat):
        assert stat in {self.PROVED, self.DISPROVED, self.UNKNOWN}, stat
        self._stat = stat
    stat = property(getStat, setStat)

    def resetStat(self):
        self._stat = None

    def expr(self, useReals):
        """
        cannot make this as property because z3 expr is ctype,
        not compat with multiprocessing Queue
        """
        if self.inv == 0:
            expr = z3.BoolVal(False)
        else:
            expr = Z3.toZ3(self.inv, useReals, useMod=False)
        return expr

    @property
    def isProved(self): return self.stat == self.PROVED

    @property
    def isDisproved(self): return self.stat == self.DISPROVED

    @property
    def isUnknown(self): return self.stat == self.UNKNOWN

    @classmethod
    def mkFalse(cls): return cls(0)

    @cached_function
    def strOfExp(p):
        """
        -p^3 => -(p*p*p)
        n*p^4 => n*(p*p*p*p)
        ab^3 => (ab*ab*ab)
        x*y*z^3 => x*y*(z*z*z)
        """
        assert Miscs.isExpr(p), p

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


class Invs(set):
    def __str__(self, printStat=False):
        invs = sorted(self, reverse=True, key=lambda inv: inv.isEq)
        return ', '.join(inv.__str__(printStat) for inv in invs)

    @property
    def nEqs(self):
        return len([inv for inv in self if inv.isEq])

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

    @classmethod
    def mk(cls, invs):
        newInvs = Invs()
        for inv in invs:
            assert isinstance(inv, Inv)
            newInvs.add(inv)
        return newInvs


class DInvs(dict):
    @property
    def invs(self):
        return (inv for invs in self.itervalues() for inv in invs)

    @property
    def siz(self): return sum(map(len, self.itervalues()))

    @property
    def nEqs(self): return sum(invs.nEqs for invs in self.itervalues())

    def __str__(self, printStat=False):
        return "\n".join("{}: {}".format(loc, self[loc].__str__(printStat))
                         for loc in sorted(self))

    def add(self, loc, inv):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(inv, Inv), inv

        if loc not in self:
            self[loc] = Invs()
        return self[loc].add(inv)

    def __setitem__(self, loc, invs):
        assert isinstance(loc, str) and loc, loc
        assert isinstance(invs, Invs), invs

        super(DInvs, self).__setitem__(loc, invs)

    def merge(self, dinvs):
        assert isinstance(dinvs, DInvs), dinvs
        for loc in dinvs:
            for inv in dinvs[loc]:
                if not inv.isDisproved:
                    self.add(loc, inv)

    def removeDisproved(self):
        dinvs = self.__class__()
        for loc in self:
            for inv in self[loc]:
                if not inv.isDisproved:
                    dinvs.add(loc, inv)
        return dinvs

    def testTraces(self, dtraces):
        assert isinstance(dtraces, DTraces)

        dinvs = self.__class__()
        for loc in self:
            assert loc not in dinvs
            dinvs[loc] = Invs()
            for inv in self[loc]:
                if dtraces[loc].test(inv.inv) is None:  # all pass
                    dinvs[loc].add(inv)
                else:
                    mlog.debug("{}: {} disproved".format(loc, inv))

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

    @classmethod
    def mkFalses(cls, locs, ntimes=1):
        dinvs = cls()
        for loc in locs:
            dinvs.add(loc, Inv.mkFalse())
        return dinvs

    @classmethod
    def mk(cls, loc, invs):
        assert isinstance(invs, Invs), invs
        newInvs = cls()
        newInvs[loc] = invs
        return newInvs
