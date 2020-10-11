import sage.all
from sage.all import cached_function
import vu_common as CM
from sageutil import is_sage_expr, get_vars
from miscs import Miscs
import settings
logger = CM.VLog('ds')
logger.level = settings.logger_level  
logger.printtime = settings.logger_printtime

"""
Data structures
"""

class Inp(tuple): pass

class Inps(set):
    def __init__(self, myset=set()): super(Inps, self).__init__(myset)

    def __contains__(self, inp):
        assert isinstance(inp, Inp), inp
        return super(Inps, self).__contains__(inp)

    def add(self, inp):
        assert isinstance(inp, Inp), inp
        return super(Inps, self).add(inp)

class _Trace(tuple):
    #private class
    def mydict(self, vs):
        assert isinstance(vs, tuple) and vs, vs
        try:
            d = self._mydict[vs]
            return d
        except AttributeError:
            self._mydict = {vs: dict(zip(vs, self))}
        except KeyError:
            self._mydict[vs] = dict(zip(vs, self))
        return self._mydict[vs]

    def test(self, inv, vs):
        assert inv.is_relational()
        #VU: todo, temp fix,  disable traces that wih extreme large values (see geo1 e.g.,)
        #435848050
        if any(x > 100000000 for x in self):
            return True
        return bool(self.myeval(inv, vs))

    def myeval(self, term, vs):
        assert is_sage_expr(term), term
        return term.subs(self.mydict(vs))

    @classmethod
    def parse(cls, tracevals):
        assert isinstance(tracevals, (tuple, list)), tracevals
        return _Trace(map(Miscs.ratOfStr, tracevals))        
    
class Traces(set):
    def __init__(self, vs, myset=set()):
        super(Traces, self).__init__(myset)
        self.vs = vs
        
    @property
    def vs(self): return self._vs
    @vs.setter
    def vs(self, myvs):
        assert myvs, myvs
        self._vs = myvs
        
    def __contains__(self, trace):
        assert isinstance(trace, _Trace), trace
        return super(Traces, self).__contains__(trace)

    def add(self, trace):
        assert isinstance(trace, _Trace), trace
        return super(Traces, self).add(trace)

    def test(self, inv):
        assert inv.is_relational(), inv
        for trace in self:
            if not trace.test(inv, self.vs):
                #print inv, trace, self.vs
                return trace
        return None

    def myeval(self, term):
        assert is_sage_expr(term), term
        return [trace.myeval(term, self.vs) for trace in self]
            
    def __str__(self, printDetails=False):
        if printDetails:
            return ", ".join(map(str, sorted(self)))
        else:
            return str(len(self))

    @classmethod
    def extract(cls, dcexs, vs, useOne=True):
        """
        dCexs is a dict{inv: set(tuple}}
        for each disproved inv, use just 1 cex
        """
        if useOne:
            cexs = [dcexs[inv].pop() for inv in dcexs]
        else:
            cexs = [cex for inv in dcexs for cex in dcexs[inv]]
        cexs = Traces(vs, set([_Trace.parse(tracevals) for tracevals in cexs]))
        return cexs
        

    @property
    def mydicts(self):
        return (trace.mydict(self.vs) for trace in self)


    def instantiate(self, term, nTraces):
        assert is_sage_expr(term), term
        assert nTraces is None or nTraces >= 1, nTraces

        
        if nTraces is None:
            exprs = set(term.subs(t) for t in self.mydicts)            
        else:
            nTracesExtra = nTraces*5
            exprs = set()
            for i,t in enumerate(self.mydicts):
                expr = term.subs(t)
                if expr not in exprs:
                    exprs.add(expr)
                    if len(exprs) >= nTracesExtra:
                        break

            #instead of doing this, can find out the # 0's in traces
            #the more 0's , the better
            exprs = sorted(exprs, key=lambda expr:len(get_vars(expr)))
            exprs = set(exprs[:nTraces])
        return exprs        

        
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
    
    def add(self, loc, trace, invdecls):
        assert isinstance(loc, str), loc
        assert isinstance(trace, _Trace), trace

        if loc not in self:
            traces = Traces(tuple(invdecls[loc]))
            self[loc] = traces
            
        notIn = trace not in self[loc]
        if notIn: self[loc].add(trace)
        return notIn

    def update(self, traces, invdecls):
        """
        Update dtraces to contain contents of self and return diffs
        """
        assert isinstance(traces, DTraces), traces
        assert isinstance(invdecls, dict) and invdecls, invdecls
        
        newTraces = DTraces()
        for loc in self:
            for trace in self[loc]:
                notIn = traces.add(loc, trace, invdecls)
                if notIn:
                    _ = newTraces.add(loc, trace, invdecls)
                else:
                    logger.detail("{} exist".format(trace))
        
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
            #l22: 8460 16 0 1 16 8460
            parts = l.split(':')
            assert len(parts) == 2, parts
            lineno = parts[0].strip()  #l22
            tracevals = parts[1].strip().split()
            trace = _Trace.parse(tracevals)
            dtraces.add(lineno, trace, invdecls)
        return dtraces


class Inv(object):
    PROVED = "p"
    DISPROVED = "d"
    UNKNOWN = "u"
    
    def __init__(self, inv):
        assert inv == 0 or inv == 1 or inv.is_relational(), inv
        self.inv = inv
        self.resetStat()
        
    def __str__(self, printStat=False):

        if is_sage_expr(self.inv):
            s = Inv.strOfExp(self.inv)
        else:
            s = str(self.inv)

        if printStat: s = "{} {}".format(s, self.stat)
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

    def resetStat(self): self._stat = None
        
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
        assert is_sage_expr(p), p
        
        def getPow(p):
            try:
                oprs = p.operands()
            except Exception:
                return []

            if p.operator() == sage.all.operator.pow:
                x,y = oprs
                pow_s = '*'.join(
                    [str(x) if x.is_symbol() else "({})".format(x)] * int(y))
                return [(str(p), '({})'.format(pow_s))]

            else:
                return [xy for o in oprs for xy in getPow(o)]

        s = str(p)
        if '^' not in s:
            return s
        rs = getPow(p)
        for (x,y) in rs: s = s.replace(x,y)
        return s    

class Invs(set):
    def __str__(self, printStat=False):
        return ", ".join(map(lambda inv: inv.__str__(printStat), sorted(self)))

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
    def siz(self): return sum(map(len, self.itervalues()))

    def __str__(self, printStat=False):
        return "\n".join("{}: {}".format(loc, invs.__str__(printStat))
                         for loc, invs in self.iteritems())

    def add(self, loc, inv):
        assert isinstance(loc, str), loc
        assert isinstance(inv, Inv), inv

        if loc not in self:
            self[loc] = Invs()
        return self[loc].add(inv)

    def __setitem__(self, loc, invs):
        assert isinstance(loc, str), loc
        assert isinstance(invs, Invs), invs
        
        super(DInvs, self).__setitem__(loc, invs)

    def resetStats(self):
        for loc in self:
            for inv in self[loc]:
                inv.resetStat()
        
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
                if dtraces[loc].test(inv.inv) is None: #all pass
                    dinvs[loc].add(inv)
                else:
                    logger.warn("{}: {} disproved".format(loc, inv))

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
    def mkFalses(cls, locs):
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
