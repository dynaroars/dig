import itertools
import sage.all
import random
import vu_common as CM

import settings
logger = CM.VLog('alg')
logger.level = settings.logger_level  

#Exceptions
class NotEnoughTraces(Exception): pass

stripTo = lambda s, to_s: s[s.find(to_s) + 1:].strip() #e.g., ...:x  -> x

def ratOfStr(s):
    """
    Convert the input 's' to a rational number if possible.
    Otherwise returns None

    Examples:

    sage: assert ratOfStr('.3333333') == 3333333/10000000
    sage: assert ratOfStr('3/7') == 3/7
    sage: assert ratOfStr('1.') == 1
    sage: assert ratOfStr('1.2') == 6/5
    sage: assert ratOfStr('.333') == 333/1000
    sage: assert ratOfStr('-.333') == -333/1000
    sage: assert ratOfStr('-12.13') == -1213/100

    #Returns None because cannot convert this str
    sage: ratOfStr('333333333333333s')
    alg:Warn:cannot convert 333333333333333s to rational

    Note: this version seems to be the *fastest*
    among several ones I've tried
    %timeit ratOfStr('322')
    """
    try:
        return sage.all.QQ(s)
    except TypeError:
        pass

    try:
        return sage.all.QQ(sage.all.RR(s))
    except TypeError:
        logger.warn('cannot convert {} to rational'.format(s))
        return None

def getTerms(ss, deg):
    """
    get a list of terms from the given list of vars and deg
    the number of terms is len(rs) == binomial(len(ss)+d, d)

    Note: itertools is faster than Sage's MultichooseNK(len(ss)+1,deg)
    
    sage: ts = getTerms(list(var('a b')), 3)
    sage: assert ts == [1, a, b, a^2, a*b, b^2, a^3, a^2*b, a*b^2, b^3]

    sage: ts = getTerms(list(var('a b c d e f')), 3)
    sage: ts
    [1, a, b, c, d, e, f,
    a^2, a*b, a*c, a*d, a*e, a*f,
    b^2, b*c, b*d, b*e, b*f, c^2, c*d, c*e, c*f,
    d^2, d*e, d*f, e^2, e*f, f^2, a^3, a^2*b, a^2*c, a^2*d, a^2*e,
    a^2*f, a*b^2, a*b*c, a*b*d, a*b*e, a*b*f, a*c^2, a*c*d, a*c*e,
    a*c*f, a*d^2, a*d*e, a*d*f, a*e^2, a*e*f, a*f^2,
    b^3, b^2*c, b^2*d, b^2*e, b^2*f, b*c^2, b*c*d, b*c*e, b*c*f, b*d^2,
    b*d*e, b*d*f, b*e^2, b*e*f, b*f^2, c^3, c^2*d, c^2*e, c^2*f, c*d^2,
    c*d*e, c*d*f, c*e^2, c*e*f, c*f^2, d^3, d^2*e, d^2*f, d*e^2, d*e*f,
    d*f^2, e^3, e^2*f, e*f^2, f^3]

    """
    assert deg >= 0, deg
    assert ss and all(s.is_symbol() for s in ss), ss
    ss_ = ([sage.all.SR(1)] if ss else (sage.all.SR(1),)) + ss
    combs = itertools.combinations_with_replacement(ss_, deg)
    terms = [sage.all.prod(c) for c in combs]
    return terms

        
def strOfExp(p):
    """
    -p^3 => -(p*p*p)
    n*p^4 => n*(p*p*p*p)
    ab^3 => (ab*ab*ab)
    x*y*z^3 => x*y*(z*z*z)
    """

    def getPow(p):
        try:
            oprs = p.operands()
        except Exception:
            return []

        if p.operator() == sage.all.operator.pow:
            x,y = oprs
            pow_s = '*'.join([str(x)
                              if x.is_symbol() else "({})".format(x)] * int(y))
            return [(str(p), '({})'.format(pow_s))]

        else:
            return [xy for o in oprs for xy in getPow(o)]
    
    s = str(p)
    if '^' not in s:
        return s
    rs = getPow(p)
    for (x,y) in rs: s = s.replace(x,y)
    return s


def elim_denom(p):
    """
    Eliminate (Integer) denominators in expression operands.
    Will not eliminate if denominators is a var (e.g.,  (3*x)/(y+2)).

    Examples:

    sage: var('x y z')
    (x, y, z)

    sage: elim_denom(3/4*x^2 + 7/5*y^3)
    28*y^3 + 15*x^2

    sage: elim_denom(-3/2*x^2 - 1/24*z^2 >= (y + 1/7))
    -252*x^2 - 7*z^2 >= 168*y + 24

    sage: elim_denom(-3/(y+2)*x^2 - 1/24*z^2 >= (y + 1/7))
    -1/24*z^2 - 3*x^2/(y + 2) >= y + 1/7

    sage: elim_denom(x + y == 0)
    x + y == 0

    """
    try:
        f = lambda g : [sage.all.Integer(o.denominator()) for o in g.operands()]
        denoms = f(p.lhs()) + f(p.rhs()) if p.is_relational() else f(p)
        return p * sage.all.lcm(denoms)
    except TypeError:
        return p


def checkVals(vs):
    """
    check for big values (likely to cause overflow)
    """
    bigV = 10000
    return all(-1*bigV <= v <= bigV for v in vs)

        
def genDeg(nvs, nts, max_deg=7):
    """
    Generates a degree wrt to a (maximum) number of terms (nss)
    """
    assert nvs >= 1, nvs
    assert nts >= nvs, (nts, nvs)
    assert max_deg >= 1, max_deg

    for d in range(1,max_deg+1):
        if d == max_deg:
            return d
            
        #look ahead
        nterms = sage.all.binomial(nvs + d+1, d+1) 
        if nterms > nts:
            return d


def genInitInps(nInps,maxV):    
    #15,75=   0...15, 15..75, 75..100

    def gen(nInps, ranges):
        """
        genInps(3,[(0,20), (20,120), (120,150)])
        """
        inps = itertools.product(*itertools.repeat(range(len(ranges)), nInps))
        return [[random.randrange(ranges[p][0], ranges[p][1]) for p in inp]
                for inp in inps]
    
    assert maxV >= 0
    p15 = int(maxV*.10)
    p75 = int(maxV*.90)
    a1 = (0, p15)
    a3 = (p75, maxV)
    ranges = [a1,a3]
    return gen(nInps, ranges)
