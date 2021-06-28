from sage.all import *
from sage.all import (QQ, RR, SR, sage_eval, save, load, shuffle, flatten,
                      PolynomialRing, MultichooseNK,prod, binomial, identity_matrix,
                      operator, var, srange, Integer, lcm, ZZ,
                      CartesianProduct, Set)
import logging
import os
import z3

import vu_common as CM
from vu_common import (get_logger,
                       is_str,
                       vset, vpartition,
                       merge_dict,vset)


logger = get_logger('miscs')
logger.setLevel(logging.DEBUG)

class ReadFile(object):
    """
    Read data file and other info (vs, tcs, xinfo)
    """
    def __init__(self, filename):
        """
        Read input files (trace data) and do some preprocessing

        EXAMPLES:

        sage: rf = ReadFile('Examples/t1.tcs',verbose=2)
        *** ReadFile ***
        0. filename: Examples/t1.tcs
        1. verbose: 2
        read 'Examples/t1.tcs'
        number of traces (tcs) read: 6
        read 'Examples/t1.tcs2'
        number of traces (tcs) read: 1
        read 'Examples/t1.ext'
        0. |_tcs|: 6
        1. |_tcs2|: 1
        2. _vs: (x, y)
        3. _xinfo:
        0. All: ['x', 'y']
        1. Assume: [y >= x]
        2. Const: []
        3. Expect: ['2*x + 1 >= y']
        4. ExtFun: []
        5. Global: []
        6. Input: []
        7. Output: []
        """

        if __debug__:
            assert isinstance(filename,str)


        def read_n_filter(filename):
            content = CM.vread(filename).splitlines()
            return ReadFile.filter_content(content)

        content = read_n_filter(filename)
        vs,tcs = ReadFile.get_vs_tcs(content)

        #get additional info
        base_fname = os.path.splitext(filename)[0]


        #get extra info if exists
        ext_file = base_fname + '.ext'
        if os.path.exists(ext_file):
            content = read_n_filter(ext_file)
        else:
            content = []
        xinfo = ReadFile.get_xinfo(vs,content)

        self.vs    = vs
        self.tcs   = tcs
        self.xinfo = xinfo


    # Static methods
    @staticmethod
    def replace_var_name(v, rpVars=['r','n', 'QQ', 'SR', 'Q', 'ZZ']):
        """
        EXAMPLES:

        sage: ReadFile.replace_var_name('n')
        'nvu'
        sage: ReadFile.replace_var_name('z')
        'z'
        sage: ReadFile.replace_var_name('r')
        'rvu'
        sage: ReadFile.replace_var_name('QQ')
        'QQvu'
        sage: ReadFile.replace_var_name('RR')
        'RRvu'
        sage: ReadFile.replace_var_name('rr')
        'rr'
        sage: ReadFile.replace_var_name('n + 3')
        'nvu + 3'
        """
        _replace = lambda x: '{}vu'.format(x) if x in rpVars else x
        v = ' '.join(map(_replace,v.strip().split()))
        return v


    @cached_function
    def check_rounding(s,n_fract=7):
        """
        Returns True if the input number doesn't have rounding imprecision
        that is, if the number of fractional digit is < n_fract

        The reason for this is because in C
        0.0309375 / 2.0 gives 0.0155688 instead of 0.01546875

        EXAMPLES:

        sage: ReadFile.check_rounding('-12342.465223',n_fract=6)
        False
        sage: ReadFile.check_rounding('-12342.465223',n_fract=7)
        True
        sage: ReadFile.check_rounding('-12342.465223')
        True
        sage: ReadFile.check_rounding('-12342.4652233')
        False
        sage: ReadFile.check_rounding('[-12342.465223, -12342.4652233]')
        False
        sage: ReadFile.check_rounding('[1, 2, 3.0001]',n_fract=4)
        False
        sage: ReadFile.check_rounding('[1, 2, 3.0000]',n_fract=4)
        True

        #invalid array format
        sage: ReadFile.check_rounding('[1, 2 3.0000]',n_fract=4)
        Traceback (most recent call last):
        ...
        AssertionError

        """

        def _check_rounding(s,n_fract):
            if __debug__:
                assert CM.isnum(s)

            rs = ('.' in s \
                      and len(s.split('.')[1].rstrip('0')) >= n_fract)

            return not rs


        if ReadFile.is_array(s):
            s = s.replace('[','').replace(']','')
            s = [s_.strip() for s_ in s.split(',')]
            rs = all(_check_rounding(s_,n_fract) for s_ in s)
        else:
            rs = _check_rounding(s,n_fract)

        return rs

    @cached_function
    def strToRatOrList(s):
        return (ReadFile.str2list(s) if ReadFile.is_array(s)
                else ReadFile.str2rat(s))


    @staticmethod
    def is_array(s):
        return s.startswith('[') and s.endswith(']')

    @staticmethod
    def str2list(s):
        """
        Converts a string containing a list of number to proper list format

        EXAMPLES:

        sage: ReadFile.str2list('[1,2,[4, 7, 13, [7,9]]] ')
        [1, 2, [4, 7, 13, [7, 9]]]

        """
        try:
            rs = Miscs.tmap(QQ, sage_eval(s))
            return rs
        except Exception as why:
            print 'W: cannot convert {} to list ({})'.format(s,why)
            return None

    @staticmethod
    def str2rat(s):
        """
        Convert the input 's' to a rational number if possible.
        Otherwise returns None

        EXAMPLES:

        sage: ReadFile.str2rat('333333333333333s')
        W: cannot convert 333333333333333s to rational
        sage: ReadFile.str2rat('.3333333')
        3333333/10000000
        sage: ReadFile.str2rat('3/7')
        3/7
        sage: ReadFile.str2rat('1.')
        1
        sage: ReadFile.str2rat('1.2')
        6/5
        sage: ReadFile.str2rat('.333')
        333/1000
        sage: ReadFile.str2rat('-.333')
        -333/1000
        sage: ReadFile.str2rat('-12.13')
        -1213/100

        Note: this version seems to be the *fastest*
        among several ones I've tried
        %timeit ReadFile.str2rat('322')
        """

        try:
            return QQ(s)
        except TypeError:
            pass

        try:
            return QQ(RR(s))
        except TypeError:
            print 'W: cannot convert {} to rational'.format(s)
            return None


    @staticmethod
    def filter_content(fcontent,
                       ignore_kws=['#','>>>','sage','$'],
                       ignore_after_kw='#MYRESULTS'):
        """
        Filter out unwanted stuff from file

        EXAMPLES:

        sage: len(ReadFile.filter_content(['Hello World','#Ignore Me1', \
        'Name is Vu $Ignore Me2','Hello World',' #  remove this line', \
        '#MYRESULTS','no print']))
        2

        """

        content = [l.strip() for l in fcontent]
        try:
            #ignore everything after
            content = content[:content.index(ignore_after_kw)]
        except ValueError:
            pass

        content = CM.vset(content)
        content = [l for l in content
                   if not any(l.startswith(k) for k in ignore_kws)]


        content = [l.split('#')[0] for l in content]

        content = [l.strip() for l in content]
        content = [l for l in content if l != '']
        return content


    @staticmethod
    def get_vs_tcs(fcontent):
        """
        Get information from fcontent about variables (vs), traces (tcs),
        and other extra info

        EXAMPLES:

        sage: var('w, x, y, z')
        (w, x, y, z)

        sage: vs,ts = ReadFile.get_vs_tcs(['x y z w', '3 7 9.99999999 [8, 9]', '7 8 12 [2, 3]', '-1 9.2 8 [[5,   7], [1,-2]]'])
        W: Skipping 1 tcs having possible rounding imprec vals
        number of traces (tcs) read: 2
        sage: vs == (x, y, z, w) and ts == [{w: [2, 3], z: 12, y: 8, x: 7}, {w: [[5, 7], [1, -2]], z: 8, y: 46/5, x: -1}]
        True

        """

        def _format_str_list(s):
            #change [1, 2, [3, 5]] => [1,2,[3,5]]
            s_ = ', '; s__ = ','
            while s_ in s: s = s.replace(s_, s__)
            return s

        msg = "':' in input (new format requires " +\
            "all fields to be in .ext file)"
        assert all(':' not in l for l in fcontent), msg


        #fcontents
        fcontent = [_format_str_list(l) for l in fcontent]
        fcontent = [l.split() for l in fcontent] #'1 2 3' => ['1','2','3']
        _is_vars = lambda l: all(c[0].isalpha() for c in l)
        tcs, vs = CM.vpartition(fcontent,_is_vars)

        #vars
        assert vs, 'variables cannot be []'
        assert len(CM.vset(vs,repr)) == 1, 'variables set is not unique'
        vs = map(ReadFile.replace_var_name,vs[0])
        vs = var(' '.join(vs))


        #traces
        tcs_old_len = len(tcs)

        #checking for possible rounding imprecision
        ReadFile.check_rounding.clear_cache()
        tcs = [tc for tc in tcs
               if all(ReadFile.check_rounding(t) for t in tc)]


        if tcs_old_len != len(tcs):
            msg = 'W: Skipping {} tcs having possible rounding imprec vals'
            print msg.format(tcs_old_len - len(tcs))


        ReadFile.strToRatOrList.clear_cache()
        tcs = [map(ReadFile.strToRatOrList, tc) for tc in tcs]

        assert tcs, 'tcs cannot be []'

        tcs =  [dict(zip(vs,t)) for t in tcs]

        logger.debug('number of traces (tcs) read: {}'.format(len(tcs)))

        return vs, tcs


    @staticmethod
    def get_xinfo(vs, fcontent):
        """
        EXAMPLES:

        sage: var('x y g f d')
        (x, y, g, f, d)

        sage: sorted(ReadFile.get_xinfo([x,y,g,f,d],['l1', 'Assume: x >= y + 10', 'Assume: x + y > 20','Global: g','Global: f','Global: d']).items())
        [('All', ['x', 'y', 'g', 'f', 'd']),
        ('Assume', [x >= y + 10, x + y > 20]), ('Const', []),
        ('Expect', []), ('ExtFun', []), ('Global', ['g', 'f', 'd']),
        ('Input', []), ('Output', [])]

        sage: sorted(ReadFile.get_xinfo([x,y],[]).items())
        [('All', ['x', 'y']), ('Assume', []),
        ('Const', []), ('Expect', []), ('ExtFun', []),
        ('Global', []), ('Input', []), ('Output', [])]

        """

        xinfoKs = ['Assume', 'Expect', 'Global',
                   'Output', 'Input', 'ExtFun', 'Const']

        xinfoVs = []

        for k in xinfoKs:
            fcontent, v = \
                CM.vpartition(fcontent,
                              lambda l: l.lower().startswith(k.lower()))
            xinfoVs = xinfoVs + [v]

        try:
            xinfoVs = [[xi_.split(':')[1].strip() for xi_ in xi]
                       for xi in xinfoVs]
        except IndexError:
            msg = 'incorrect xinfo format (missing ":" somewhere ?)'
            msg = msg + '\n' + \
                '\n'.join([g for g in flatten(xinfoVs) if ':' not in g])
            raise AssertionError(msg)

        xinfoVs = [map(ReadFile.replace_var_name,xi) for xi in xinfoVs]
        xinfo = dict([(k,v) for k,v in zip(xinfoKs,xinfoVs)])

        xinfo['All'] = map(str,vs)
        xinfo['Assume'] = [eval(assume) for assume in xinfo['Assume']]

        return xinfo



class Miscs(object):

    sage_expr = sage.symbolic.expression.Expression
    sage_real = sage.rings.real_mpfr.RealLiteral
    sage_int = sage.rings.integer.Integer

    @staticmethod
    def sage_save(obj, filename, src=None):
        """
        sage: Miscs.sage_save(x,'/tmp/ts','x')
        save 'x' to '/tmp/ts'
        """
        if verbose >= 1:
            print("save '{s}' to '{fn}'".format(
                    s = '' if src is None else src,
                    fn=filename))
        save(obj,filename)

    @staticmethod
    def sage_load(filename, src=None):
        """
        sage: Miscs.sage_save(x,'/tmp/ts','x')
        save 'x' to '/tmp/ts'
        sage: t = Miscs.sage_load('/tmp/ts','x')
        load 'x' from '/tmp/ts'
        """

        if verbose >= 1:
            print("load '{s}' from '{fn}'".format(
                    s = '' if src is None else src,
                    fn = filename))
        return load(filename)


    @staticmethod
    def get_sample(tcs, tcsN, sampleP, min_, preserveTcs=False):

        sampleN = int(round(tcsN * sampleP / 100.00))
        if min_ is not None and sampleN < min_:
            sampleN = min_

        rs = Miscs.sample_traces(tcs,sampleN,preserveTcs)

        return rs


    @staticmethod
    def sample_traces(tcs, sampleN, preserveTcs=False,
                      no_tcs2=False):
        """
        preserveTcs: don't modify the input/orig tcs

        Note: much faster than using
        tcs1 = sample(tcs,sampleN)
        tcs2 = [x for x in tcs if x not in tcs1] #very slow


        EXAMPLES:

        sage: set_random_seed(0)
        sage: l=srange(10); l1,l2= Miscs.sample_traces(l,13); l1,l2,l
        sample_traces: chose |tcs1|=10, |tcs2|=0 (attempted 13/10 tcs)
        ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

        sage: set_random_seed(0)
        sage: l=srange(10); l1,l2= Miscs.sample_traces(l,3); l1,l2,l
        sample_traces: chose |tcs1|=3, |tcs2|=7 (attempted 3/10 tcs)
        ([5, 9, 8], [6, 7, 3, 2, 0, 4, 1], [5, 9, 8, 6, 7, 3, 2, 0, 4, 1])

        sage: set_random_seed(0)
        sage: l=srange(10); l1,l2= Miscs.sample_traces(l,3,preserveTcs=True); l1,l2,l
        sample_traces: chose |tcs1|=3, |tcs2|=7 (attempted 3/10 tcs)
        ([5, 9, 8], [6, 7, 3, 2, 0, 4, 1], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

        sage: set_random_seed(0)
        sage: l=srange(10); l1,l2= Miscs.sample_traces(l,3,preserveTcs=True,no_tcs2=True); l1,l2,l
        sample_traces: chose |tcs1|=3, |tcs2|=0 (attempted 3/10 tcs)
        ([5, 9, 8], [], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9])

        sage: l=srange(3); l1,l2= Miscs.sample_traces(l,0,preserveTcs=True)
        sample_traces: chose |tcs1|=0, |tcs2|=3 (attempted 0/3 tcs)

        sage: l=srange(3); l1,l2= Miscs.sample_traces(l,4,preserveTcs=True)
        sample_traces: chose |tcs1|=3, |tcs2|=0 (attempted 4/3 tcs)

        """


        if sampleN >= len(tcs):
            tcs1 = tcs[:]
            tcs2 = []
        else:
            tcs_ = list(tcs) if preserveTcs else tcs
            shuffle(tcs_)
            tcs1 = tcs_[:sampleN]
            tcs2 = [] if no_tcs2 else tcs_[sampleN:]

            tcs2_min_siz = 1000
            if len(tcs2) >= tcs2_min_siz:
                logger.debug('set tcs2 to %d'%tcs2_min_siz)
                tcs2=tcs2[:tcs2_min_siz]

        logger.debug('sample_traces: chose |tcs1|=%s, |tcs2|=%s (attempted %d/%s tcs)'
                     %(len(tcs1), len(tcs2),sampleN,len(tcs)))

        return tcs1, tcs2



    @staticmethod
    def keys_to_str(ls):
        """
        Convert key in dictionary to str, {a:5} => {'a' => 5}

        Input: list of dicts (could be some non-dict elem)
        Output: list of dicts with keys as string

        EXAMPLES:

        sage: Miscs.keys_to_str([{var('a'):5},{var('b'):7},5])
        [{'a': 5}, {'b': 7}, 5]
        """
        return [(dict([(str(k),c) for k,c in l.items()])) \
                    if isinstance(l,dict) else l
                for l in ls]


    @staticmethod
    def get_vars(ps):
        """
        Returns a list of uniq variables from a list of properties

        EXAMPLES:

        sage: var('a b c x')
        (a, b, c, x)
        sage: Miscs.get_vars([x^(a*b) + a**2+b+2==0, c**2-b==100, b**2 + c**2 + a**3>= 1])
        [a, b, c, x]

        sage: Miscs.get_vars(a**2+b+5*c+2==0)
        [a, b, c]

        sage: Miscs.get_vars(x+x^2)
        [x]

        sage: Miscs.get_vars([3])
        []

        sage: Miscs.get_vars([3,'x + c',x+b])
        [b, x]

        """

        ps = ps if isinstance(ps,list) else [ps]
        vs = flatten([p.variables() for p in ps
                      if isinstance(p, Miscs.sage_expr)])

        if __debug__:
            assert all(v.is_symbol() for v in vs)

        return sorted(set(vs),key=str)

    @staticmethod
    def get_coefs_terms(p):
        """
        Returns the Coefs and Terms of a given expression

        EXAMPLES:

        sage: var('a b c')
        (a, b, c)

        sage: Miscs.get_coefs_terms(a**2+b+5*c+2==0)
        ([1, 1, 5, 2], [a^2, b, c, 1])

        sage: Miscs.get_coefs_terms(10/3*a**2+3*b+5*c+2)
        ([10/3, 3, 5, 2], [a^2, b, c, 1])
        """

        if __debug__:
            assert isinstance(p,Miscs.sage_expr)

        vs = Miscs.get_vars(p)
        Q = PolynomialRing(QQ,vs, None if len(vs) > 1 else 1)

        cs = Q(p).coefficients()
        ts = map(SR,Q(p).monomials())

        if __debug__:
            assert all(isinstance(t,Miscs.sage_expr) for t in ts)


        return cs, ts

    @staticmethod
    def gen_terms(deg, vs):
        """
        Generates a list of terms from the given list of vars and deg
        the number of terms should be len(rs) == binomial(len(vs)+d, d)

        EXAMPLES:

        sage: Miscs.gen_terms(3,list(var('a b')))
        * gen_terms(deg=3,vs=[a, b])
        Generate 10 terms
        terms: [1, a, b, a^2, a*b, b^2, a^3, a^2*b, a*b^2, b^3]
        [1, a, b, a^2, a*b, b^2, a^3, a^2*b, a*b^2, b^3]

        sage: Miscs.gen_terms(3,list(var('a b c d e f')))
        * gen_terms(deg=3,vs=[a, b, c, d, e, f])
        Generate 84 terms
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

        logger.info('* gen_terms(deg=%d,vs=%s)' %(deg,vs))

        #since we also want constant term 1
        mc = MultichooseNK(len(vs)+1,deg)
        vs_ = [SR(1)] + vs
        ts = [prod(vs_[i] for i in m) for m in mc]


        logger.info('Generate %d terms' %len(ts))
        logger.debug('terms: {}'.format(map(str,ts)))

        if __debug__:
            assert len(ts) == binomial(len(vs)+ deg, deg)

        return ts



    @staticmethod
    def get_sols(sols, sol_format):
        """
        Construct a list of properties from the inputs sols and sol_format


        EXAMPLES:

        #when sols are in dict form
        sage: var('uk_0,uk_1,uk_2,uk_3,uk_4,r14,r15,a,b,y')
        (uk_0, uk_1, uk_2, uk_3, uk_4, r14, r15, a, b, y)

        sage: Miscs.get_sols([{uk_0: -2*r14 + 7/3*r15, uk_1: -1/3*r15, \
        uk_4: r14, uk_2: r15, uk_3: -2*r14}],\
        uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]

        #when sols are not in dict form
        sage: Miscs.get_sols([[uk_0== -2*r14 + 7/3*r15, \
        uk_1== -1/3*r15, uk_4== r14, uk_2== r15, uk_3== -2*r14]],\
        uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0)
        [-2*x + y - 2 == 0, -1/3*a + b + 7/3 == 0]

        sage: Miscs.get_sols([],uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0)
        []
        """

        if CM.is_none_or_empty(sols):
            return []

        if len(sols) > 1:
            print 'W: get_sols: len(sols) = %d' %len(sols)
            print sols

        def f_eq(d):
            if isinstance(d,list):
                f_ = sol_format
                for d_ in d:
                    f_ = f_.subs(d_)
                rhsVals = CM.vset([d_.rhs() for d_ in d])
                uk_vars = Miscs.get_vars(rhsVals)
            else:
                f_ = sol_format(d)
                uk_vars = Miscs.get_vars(d.values()) #e.g., r15,r16 ...

            if CM.is_none_or_empty(uk_vars):
                return f_

            iM = identity_matrix(len(uk_vars)) #standard basis
            rs = [dict(zip(uk_vars,l)) for l in iM.rows()]
            rs = [f_(r) for r in rs]
            return rs

        sols = flatten([f_eq(s) for s in sols])

        #remove trivial (tautology) str(x) <=> str(x)
        sols = [s for s in sols
                if not (s.is_relational() and str(s.lhs()) == str(s.rhs()))]

        return sols


    @staticmethod
    def gen_template(ts, rv, op=operator.eq, prefix=None,
                     ret_coef_vs=False):

        """
        Generates template from terms.

        EXAMPLES:

        sage: var('a,b,x,y')
        (a, b, x, y)

        sage: Miscs.gen_template(ts=[1, a, b, x, y],rv=0,prefix=None)
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0 == 0

        sage: Miscs.gen_template(ts=[1, x, y],rv=0,\
        op=operator.gt,prefix=None,ret_coef_vs=True)
        (uk_1*x + uk_2*y + uk_0 > 0, [uk_0, uk_1, uk_2])

        sage: Miscs.gen_template(ts=[1, a, b, x, y],rv=None,prefix=None)
        a*uk_1 + b*uk_2 + uk_3*x + uk_4*y + uk_0

        sage: Miscs.gen_template(ts=[1, a, b, x, y],rv=0,prefix='hi')
        a*hi1 + b*hi2 + hi3*x + hi4*y + hi0 == 0

        sage: var('x1')
        x1
        sage: Miscs.gen_template(ts=[1, a, b, x1, y],rv=0,prefix='x')
        Traceback (most recent call last):
        ...
        AssertionError: name conflict in gen_template

        """

        if prefix is None:
            prefix = 'uk_'

        prefix = prefix + "%d"

        coefVars = [var(prefix%i) for i in srange(len(ts))]

        assert len(set(ts) & set(coefVars))==0,\
            'name conflict in gen_template'

        template = sum(map(prod,zip(coefVars,ts)))

        if rv is not None:
            template = op(template,rv) #eqt

        if ret_coef_vs:
            return template, coefVars
        else:
            return template


    @staticmethod
    def instantiate_template(template,tcs):
        """
        Instantiates a (potentially nonlinear) relation with traces to obtain
        a set of linear relations.

        EXAMPLES:

        sage: var('a,b,x,y,uk_0,uk_1,uk_2,uk_3,uk_4')
        (a, b, x, y, uk_0, uk_1, uk_2, uk_3, uk_4)

        sage: Miscs.instantiate_template(uk_1*a + uk_2*b + uk_3*x + uk_4*y + uk_0 == 0, \
        [{y: 4, b: 2, a: 13, x: 1}, {y: 6, b: 1, a: 10, x: 2}, {y: 8, b: 0, a: 7, x: 3}, \
        {y: 10, b: 4, a: 19, x: 4}, {y: 22, b: 30, a: 97, x: 10}, \
        {y: 28, b: 41, a: 130, x: 13}])
        Create equations from 6 data
        [uk_0 + 13*uk_1 + 2*uk_2 + uk_3 + 4*uk_4 == 0,
        uk_0 + 10*uk_1 + uk_2 + 2*uk_3 + 6*uk_4 == 0,
        uk_0 + 7*uk_1 + 3*uk_3 + 8*uk_4 == 0,
        uk_0 + 19*uk_1 + 4*uk_2 + 4*uk_3 + 10*uk_4 == 0,
        uk_0 + 97*uk_1 + 30*uk_2 + 10*uk_3 + 22*uk_4 == 0,
        uk_0 + 130*uk_1 + 41*uk_2 + 13*uk_3 + 28*uk_4 == 0]

        """

        logger.info('Create equations from %d data' %len(tcs))

        eqts = [template.subs(tc) for tc in tcs]
        eqts = CM.vset(eqts) #sys of lin eqts
        return eqts





    @staticmethod
    def solve_eqts(ts,rv,ds):
        """
        shortcut of some functions often called together

        EXAMPLES:
        sage: var('x y')
        (x, y)
        sage: ts = [1, x, y, x^2, x*y, y^2]
        sage: rv = 0
        sage: ds = [{y: 1, x: 1}, {y: 2, x: 4}, {y: 4, x: 16}, {y: 0, x: 0}, {y: 8, x: 64}, {y: 9, x: 81}, {y: -1, x: 1}, {y: 5, x: 25}]

        sage: Miscs.solve_eqts(ts,rv,ds)
        Create equations from 8 data
        * EQ: Solve 8 (uniq) eqts for 6 unknowns coeffs
        [y^2 - x == 0]
        """

        def _solve(eqts):
            vs = Miscs.get_vars(eqts)

            assert len(eqts) >= len(vs),\
                "eqts %d <= unknown coefs %d" %(len(eqts),len(vs))

            logger.debug('* EQ: Solve %d (uniq) eqts for %d unknowns coeffs'
                        %(len(eqts), len(vs)))

            rs = solve(eqts,*vs,solution_dict=True)
            return rs


        template = Miscs.gen_template(ts=ts,rv=rv)
        eqts     = Miscs.instantiate_template(template,tcs=ds)
        rs       = _solve(eqts)
        rs       = Miscs.get_sols(rs,template)

        return rs


    @staticmethod
    def solve_eqts_(ts,rv,ds):
        rs = Miscs.solve_eqts(ts,rv,ds)
        if CM.is_none_or_empty(rs):
            return []
        else:
            return {rs[0].rhs():rs[0].lhs()}




    @staticmethod
    def elim_denom(p):
        """
        Eliminates (Integer) denominators in expression operands.
        Will not eliminate if denominators is a var (e.g.,  (3*x)/(y+2)).

        EXAMPLES:

        sage: var('x y z')
        (x y, z)

        sage: Miscs.elim_denom(3/4*x^2 + 7/5*y^3)
        15*x^2 + 28*y^3

        sage: Miscs.elim_denom(-3/2*x^2 - 1/24*z^2 >= (y + 1/7))
        -252*x^2 - 7*z^2 >= 168*y + 24

        sage: Miscs.elim_denom(-3/(y+2)*x^2 - 1/24*z^2 >= (y + 1/7))
        -1/24*z^2 - 3*x^2/(y + 2) >= y + 1/7

        sage: Miscs.elim_denom(x + y == 0)
        x + y == 0

        """
        try:
            f = lambda g : [Integer(o.denominator()) for o in g.operands()]
            denoms = f(p.lhs()) + f(p.rhs()) if p.is_relational() else f(p)
            return p * lcm(denoms)
        except TypeError:
            return p

    @staticmethod
    def senumerate(ls):
        return((ZZ(i),x) for i,x in enumerate(ls))


    #############################
    @staticmethod
    def _f(ls,op,is_real):
        """

        """

        if CM.vany(ls,lambda l: l is None) or ls == []:
            return None

        import z3
        from smt_z3py import SMT_Z3

        rs = [SMT_Z3.to_z3exp(l,is_real=is_real) \
                  if isinstance(l,Miscs.sage_expr) \
                  else l
              for l in ls]

        if len(rs) == 1:
            rs = rs[0]
        else:
            rs = z3.And(rs) if op == 'and' else z3.Or(rs)

        return rs

    @staticmethod
    def tmap(f,A):
        """
        EXAMPLES

        sage: Miscs.tmap(str,[1,2,[[3],5,[]],[6]])
        ['1', '2', [['3'], '5', []], ['6']]
        """
        if CM.is_iterable(A):
            return [Miscs.tmap(f,a) for a in A]
        else:
            return f(A)

    @staticmethod
    def travel(A):
        """
        EXAMPLES:

        sage: Miscs.travel([1,[0,[5]],8,[8]])
        [([0], 1), ([1, 0], 0), ([1, 1, 0], 5), ([2], 8), ([3, 0], 8)]
        """

        if CM.is_none_or_empty(A):
            return []

        #if A is already the traveled info
        if isinstance(A[0],tuple):
            return A

        else:  #otherwise get the traveled info
            def _travel(A,idx,rs):
                for i,c in Miscs.senumerate(A):
                    if CM.is_iterable(c): #hasattr(c,"__iter__"):
                        rs = _travel(c,idx+[i],rs)
                    else:
                        rs = rs + [(idx+[i],c)]
                return rs

            results = _travel(A,[],[])
            return results

    @staticmethod
    def getListIdxs(A):
        """
        Return the (nested) order of A in dict format where dkey is value v
        of A and the dvalue is the list of indices I of A containing v

        EXAMPLES:

        sage: Miscs.getListIdxs([1,[0,[5]],8,[8]])
        {0: [(1, 0)], 1: [(0,)], 5: [(1, 1, 0)], 8: [(2,), (3, 0)]}

        sage: Miscs.getListIdxs([])
        {}
        """

        idxs_vals = Miscs.travel(A)
        vals_idxs = [(v,tuple(idx)) for idx,v in idxs_vals]
        return CM.create_dict(vals_idxs)

    @staticmethod
    def getVals(A):
        return [v for _,v in Miscs.travel(A)]

    @staticmethod
    def getIdxs(A):
        return [v for v,_ in Miscs.travel(A)]

    @staticmethod
    def getValFromIdx(A,idx):
        """
        EXAMPLES:

        sage: Miscs.getValFromIdx([1,[0,[5]],8,[8]],[3,0])
        8
        """
        #R_ = A[idx[0]] if hasattr(idx,"__iter__") else A[idx]
        R_ = A[idx[0]] if CM.is_iterable(idx) else A[idx]
        if not isinstance(idx,list) or len(idx)==1:
            return R_
        else:
            return Miscs.getValFromIdx(R_,idx[1:])


    @staticmethod
    def getIdxFromVal(A,v,idfun=lambda x:x):
        """
        EXAMPLES:

        sage: Miscs.getIdxFromVal([1,[0,[5]],8,[8]],'8',idfun=str)
        [[2], [3, 0]]
        sage: Miscs.getIdxFromVal(Miscs.travel([1,[0,[5]],8,[8]]),'8',idfun=str)
        [[2], [3, 0]]
        """
        return [idx for idx,c in Miscs.travel(A) if idfun(c)==v]


    @staticmethod
    def reach(vss, rdata):
        """
        Checks if values in vss can be found from rdata and performs
        branching if necessary in the case of multiple occurences.

        The output is a list of size == dim of rdata.

        EXAMPLES:

        sage: Miscs.reach([(8,), (15,), (7,)], \
        rdata = {8:[(10,), (4,)], 15:[(8,), (3,)], 7:[(2,)]})
        [[(10, 4), (8, 3), (2,)]]

        #10 is found at either (3,) or (8,), written as (3,8)
        #The output is a list of size 1 since the dim of rdata is 1
        sage: Miscs.reach([(10,)], rdata = {10:[(3,), (8,)]})
        [[(3, 8)]]

        #10 is found at either (3,7) or (8,2), written as [(3,8)],[(7,2)]
        sage: Miscs.reach([(10,)], rdata = {10:[(3,7),(8,2)]})
        [[(3, 8)], [(7, 2)]]

        #10 or 4 is found at either (3,7),(8,2) or (0,4), written as [(3,8,0)],[(7,2,4)]
        sage: Miscs.reach([(10,4)], \
        rdata = {4:[(0,4)], 10:[(3,7),(8,2)]})
        [[(3, 8, 0)], [(7, 2, 4)]]

        #10 or 4 is found at either (3,7),(8,2) or (0,4), written as [(3,8,0)],[(7,2,4)]
        #8 or 3 is found at either (2,6) or (1,2), written as [(2,1)],[(6,2)]
        #2 is found at either (2,0) or (1,7),  written as [(2,1)],[(0,7)]
        #all together, written as [[(3,8,0),(2,1),(2,1)], [(7,2,4),(6,2),(0,7)]]
        #The output is 2 lists. Each list has 3 (# of inputs) tuples.

        sage: Miscs.reach([(10,4),(8,3),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2, 1), (2, 1)], [(7, 2, 4), (6, 2), (0, 7)]]

        sage: Miscs.reach([(10,4),(8,3),(8,3)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2, 1), (2, 1)], [(7, 2, 4), (6, 2), (6, 2)]]

        sage: Miscs.reach([(10,5),(8,3),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8), (2, 1), (2, 1)], [(7, 2), (6, 2), (0, 7)]]

        sage: Miscs.reach([(10,4),(8,13),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(3, 8, 0), (2,), (2, 1)], [(7, 2, 4), (6,), (0, 7)]]

        sage: Miscs.reach([(100,14),(8,13),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})

        sage: Miscs.reach([(100,4),(8,13),(2,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})
        [[(0,), (2,), (2, 1)], [(4,), (6,), (0, 7)]]

        sage: Miscs.reach([(100,4),(8,13),(100,)], \
        rdata = {4:[(0,4)], 8:[(2,6)], 10:[(3,7),(8,2)], 3:[(1,2)], 2:[(2,0),(1,7)]})

        """
        if __debug__:
            assert isinstance(vss,list)
            assert all(isinstance(vs,tuple) for vs in vss)


        _getIdxs = lambda vs: [rdata[v] for v in vs if v in rdata]
        rs = [_getIdxs(vs) for vs in vss]

        if CM.vany(rs, lambda r_: len(r_) == 0):
            return
        else:
            rs = [flatten(r_,list) for r_ in rs]
            rs = [zip(*r_) for r_ in rs]
            rs = zip(*rs)
            rs = [list(r_) for r_ in rs]
            assert len(rs) == len(rdata[rdata.keys()[0]][0])
            return rs






class Tree(object):

    def __init__(self, args):
        """
        Tree is a leaf (None or Expression)  or a dict {'root':, 'children':[..]}

        sage: Tree({'root':None,'children':[None,None]})
        Traceback (most recent call last):
        ...
        AssertionError: args['roots'] cannot be None

        sage: var('y')
        y
        sage: print Tree({'root':'B', 'children':[{'root':'C','children':[x + 2*y]}]})
        B[C[x + 2*y]]

        """

        if isinstance(args, dict) and 'coef' not in args and 'first_idx' not in args:

            assert 'root' in args and 'children' in args, 'improper tree format: %s'%map(str,args)
            assert args.get('root') is not None, "args['roots'] cannot be None"
            assert isinstance(args.get('children'), list)
            assert len(args.get('children')) > 0

            self.root = args.get('root')
            self.children = [c if isinstance(c,Tree) else Tree(c)
                             for c in args.get('children')]


            if 'commute' not in args or self.get_nchildren() == 1:
                self.commute = False
            else:
                self.commute = args.get('commute')

        else:  #leaf
            self.root = args
            self.children = None
            self.commute = False
            self.data = {}

    def __eq__(self,other):
        """
        sage: var('y')
        y
        sage: Tree(x+y+7) == Tree(7+x+y)
        True
        sage: Tree({'root':x+y+7,'children':[None]}) == Tree({'root':x+y+7,'children':[None,None]})
        False
        sage: Tree({'root':x+y+7,'children':[None]}) == Tree({'root':x+y+7,'children':[None]})
        True
        """
        return type(other) is type(self) and self.__dict__ == other.__dict__

    def __ne__(self,other):
        """
        sage: var('y')
        y
        sage: Tree(x+y+7) != Tree(7+x+y)
        False
        sage: Tree(x+y+7) != Tree(x+y)
        True
        """
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.__str__())

    def __str__(self, leaf_content=None):
        """
        EXAMPLES:
        sage: print Tree(None)
        None

        sage: print Tree({'root':'a','children':[None,None]})
        a[None][None]

        sage: print Tree({'root':'a','children':[None,{'root':'b','children':[None]}]})
        a[None][b[None]]

        sage: print Tree({'root':'xor','children':[None, \
        {'root':'b','children':[None]}, {'root':x,'children':[None]}]})
        xor(None,b[None],x[None])

        sage: print Tree(x^2 + 7)
        x^2 + 7

        sage: print Tree(x).__str__(leaf_content='hi')
        hi

        sage: var('y')
        y
        sage: print Tree(x).__str__(leaf_content={x:y+7})
        y + 7


        sage: print Tree({'root':'x','children':[None]})
        x[None]
        sage: print Tree({'root':x,'children':[None]})
        x[None]
        """
        try:
            children = [c.__str__(leaf_content=leaf_content) for c in self.get_children()]

            if self.get_root() in ExtFun.efdict:
                rs = '(%s)'%(','.join(children))
            else:
                rs = ''.join(['[%s]'%c for c in children])

            rs = str(self.get_root()) + rs
            return rs

        except Exception:
            if leaf_content is None:
                return str(self.get_root())
            else:
                if isinstance(leaf_content, dict):
                    if isinstance(self.get_root(), Expression):
                        return str(self.get_root()(leaf_content))
                    else:
                        str(self.get_root())
                else:
                    return str(leaf_content)


    def get_root(self):
        return self.root

    def get_nchildren(self):
        return len(self.children)

    def get_children(self):
        return self.children

    def is_commute(self):
        return self.commute

    @staticmethod
    def leaf_tree():
        return Tree(None)

    def is_node(self):
        """
        sage: Tree({'root':'a','children':[None,None]}).is_node()
        True
        """
        return all(c.is_leaf() for c in self.get_children())


    def is_leaf(self):
        """
        sage: Tree({'root':'a','children':[None,None]}).is_leaf()
        False
        """
        return self.get_children() is None

    ###



    def get_non_leaf_nodes(self, nl_nodes=[]):
        """
        Returns the *names* of the non-leaves nodes

        sage: print Tree({'root':'a','children':[None,None]}).get_non_leaf_nodes()
        ['a']

        sage: Tree({'root':'a','children':[None, \
        {'root':'b','children':[None,None]}, \
        {'root':'c','children':[None]}, \
        {'root':'d','children':[None,None]}]}).get_non_leaf_nodes()
        ['a', 'b', 'c', 'd']
        """
        if self.is_leaf():
            return nl_nodes
        else:
            nl_nodes_ = [c.get_non_leaf_nodes(nl_nodes)
                         for c in self.get_children()]
            nl_nodes = [self.get_root()] + flatten(nl_nodes_)
            return nl_nodes


    def get_leaves(self):
        """
        TOCHECK

        EXAMPLES:

        sage: Tree.leaf_tree().get_leaves()
        [(None, None, [])]

        sage: rs = Tree({'root':'A','children': [ \
        {'root':'C','children':[None,None]}, \
        {'root':'D','children':[None]}]}).get_leaves()

        sage: [(str(p),idx,tid) for p,idx,tid in rs]
        [('C[None][None]', 0, ['A', 0, 'C', 0]),
        ('C[None][None]', 1, ['A', 0, 'C', 1]),
        ('D[None]', 0, ['A', 1, 'D', 0])]
        """

        def _get_leaves(t,p,idx,tid):

            assert isinstance(t,Tree)

            if t.is_leaf():  #leaf
                return [(p,idx,tid)]
            else:
                results = [_get_leaves(child, t, idx_, tid + [t.get_root(), idx_])
                           for idx_, child in Miscs.senumerate(t.get_children())]

                results = flatten(results,list)
                return results


        return _get_leaves(self,p=None,idx=None,tid=[])




    def gen_root_trees(self, nodes, vss, blacklist, data):
        """
        Generates trees from nodes whose root is self.root

        blacklist {a: L} disallows a[b[..]] and a[[c..]]
        where {b,c} in L and only allows
        [a[x[..]]] where x is not in L

        so for example if we want to force a to be a Leaf then {a:L}
        where L is all variables (except None).
        This allows the removal of an extra whitelist

        also if we have {a: L} where L is all variablles (except a) then basically
        we disallow the tree with root 'a' since this says 'a' cannot have
        any children (including) leaf.


        EXAMPLES

        sage: t = Tree({'root':'a','children':[None,None]})
        sage: nodes = [Tree({'root':'b','children':[None,None]})]
        sage: map(str,t.gen_root_trees(nodes, vss=None, blacklist = {}, data={}))
        ['a[b[None][None]][b[None][None]]',
        'a[b[None][None]][None]',
        'a[None][b[None][None]]',
        'a[None][None]']

        sage: t = Tree({'root':'B','children':[None]})

        sage: nodes = [ \
        Tree({'root':'C','children':[None,None]}), \
        Tree({'root':'D','children':[None]})]

        sage: vss=[(8,),(15,),(7,)]
        sage: data = {'C':{8: [(2, 6)], 10: [(3, 7), (8, 2)], 3: [(1, 2)], 4: [(0, 4)], 2: [(2, 0), (1, 7)]},\
        'D':{8: [(7,)], 1: [(9,)], 2: [(8,)], 3: [(5,)]}, 'B':{8: [(10,), (4,)], 7: [(2,)], 15: [(8,), (3,)]}}

        sage: map(str,t.gen_root_trees(nodes,vss=vss, blacklist={}, data=data))
        ['B[C[D[None]][None]]', 'B[C[None][None]]', 'B[None]']

        """
        if __debug__:
            assert isinstance(nodes,list) and \
                all(isinstance(x,Tree) and x.is_node() for x in nodes)

            assert vss is None or \
                (isinstance(vss,list) and all(isinstance(v,tuple) for v in vss))

            assert isinstance(blacklist, dict)


        if vss is not None:
            children_vss = Miscs.reach(vss, data[self.get_root()])
            if children_vss is None:
                return []
        else:
            children_vss = [None] * self.get_nchildren()

        if nodes:

            children = nodes + [Tree.leaf_tree()]

            children = [c for c in children \
                            if self.get_root() not in blacklist or \
                            c.get_root() not in blacklist[self.get_root()]]


            #recursive call
            def _gt(r_, nodes_, vss_):
                if r_.is_leaf():
                    return [r_]
                else:
                    return r_.gen_root_trees(nodes=nodes_,vss=vss_,
                                             blacklist=blacklist,
                                             data=data)


            children = [[_gt(c, CM.vsetdiff(nodes,[c]), vs) for c in children]
                        for vs in children_vss]


            children = [flatten(c) for c in children]

            assert len(children) == self.get_nchildren()

            combs = CartesianProduct(*children)

            if self.is_commute():
                """
                (T1, T2, T3) is equiv to (T1, T3, T2)
                """
                combs = CM.vset(combs,idfun=Set)


            rs = [Tree({'root':self.get_root(),
                        'children': c,
                        'commute': self.is_commute()})
                         for c in combs]

        else:
            rs = [Tree({'root':self.get_root(),
                        'children':[Tree.leaf_tree()] * self.get_nchildren(),
                        'commute': self.is_commute()})]


        return rs


    def gen_formula(self, v, data):
        """
        Generate a formula recursively to represent the data structure of tree based on
        input value v and data.


        sage: var('_B_0_C_0__i0 _B_0_C_0__i1')
        (_B_0_C_0__i0, _B_0_C_0__i1)


        sage: Tree({'root':'B','children':[\
        {'root':'C', 'children':[_B_0_C_0__i0 + 2*_B_0_C_0__i1]}]}).gen_formula(v=81,\
        data = {'C':{0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},\
        'B':{81: [(17,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 7


        sage: Tree({'root':'B','children':[\
        {'root':'C', 'children':[_B_0_C_0__i0 + 2*_B_0_C_0__i1]}]}).gen_formula(v=81, \
        data = {'C':{0: [(0,), (3,)], 1: [(4,)], 7: [(2,), (5,)], 8: [(6,)], 9: [(1,), (8,)], 17: [(7,)]},\
        'B':{81: [(17,), (9,)], 74: [(6,), (8,)], 71: [(5,), (7,)]}})
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 7,
        Or(_B_0_C_0__i0 + _B_0_C_0__i1*2 == 1,
        _B_0_C_0__i0 + _B_0_C_0__i1*2 == 8))


        sage: Tree({'root':'add','children':[\
        {'root':'C', 'children':[{'root':'_add_0_C_','children':[100,200]}]},\
        {'root':'D', 'children':[{'root':'_add_1_D_','children':[100,200]}]}]}).gen_formula(v=17, \
        data = {'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},\
        'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},\
        'add':{17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)]}})


        """

        if isinstance(self.get_root(), Expression):
            return self.get_root() == v

        elif isinstance(self.get_root(), dict) and 'first_idx' in self.get_root():
            #special case {'first_idx':i,'coef':z}
            if v == 0:
                t0 = self.get_root()['coef'] == 0
                t1 = self.get_root()['first_idx'] == 1
                return Miscs._f([t0,t1],'and',is_real=False)
            else:
                return self.get_root()['coef'] == v
        else:
            try:
                idxs = data[self.get_root()][v]
            except KeyError: #not reachable, no rel
                return None


            orRs = []
            for idx in idxs:
                andRs = []
                for v_,a_ in zip(idx,self.get_children()):
                    p_ = a_.gen_formula(v_,data)

                    if p_ is None:
                        andRs = None
                        break
                    andRs.append(p_)


                if andRs is not None:
                    assert len(andRs)>0
                    andRs = Miscs._f(andRs,'and',is_real=False)
                    orRs.append(andRs)

            orRs = Miscs._f(orRs,'or',is_real=False)
            return orRs

    ##### Static methods for Tree #####

    @staticmethod
    def gen_trees(nodes, vss, blacklist, data):
        """
        Generates nestings from a set of nodes. E.g., given nodes [a,b,c],
        returns all nestings, e.g. [{a,[b,c],{a,[c,b]}},{b,[a,c]} ..

        EXAMPLES:

        sage: nodes = [\
        Tree({'root':'A','children':[None]}), \
        Tree({'root':'B','children':[None,None]}), \
        Tree({'root':'C','children':[None,None,None]})]
        sage: len(Tree.gen_trees(nodes=nodes,vss=None,blacklist={},data={}))
        477

        """
        if __debug__:
            assert isinstance(nodes,list) and \
                all(isinstance(x,Tree) and x.is_node() for x in nodes)

            assert vss is None or \
                (isinstance(vss,list) and all(isinstance(v,tuple) for v in vss))

            assert isinstance(blacklist, dict)



        def _gt(t):
            ts = t.gen_root_trees(nodes     = CM.vsetdiff(nodes,[t]),
                                  vss       = vss,
                                  blacklist = blacklist,
                                  data      = data)
            return ts


        trees = [ _gt(node) for node in nodes]
        trees = flatten(trees)

        if __debug__:
            assert all(isinstance(t,Tree) for t in trees)


        return trees


class AEXP(object):

    def __init__(self,lt,rt):
        """
        Initialize AEXP (Array Expression) which has the form left_tree = right_tree,
        e.g.  A[None][None] = B[C[None][None]][D[None]]

        EXAMPLES:
        _ = AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})

        sage: _ = AEXP(Tree({'root':'v','children':[None]}), \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})

        sage: _ = AEXP({'root':'v','children':[{'root':'a','children':[None]}]}, \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]})
        Traceback (most recent call last):
        ...
        AssertionError: left tree has to be a node tree

        """


        if not isinstance(lt,Tree):
            lt = Tree(lt)
        if not isinstance(rt,Tree):
            rt = Tree(rt)

        assert lt.is_node(), 'left tree has to be a node tree'

        self.lt = lt
        self.rt = rt

    def __str__(self,leaf_content=None,do_lambda_format=False):
        """
        Returns the str of AEXP

        leaf_content: {},None,str
        Instantiates leaves of rt with leaf_content, e.g. A[x], leaf_info={x:5} => A[5]

        do_lambda_format: T/F
        Returns a lambda format of array expressions for evaluation

        EXAMPLES:

        sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3','children':[None,None,None]}]}).__str__()
        'v[i1] == a[x3[(i1)_][(i1)_][(i1)_]]'

        sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3',\
        'children':[None,None,None]}]}).__str__(do_lambda_format=True)
        'lambda v,a,x3,i1: v[i1] == a[x3[(i1)_][(i1)_][(i1)_]]'

        sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3',\
        'children':[None,None,x+7]}]}).__str__(leaf_content={x:5},do_lambda_format=True)
        'lambda v,a,x3,i1: v[i1] == a[x3[None][None][12]]'

        sage: var('y')
        y

        sage: AEXP({'root':'v','children':[None]}, \
        {'root':'a','children':[{'root':'x3',\
        'children':[None,{'root':'c',\
        'children':[x-y,None]}, x+7]}]}).__str__(leaf_content={x:5,y:7},\
        do_lambda_format=False)
        'v[i1] == a[x3[None][c[-2][None]][12]]'

        """

        def get_idx_strs(lt):
            """
            EXAMPLES
            #sage: Tree({'root':'xor','children':[None,None,None]}).get_str_formats()
            ([1, 2, 3], '[i1][i2][i3]', 'i1,i2,i3')
            """

            idxs = [(i+1) for i in srange(lt.get_nchildren())]
            iformat = ''.join(['[i%s]'%li for li in idxs]) #[i][j]
            aformat = ','.join(['i%s'%li for li in idxs])  #i,j
            return idxs, iformat, aformat

        l_idxs, l_iformat, l_aformat = get_idx_strs(self.lt)

        if leaf_content is None:
            r_idxs = "(%s)_"%l_aformat
            rt = self.rt.__str__(leaf_content=r_idxs)
        else:
            assert isinstance(leaf_content,dict)
            rt = self.rt.__str__(leaf_content=leaf_content)


        rs = '%s%s == %s'%(self.lt.root,l_iformat,rt)

        if do_lambda_format:
            l_idxs_ = ','.join(['i%s'%li for li in l_idxs])
            nodes = [self.lt.get_root()]  + CM.vset(self.rt.get_non_leaf_nodes())
            lambda_ = 'lambda %s,%s' %(','.join(nodes),l_aformat)
            rs= '%s: %s'%(lambda_,rs)

        return rs


    def is_ok(self, xinfo):
        """
        Return True if this aexp is fine. Otherwise, returns False, which marks
        it for pruning.

        e.g., Those that do not contain the input variables
        """

        #all inputs must be in rt
        roots = self.rt.get_non_leaf_nodes()
        rs = all(iv in roots for iv in xinfo['Input'])
        return rs


    def gen_smt_formula(self, data):
        """
        todo: combine both gen_template & gen_formula

        returns a SMT formula from the aex wrt to data
        """
        pass


    def gen_template(self, idxs_vals=None, special=False):
        """
        special = True then it means we only have 1 data to compare against
        thus if the pass in indices of the leaves are 0's  , the result will be  z + 0*i = 0
        which then just gives z = 0, doesn't contribute to anything if we have only 1 data.
        Thus special flag turns the result z + 0*i = 0 into z = 0 and i = 1.

        EXAMPLES:

        sage: lt = Tree({'root':'R','children':[None,None,None]})
        sage: rt = Tree({'root': 'add', \
        'children': [{'root': 'C', 'children': [None]}, \
        {'root': 'D', 'children': [None]}]})
        sage: rs = AEXP(lt,rt).gen_template()
        sage: print rs.lt; print rs.rt
        R[None][None][None]
        add(C[_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i3*i3 + _add_0_C_0__i0],D[_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i3*i3 + _add_1_D_0__i0])



        sage: rs = AEXP({'root':'R','children':[None,None]}, \
        {'root':'add', 'children':[{'root':'C','children':[None]}, \
        {'root':'D','children':[None]}]}).gen_template()
        sage: print rs.lt; print rs.rt
        R[None][None]
        add(C[_add_0_C_0__i1*i1 + _add_0_C_0__i2*i2 + _add_0_C_0__i0],D[_add_1_D_0__i1*i1 + _add_1_D_0__i2*i2 + _add_1_D_0__i0])

        sage: rs = AEXP({'root':'R','children':[None,None]}, \
        {'root':'add', 'children':[None,None]}).gen_template(idxs_vals=[0,0],special=False)
        sage: print rs.lt; print rs.rt
        R[None][None]
        add(_add_0__i0,_add_1__i0)
        """
        if __debug__:
            assert not special or all(x == 0 for x in idxs_vals)
            assert idxs_vals is not None or not special


        if idxs_vals is None:
            ts = [1] + [var('i%d'%(i+1)) for i in srange(self.lt.get_nchildren())]
        else:
            ts = [1] + list(idxs_vals)


        rt = deepcopy(self.rt)  #make a copy

        leaves = rt.get_leaves()
        leaves = [(p,idx,tid) for p,idx,tid in leaves if p is not None]


        for p,idx,tid in leaves:
            prefix = '_%s__i'%'_'.join(map(str,tid))
            if special:
                c = {'first_idx':var(prefix+str(1)),'coef':var(prefix+str(0))}
            else:
                c = Miscs.gen_template(ts,rv=None,prefix=prefix)

            p.children[idx] = Tree(c)
            assert isinstance(p,Tree)

        #rt.replace_leaf(tid=[], special=special, ts=ts, verbose=verbose)

        return AEXP(lt=self.lt,rt=rt)



    def peelme(self, data):
        """
        Go through each nesting (aexp), generate a SMT formula, and checks its satisfiability.


        EXAMPLES:

        sage: data = {'C':{1: [(5,)], 2: [(4,)], 4: [(6,)], 5: [(1,)], 6: [(2,), (3,)], 8: [(0,)]},\
        'B': {0: [(4,)], 1: [(0,), (3,), (6,)], 7: [(5,)], -3: [(1,)], 5: [(2,)]},\
        'A':{1: [(1,)], -3: [(2,)], 7: [(0,)]}}

        sage: AEXP({'root':'A','children':[None]}, \
        {'root': 'B','children':[{'root':'C','children':[None]}]}).peelme(data=data)
        ['lambda A,B,C,i1: A[i1] == B[C[2*i1 + 1]]']

        sage: data = {'C':{0:[(0,),(3,)],9:[(1,),(8,)],7:[(2,),(5,)], 1:[(4,)],8:[(6,)],17:[(7,)]},\
        'B':{71:[(5,),(7,)],74:[(6,),(8,)],81:[(17,)]},\
        'A':{71:[(0,)],74:[(1,)],81:[(2,)]}}
        sage: AEXP({'root':'A','children':[None]},\
        {'root':'B','children':[{'root':'C','children':[None]}]}).peelme(verbose=1, data=data)
        ['lambda A,B,C,i1: A[i1] == B[C[i1 + 5]]']

        sage: data = {'A':{17:[(0,0)],8:[(0,1)],12:[(1,0)],3:[(1,1)]},\
        'C':{0:[(0,)],17:[(1,)],8:[(2,)],3:[(3,),(4,)]},\
        'D':{1:[(0,)],9:[(1,),(3,)],0:[(2,)]},\
        'add': {17:[(8,9),(17,0)],8:[(8,0)],12:[(3,9),(0,12)],3:[(3,0)]}}
        sage: rs = AEXP({'root':'A','children':[None]}, \
        {'root':'add','children':[{'root':'C' , 'children':[None]}, \
        {'root':'D','children':[None]}]}).peelme(verbose=1,data=data)

        sage: print '\n'.join(rs)
        lambda A,add,C,D,i1: A[i1] == add(C[i1 + 2],D[3])
        lambda A,add,C,D,i1: A[i1] == add(C[i1 + 2],D[1])
        lambda A,add,C,D,i1: A[i1] == add(C[2*i1 + 2],D[1])
        lambda A,add,C,D,i1: A[i1] == add(C[2*i1 + 2],D[3])


        """

        _gen_template = lambda iv,sp: \
            self.gen_template(idxs_vals=iv,special=sp)


        vi = [[(v,ids) for ids in idxs]
              for v,idxs in data[self.lt.get_root()].items()]
        vi = flatten(vi,list)

#        if verbose >= 3:
#            print 'vi: ', vi


        sts = [_gen_template(ids,sp = len(vi) == 1).rt for _,ids in vi]

        formula = [rh.gen_formula(v,data) for (v,_),rh in zip(vi,sts)]

        formula = Miscs._f(formula,'and',is_real=False)


        if formula is None:
            return None


        from common_z3 import get_models
        ms = get_models(formula,k=10)
        if len(ms) == 0: #no model, formula is unsat, i.e. no relation
            return None

        from smt_z3py import SMT_Z3
        ds = [SMT_Z3.get_constraints(m,result_as_dict=True) for m in ms]

        #generate the full expression
        template = _gen_template(None,False)

        rs = [template.__str__(leaf_content=d, do_lambda_format=True)
              for d in ds]

        if __debug__:
            assert all(isinstance(x,str) for x in rs)

        return rs



    ##### Static methods for AEXP #####

    @staticmethod
    def gen_aexps(nodes, xinfo, data, verbose):
        """
        arrs = [a,b,c]
        returns a=allpostrees(b,c)  , b = allpostrees(a,b)  , etc

        sage: nodes = map(Tree,[ \
        {'root':'A','children':[None]}, \
        {'root':'B','children':[None]}, \
        {'root':'C','children':[None]}])

        sage: data = {'A':{1: [(1,)], -3: [(2,)], 7: [(0,)]},\
        'B':{0: [(4,)], 1: [(0,), (3,), (6,)], 7: [(5,)], -3: [(1,)], 5: [(2,)]},\
        'C': {1: [(5,)], 2: [(4,)], 4: [(6,)], 5: [(1,)], 6: [(2,), (3,)], 8: [(0,)]}}
        sage: _ = AEXP.gen_aexps(nodes, xinfo={'All': ['A', 'B', 'C'], \
        'Const': [], 'Assume': [], 'Global': [], 'ZDims': {'A': 1, 'C': 1, 'B': 1}, \
        'Expect': [], 'ExtFun': [], 'Input': [], 'Output': []}, data=data, verbose=2)
        * gen_aexps [A,B,C]: 2 expressions generated
        0. A[i1] == B[C[(i1)_]]
        1. A[i1] == B[(i1)_]

        sage: nodes = map(Tree,[{'root':'A','children':[None]}, {'root':'C','children':[None]}, {'root':'B','children':[None]}])



        sage: _ = AEXP.gen_aexps(nodes, xinfo={'All': ['A', 'B', 'C'], \
        'Const': [], 'Assume': [], 'Global': [], 'ZDims': {'A': 1, 'C': 1, 'B': 1}, \
        'Expect': [], 'ExtFun': [], 'Input': [], 'Output': []}, data={}, verbose=2)
        * gen_aexps [A,C,B]: 12 expressions generated
        0. A[i1] == C[B[(i1)_]]
        1. A[i1] == C[(i1)_]
        2. A[i1] == B[C[(i1)_]]
        3. A[i1] == B[(i1)_]
        4. C[i1] == A[B[(i1)_]]
        5. C[i1] == A[(i1)_]
        6. C[i1] == B[A[(i1)_]]
        7. C[i1] == B[(i1)_]
        8. B[i1] == A[C[(i1)_]]
        9. B[i1] == A[(i1)_]
        10. B[i1] == C[A[(i1)_]]
        11. B[i1] == C[(i1)_]


        sage: nodes = map(Tree,[ \
        {'root':'A','children':[None]}, \
        {'root':'C','children':[None]}, \
        {'root':'B','children':[None]}])

        sage: _ = AEXP.gen_aexps(nodes, xinfo={'All': ['A', 'B', 'C'], \
        'Const': [], 'Assume': [], 'Global': [], 'ZDims': {'A': 1, 'C': 1, 'B': 1}, \
        'Expect': [], 'ExtFun': [], 'Input': [], 'Output': ['C']}, data={}, verbose=2)
        * gen_aexps [A,C,B]: 4 expressions generated
        0. C[i1] == A[B[(i1)_]]
        1. C[i1] == A[(i1)_]
        2. C[i1] == B[A[(i1)_]]
        3. C[i1] == B[(i1)_]

        """
        if __debug__:
            assert isinstance(nodes, list) and \
                all(isinstance(x,Tree) and x.is_node() for x in nodes)
            assert isinstance(xinfo, dict)


        blacklist = AEXP.gen_blacklist(xinfo, verbose=verbose)

        #Generate nestings
        def _gt(nodes, ln):
            if ln.get_root() not in data:
                vss = None
            else:
                vss = data[ln.get_root()].keys()
                assert all(not CM.is_iterable(v) for v in vss)

                vss = map(lambda v: tuple([v]),vss)

            rs =  Tree.gen_trees(nodes=nodes,vss=vss,
                                 blacklist=blacklist,
                                 data=data,
                                 verbose=verbose)

            return rs

        #Construct an AEXP
        def _ga(x):
            t = Tree({'root':x.get_root(), 'children':[None] * x.get_nchildren(),
                      'commute': x.is_commute()})

            return t

        if xinfo['Output']:
            #x = a[b[...]], x in output vars and a,b not in output vars
            anodes, lnodes = \
                CM.vpartition(nodes, lambda x: x.get_root() in xinfo['Output'])

            aexps = [[AEXP(_ga(ln),rn) for rn in _gt(anodes,ln)] for ln in lnodes]

        else:
            aexps= [[AEXP(_ga(ln),rn) for rn in _gt(CM.vsetdiff(nodes,[ln]),ln)]
                    for ln in nodes]

        aexps = flatten(aexps)

        #filter out unlikely array expressions
        aexps = [ae for ae in aexps if ae.is_ok(xinfo)]

        if verbose >= 1:
            print '* gen_aexps [%s]: %d expressions generated'\
                %(','.join(map(lambda x: str(x.get_root()),nodes)),len(aexps))

            if verbose >= 2:
                arrStrs = ['%d. %s'%(i,ae) for i,ae in Miscs.senumerate(aexps)]
                print '\n'.join(arrStrs)

        return aexps

    @staticmethod
    def gen_blacklist(xinfo):
        """
        Takes advantage of user inputs to reduce the number of generated nestings

        EXAMPLES:

        sage: AEXP.gen_blacklist({'All':['R','A','B','D','E','xor','g'], \
        'Input':['A','B'],'Output':['R'],'Global':[],'Const':[], \
        'ExtFun':['xor'],'Global':['g']})
        {'A': ['R', 'A', 'B', 'D', 'E', 'xor', 'g'],
        'R': ['R', 'A', 'B', 'D', 'E', 'xor', 'g', None],
        'B': ['R', 'A', 'B', 'D', 'E', 'xor', 'g'], 'xor': [None], 'g': [None]}

        """

        allVars    = xinfo['All']
        inputVars  = xinfo['Input']
        outputVars = xinfo['Output']
        globalVars = xinfo['Global']
        constVars  = xinfo['Const']
        extFuns    = [x for x in xinfo['ExtFun']]

        #Inputs must be leaves
        #e.g., a[i] = x[y[i']] is not possible
        #e.g., a[i] = xor[x[i'][y[i']]
        inputsLeaves = [{inp:allVars} for inp in inputVars]

        #Const must be leaves
        constLeaves = [{c:allVars} for c in constVars]

        #Extfuns are never leaves
        #e.g.,  r[i] = a[b[xor[i'][i']]]  is not possible
        extfunsNotLeaves = [{ef:[None]} for ef in extFuns]

        #Globals are never leaves
        globalsNotLeaves = [{gv:[None]} for gv in globalVars]

        #Outputs should never be part of the tree
        outputsNotInTree = [{oup:allVars + [None]} for oup in outputVars]

        ds = inputsLeaves+constLeaves + extfunsNotLeaves + \
            globalsNotLeaves + outputsNotInTree
        rs = CM.merge_dict(ds)

        return rs



class ExtFun(object):

    efdict = {
            'add'     : (lambda x,y: QQ(ZZ(x) + ZZ(y)), 2, True),
            'sub'     : (lambda x,y: QQ(ZZ(x) - ZZ(y)), 2, False), #not commute
            'xor'     : (lambda x,y: QQ(ZZ(x).__xor__(ZZ(y))), 2, True),
            'xor_xor' : (lambda x,y,z: QQ(ZZ(x).__xor__(ZZ(y)).__xor__(ZZ(z))), 3, True),
            'mod4'    : (lambda x: QQ(ZZ(x) % 4),   1, True),
            'mod255'  : (lambda x: QQ(ZZ(x) % 255), 1, True),
            'mul4'    : (lambda x: QQ(ZZ(x) * 4),   1, True),
            'div4'    : (lambda x: QQ(ZZ(x) // 4),  1, True)
            }

    def __init__(self, fn):
        assert isinstance(fn,str)
        self.fn = fn

    def __eq__(self, other):
        return type(other) is type(self) and self.__dict__ == other.__dict__

    def __ne__(self,other):
        return not self.__eq__(other)

    def __str__(self):
        return self.get_fname()

    def __hash__(self):
        return self.get_fname().__hash__()

    def get_fname(self):
        return self.fn

    def get_fun(self):
        """
        sage: ExtFun('xor').get_fun()(*[7,15])
        8
        sage: ExtFun('xor').get_fun()(8,9)
        1
        sage: ExtFun('xor').get_fun()(18,-9)
        -27
        sage: ExtFun('sub').get_fun()(128,1)
        127
        sage: ExtFun('sub').get_fun()(0,1)
        -1
        sage: ExtFun('xor').get_fun()(10,128)
        138
        sage: ExtFun('xor').get_fun()(128,10)
        138
        sage: ExtFun('mod4').get_fun()(128)
        0
        sage: ExtFun('mod4').get_fun()(127)
        3
        sage: ExtFun('mod4').get_fun()(1377)
        1
        sage: ExtFun('mod4').get_fun()(1378)
        2
        sage: ExtFun('mod4').get_fun()(1379)
        3
        sage: ExtFun('mod4').get_fun()(1380)
        0
        sage: ExtFun('div4').get_fun()(127)
        31
        sage: ExtFun('div4').get_fun()(128)
        32
        sage: ExtFun('div4').get_fun()(126)
        31
        """
        return ExtFun.efdict[self.get_fname()][0]

    def get_nargs(self):
        """
        Returns the number of function arguments

        EXAMPLES:
        sage: ExtFun('sub').get_nargs()
        2
        sage: ExtFun('something').get_nargs()
        Traceback (most recent call last):
        ...
        KeyError: 'something'

        """
        return ExtFun.efdict[self.get_fname()][1]

    def is_commute(self):
        """
        Returns true if the function is commutative

        sage: ExtFun('sub').is_commute()
        False
        sage: ExtFun('add').is_commute()
        True
        sage: ExtFun('something').is_commute()
        False
        """
        try:
            return ExtFun.efdict[self.get_fname()][2]
        except KeyError:
            """
            If we don't know anything about the function, then
            the default is non commutative.
            """
            return False

    def gen_data(self, avals, doDict):
        """
        Note: did not use caching because caching makes it slower.
        Probably because these functions are too simple that
        doesn't worth the caching overhead
        EXAMPLES:

        sage: ExtFun('add').gen_data([1,7,9,-1],doDict=False)
        [2, 8, 10, 0, 14, 16, 6, 18, -2, 1, 7, 9, -1]

        sage: ExtFun('add').gen_data([[1,7,9,-1]],doDict=False)
        [2, 8, 10, 0, 14, 16, 6, 18, -2, 1, 7, 9, -1]

        sage: ExtFun('add').gen_data([[1,7,9,-1]],doDict=True)
        * fun: add, fvals 9, idxs 16
        {'add': {0: [(1, -1)], 2: [(1, 1)], 6: [(7, -1)], 8: [(1, 7), (9, -1)], 10: [(1, 9)], 14: [(7, 7)], 16: [(7, 9)], 18: [(9, 9)], -2: [(-1, -1)]}}

        sage: ExtFun('sub').gen_data([[1,2],[5,6]], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]
        sage: ExtFun('sub').gen_data([[1,2,5,6]], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]
        sage: ExtFun('sub').gen_data([1,2,5,6], doDict=False)
        [0, -1, -4, -5, 1, -3, 4, 3, 5, 2, 6]

        sage: ExtFun('sub').gen_data([[1,2],[5,6]],doDict=True)
        * fun: sub, fvals 9, idxs 16
        {'sub': {0: [(1, 1), (2, 2), (5, 5), (6, 6)], 1: [(2, 1), (6, 5)], 3: [(5, 2)], 4: [(5, 1), (6, 2)], 5: [(6, 1)], -5: [(1, 6)], -4: [(1, 5), (2, 6)], -3: [(2, 5)], -1: [(1, 2), (5, 6)]}}

        sage: ExtFun('add').gen_data([[1,2,3,4],[5,6],[7,8,9]], doDict=False)
        [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 1]

        sage: ExtFun('add').gen_data([[1,2,3,4],[5,6],[7,8,9]], doDict=True)
        * fun: add, fvals 17, idxs 81
        {'add': {2: [(1, 1)], 3: [(1, 2)], 4: [(1, 3), (2, 2)], 5: [(1, 4), (2, 3)], 6: [(1, 5), (2, 4), (3, 3)], 7: [(1, 6), (2, 5), (3, 4)], 8: [(1, 7), (2, 6), (3, 5), (4, 4)], 9: [(1, 8), (2, 7), (3, 6), (4, 5)], 10: [(1, 9), (2, 8), (3, 7), (4, 6), (5, 5)], 11: [(2, 9), (3, 8), (4, 7), (5, 6)], 12: [(3, 9), (4, 8), (5, 7), (6, 6)], 13: [(4, 9), (5, 8), (6, 7)], 14: [(5, 9), (6, 8), (7, 7)], 15: [(6, 9), (7, 8)], 16: [(7, 9), (8, 8)], 17: [(8, 9)], 18: [(9, 9)]}}

        """

        avals = CM.vset(flatten(avals))
        alists = [avals] * self.get_nargs()
        idxs = CartesianProduct(*alists).list()
        fun_vals = [self.get_fun()(*idx) for idx in idxs]

        if doDict: #create dict
            cs = zip(fun_vals,idxs)
            cs = [(fv,tuple(idx)) for (fv,idx) in cs]

            d= CM.create_dict(cs)

            if self.is_commute():
                #[(1,2),(2,1),(2,2)] => [(1,2),(2,2)]
                d = dict([(k,CM.vset(v,Set)) for k, v in d.items()])

            rs = {self.get_fname():d}

            logger.debug('* fun: %s, fvals %d, idxs %d'\
                         %(self.get_fname(),len(d.keys()),len(idxs)))


        else:   #returns fun_vals as well as the orig avals
            rs =  CM.vset(fun_vals + avals)

        return rs


    @staticmethod
    def gen_extfuns(tc, xinfo):
        """
        EXAMPLES:


        sage: ExtFun.gen_extfuns(tc={'X':[1,7,9,15]}, xinfo={'ExtFun':['add'],'Output':[]})
        * gen_extfuns: 1 ext funs ['add']
        * gen_ef_data([add],|avals|=4)
        * fun: add, fvals 9, idxs 16
        {'X': [1, 7, 9, 15], 'add': {2: [(1, 1)], 8: [(1, 7)], 10: [(1, 9)], 14: [(7, 7)],
        16: [(1, 15), (7, 9)], 18: [(9, 9)], 22: [(7, 15)], 24: [(9, 15)], 30: [(15, 15)]}}

        sage: _ = ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['sub', 'add']})
        * gen_extfuns: 2 ext funs ['sub', 'add']
        * gen_ef_data([sub,add],|avals|=5)
        * fun: sub, fvals 21, idxs 100
        * fun: add, fvals 21, idxs 121

        sage: ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['xor', 'mod255']})
        * gen_extfuns: 2 ext funs ['xor', 'mod255']
        * gen_ef_data([xor,mod255],|avals|=5)
        * fun: xor, fvals 8, idxs 25
        * fun: mod255, fvals 8, idxs 8
        {'y': [2, 5, 1], 'x': [0, 1, 3], 'z': [153, 173, 184, 65], 'xor': {0: [(2, 2), (5, 5), (1, 1), (0, 0), (3, 3)], 1: [(2, 3), (1, 0)], 2: [(2, 0), (1, 3)], 3: [(2, 1), (0, 3)], 4: [(5, 1)], 5: [(5, 0)], 6: [(5, 3)], 7: [(2, 5)]}, 'mod255': {0: [(0,)], 1: [(1,)], 2: [(2,)], 3: [(3,)], 4: [(4,)], 5: [(5,)], 6: [(6,)], 7: [(7,)]}}


        sage: ExtFun.gen_extfuns({'x': [0, 1, 3], 'y': [2, 5, 1], 'z': [153, 173, 184, 65]}, \
        {'Output': ['z'], 'ExtFun': ['xor', 'mod255']})
        * gen_extfuns: 2 ext funs ['xor', 'mod255']
        * gen_ef_data([xor,mod255],|avals|=5)
        * fun: xor, fvals 8, idxs 25
        * fun: mod255, fvals 8, idxs 8
        {'y': [2, 5, 1], 'x': [0, 1, 3], 'z': [153, 173, 184, 65], 'xor': {0: [(2, 2), (5, 5), (1, 1), (0, 0), (3, 3)], 1: [(2, 3), (1, 0)], 2: [(2, 0), (1, 3)], 3: [(2, 1), (0, 3)], 4: [(5, 1)], 5: [(5, 0)], 6: [(5, 3)], 7: [(2, 5)]}, 'mod255': {0: [(0,)], 1: [(1,)], 2: [(2,)], 3: [(3,)], 4: [(4,)], 5: [(5,)], 6: [(6,)], 7: [(7,)]}}


        sage: ExtFun.gen_extfuns({'R':[128,127,126,125], 'N':[128],'x': [0, 7]}, \
        {'Output': ['R'], 'ExtFun': ['sub']})
        * gen_extfuns: 1 ext funs ['sub']
        * gen_ef_data([sub],|avals|=6)
        * fun: sub, fvals 25, idxs 36
        {'x': [0, 7], 'R': [128, 127, 126, 125], 'sub': {0: [(0, 0), (7, 7), (128, 128), (1, 1), (2, 2), (3, 3)], -128: [(0, 128)], 2: [(2, 0), (3, 1)], 3: [(3, 0)], 4: [(7, 3)], 5: [(7, 2)], 6: [(7, 1)], 7: [(7, 0)], 128: [(128, 0)], -126: [(2, 128)], -125: [(3, 128)], -127: [(1, 128)], 1: [(1, 0), (2, 1), (3, 2)], -121: [(7, 128)], -2: [(0, 2), (1, 3)], -7: [(0, 7)], -3: [(0, 3)], -1: [(0, 1), (1, 2), (2, 3)], 121: [(128, 7)], -6: [(1, 7)], -5: [(2, 7)], -4: [(3, 7)], 125: [(128, 3)], 126: [(128, 2)], 127: [(128, 1)]}, 'N': [128]}


        """
        assert xinfo is not None

        extfuns = map(ExtFun,xinfo['ExtFun'])

        if extfuns == []:
            return tc

        logger.debug('* gen_extfuns: %d ext funs'%len(extfuns), map(str,extfuns))

        #don't consider values of 'output' arrays
        avals = [tc[a] for a in tc if a not in xinfo['Output']]

        #the range of the outputs are also included to have e.g. R[i] = sub(N,i)
        lo = map(len,[tc[a] for a in tc if a in xinfo['Output']])

        if lo:  #  != []
            avals = avals + [range(max(lo))]

        avals = vset(flatten(avals))


        #generate new array representing external functions
        d = ExtFun.gen_ef_data(extfuns,avals)

        tc_ = merge_dict(d+[tc])
        return tc_



    @staticmethod
    def gen_ef_data(extfuns,avals):
        """
        create representations for extfuns
        Note: the order of F matters (see example below when add,xor,xor_xor gens 63
        but xor,add,xor_xor gens 124.

        EXAMPLES
        sage: rs = ExtFun.gen_ef_data(map(ExtFun,['add','xor','xor_xor']),[1,2,256,9]); len(rs[0].values()[0])
        * gen_ef_data([add,xor,xor_xor],|avals|=4)
        * fun: add, fvals 30, idxs 64
        * fun: xor, fvals 8, idxs 64
        * fun: xor_xor, fvals 16, idxs 1331
        30

        sage: rs = ExtFun.gen_ef_data(map(ExtFun,['xor','add','xor_xor']),[1,2,256,9]); len(rs[0].values()[0])
        * gen_ef_data([xor,add,xor_xor],|avals|=4)
        * fun: xor, fvals 8, idxs 64
        * fun: add, fvals 30, idxs 64
        * fun: xor_xor, fvals 95, idxs 2197
        8
        """
        logger.debug('* gen_ef_data([%s],|avals|=%d)'\
                %(','.join(map(str,extfuns)),len(flatten(avals))))


        if len(extfuns) == 1:
            F_avals = [avals]
        else:
            assert CM.vall_uniq(map(lambda f: f.get_fname(),extfuns)), \
                'extfuns list cannot contain duplicate'

            F_rest = [CM.vsetdiff(extfuns,[f]) for f in extfuns]

            F_avals = [ExtFun.get_outvals(tuple(fs),tuple(avals))
                       for fs in F_rest]


        F_d = [fn.gen_data(f_aval,doDict=True)
               for fn,f_aval in zip(extfuns,F_avals)]


        return F_d


    @cached_function
    def get_outvals(extfuns,avals):
        """
        Recursive function that returns the all possible input values

        [f,g,h],[avals] =>  f(g(h(avals)))

        EXAMPLES:

        sage: ExtFun.get_outvals(tuple(map(ExtFun,['sub'])),tuple([1,2,256]))
        [0, -1, -255, 1, -254, 255, 254, 2, 256]
        sage: ExtFun.get_outvals(tuple(map(ExtFun,['xor_xor'])),tuple([1,2,256]))
        [1, 2, 256, 259]
        sage: ExtFun.get_outvals(tuple(map(ExtFun,['xor_xor','add'])),tuple([1,2,256]))
        [2, 3, 257, 4, 258, 512, 1, 256]
        sage: ExtFun.get_outvals(tuple(map(ExtFun,['add','xor_xor'])),tuple([1,2,256]))
        [1, 2, 256, 259]
        """

        if __debug__:
            assert len(extfuns) >= 1
            assert all(isinstance(f, ExtFun) for f in extfuns)


        if len(extfuns) > 1:
            avals = ExtFun.get_outvals(extfuns[1:],avals)
        else:
            avals = extfuns[0].gen_data(avals,doDict=False)

        return avals
