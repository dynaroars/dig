import vu_common as CM
from miscs import Miscs

from refine import Refine
from invgen import Inv

from sage.all import *


class Eqt(Inv):
    """
    Find Equalities using standard equation solving

    EXAMPLES:
    ig = InvGen("Traces/NLA/cohendiv.tcs",verbose=1)
    _ =  ig.getInvs(inv_typ='eqt',seed=1)

    *** InvGen ***
    Sun Jun  3 21:42:07 2012
    Sage Version 5.0, Release Date: 2012-05-14
    Godel.local Darwin 10.8.0 x86_64
    *** ReadFile ***
    read 'Traces_ICSE2012/NLA/cohendiv.tcs'
    number of traces (tcs) read: 2685
    read 'Traces_ICSE2012/NLA/cohendiv.ext'
    0. |tcs|: 2685
    1. |tcs2|: 0
    2. vs: [a, b, q, rvu, x, y]
    3. xinfo: 
    0. All: ['a', 'b', 'q', 'rvu', 'x', 'y']
    1. Assume: ['rvu >= 2*b']
    2. Const: []
    3. Expect: ['b = ay', 'x = qy+r', 'rvu >= 2*y*a']
    4. ExtFun: []
    5. Global: []
    6. Input: []
    7. Output: []
    Time elapsed: 0.1373 s (ReadFile)
    seed 1 (test 0.829402 0.595912 0.429361)
    * gen_terms(deg=2,vs=[q, x, rvu, b, y, a])
    Generate 28 terms
    set tcs2 to 1000
    sample_traces: chose |tcs1|=42, |tcs2|=1000 (attempted 42/2685 tcs)
    Time elapsed: 0.0015 s (function sample_traces)
    *** Eqt ***
    Create equations from 42 data
    * EQ: Solve 42 (uniq) eqts for 28 unknowns coeffs
    Time elapsed: 2.7277 s (solve)
    Refine 3 candidate invariants
    * rfilter(|ps|=3,|tcs|=1000)
    rfilter (before 3, after 3, diff 0)
    * rinfer(|ps|=3)
    rinfer (before 3, after 2, diff 1)
    Time elapsed: 0.4703 s (refine)
    Detected Invariants for Eqt:
    0: -a*y + b == 0
    1: q*y + rvu - x == 0
    *** IeqDeduce ***
    |assumes|=1, |eqts|=2
    * deduce(|assumes|=1,|eqts|=2)
    ('assumed ps: ', [-2*b + rvu >= 0])
    Time elapsed: 0.0220 s (solve)
    Refine skips (Deduction method)
    Time elapsed: 0.0000 s (refine)
    Detected Invariants for IeqDeduce:
    0: -2*a*y + rvu >= 0
    1: -q*y - 2*b + x >= 0
    """

    def __init__(self,terms,tcs1,tcs2,xinfo,verbose):
        
        super(Eqt,self).__init__(
            terms   = terms,
            tcs1    = tcs1,
            tcs2    = tcs2,
            xinfo   = xinfo,
            verbose = verbose)

    def solve(self):
        sols = Miscs.solve_eqts(ts      = self.terms,
                                rv      = 0,
                                ds      = self.tcs1,
                                verbose = self.verbose)
        self.sols = sols

    def refine(self):
        super(Eqt,self).refine()
        
        rf = Refine(ps=self.sols,verbose=self.verbose)
        rf.rrank()
        rf.rfilter(tcs=self.tcs2)
        rf.rinfer()

        self.sols = rf.ps


class IeqDeduce(Inv):
    """
    Find Inequalities by Deduction (require external information, i.e assumes)

    sage: var('b rvu a y q')
    (b, rvu, a, y, q)

    sage: ieqdeduce = IeqDeduce(xinfo={'Assume':['-2*b + rvu >= 0']},eqts=[-a*y + b == 0,q*y + rvu - x == 0],verbose=1)
    Traceback (most recent call last):
    ...
    AssertionError: Assumes (['-2*b + rvu >= 0']) and Eqts ([-a*y + b == 0, q*y + rvu - x == 0]) must be relational

    sage: ieqdeduce = IeqDeduce(xinfo={'Assume':[-2*b + rvu >= 0]},eqts=[-a*y + b == 0,q*y + rvu - x == 0],verbose=1)
    *** IeqDeduce ***
    |assumes|=1, |eqts|=2

    sage: ieqdeduce.go()
    * deduce(|assumes|=1,|eqts|=2)
    ('assumed ps: ', [-2*b + rvu >= 0])
    ...
    Refine 2 candidate invariants
    Refine skips (Deduction method)
    ...
    Detected Invariants for IeqDeduce:
    0: -2*a*y + rvu >= 0
    1: -q*y - 2*b + x >= 0

    """

    def __init__(self,eqts,xinfo,verbose):
        
        if __debug__:
            assert eqts, 'Eqts ({}) cannot be empty'.format(eqts)
            assert xinfo['Assume'], \
                'Assumes ({}) cannot be empty'.format(xinfo['Assume'])

            msg = 'Assumes ({}) and Eqts ({}) must be relational'
            assert all(isinstance(x, Miscs.sage_expr) and x.is_relational()
                       for x in xinfo['Assume'] + eqts), \
                       msg.format(xinfo['Assume'],eqts)
                       

        super(IeqDeduce,self).__init__(
            terms   = [],
            tcs1    = [],
            tcs2    = [],
            xinfo   = xinfo,
            verbose = verbose)

        if verbose >= 1:
            msg = '|assumes|={}, |eqts|={}'
            print(msg.format(len(xinfo['Assume']),len(eqts)))


        self.eqts = eqts


    def solve(self):
        assumes = [assume-assume.rhs() for assume in self.xinfo['Assume']]

        sols = IeqDeduce.deduce(assumes = assumes,
                                eqts    = self.eqts,
                                verbose = self.verbose)
        self.sols = sols


    def refine(self):
        super(IeqDeduce,self).refine()

        if self.verbose >= 1:
            print('Refine skips (Deduction method)')
            

    ##### Helpers for IeqDeduce #####

    @staticmethod
    def substitute(e1,e2,verbose=1):
        """
        EXAMPLES:

        sage: var('x t q b y a')
        (x, t, q, b, y, a)

        sage: IeqDeduce.substitute(t-2*b>=0,x==q*y+t)
        [-q*y - 2*b + x >= 0]


        sage: IeqDeduce.substitute(t-2*b>=0,b-y*a==0)
        [-2*a*y + t >= 0]

        sage: IeqDeduce.substitute(t-2*b>=0,b-4==0)
        [t - 8 >= 0]

        sage: IeqDeduce.substitute(t-2*b>=0,b+4==0)
        [t + 8 >= 0]

        sage: IeqDeduce.substitute(t-2*b>=0,b^2+4==0)
        [t + 4*I >= 0, t - 4*I >= 0]
        
        sage: IeqDeduce.substitute(t-2*b>=0,b^2-4==0)
        [t + 4 >= 0, t - 4 >= 0]

        #todo: cannot do when e2 is not equation
        sage: IeqDeduce.substitute(2*b>=0,b>=5)
        W: substitution fails on b >= 5
        2*b >= 0

        sage: IeqDeduce.substitute(2*b==0,b>=5)
        W: substitution fails on b >= 5
        2*b == 0
        """

        e1_vs = Miscs.get_vars(e1)
        e2_vs = Miscs.get_vars(e2)

        rs = [solve(e2,e2_v,solution_dict=True) 
              for e2_v in e2_vs if e2_v in e1_vs]
        
        rs = flatten(rs)
        
        try:
            rs = [e1.subs(rs_) for rs_ in rs]
            return rs
        except Exception:
            print 'W: substitution fails on', e2
            return e1
        

    @staticmethod
    def deduce(assumes,eqts,verbose=1):
        """
        EXAMPLES:
        
        sage: var('r a b q y x'); IeqDeduce.deduce([r>=2*b],[b==y*a,x==q*y+r],verbose=0)
        (r, a, b, q, y, x)
        [r >= 2*a*y, -q*y + x >= 2*b]

        sage: var('s n a t'); IeqDeduce.deduce([s<=n],[t==2*a+1,s==a**2+2*a+1],verbose=0)
        (s, n, a, t)
        [a^2 + 2*a + 1 <= n]

        """
        if verbose >= 1:
            msg = '* deduce(|assumes|={},|eqts|={})'
            print(msg.format(len(assumes),len(eqts)))
            print('assumed ps: ' , assumes)

        combs = [(aps,ei) for aps in assumes for ei in eqts
                 if any(x in Miscs.get_vars(aps) for x in Miscs.get_vars(ei))]
        
        #if CM.vany(Miscs.get_vars(ei),lambda x: x in Miscs.get_vars(aps))

        sols= [IeqDeduce.substitute(e1,e2) for e1,e2 in combs]
        sols = flatten(sols,list)

        return sols



class IeqMPP(Inv):
    """
    Generating Disjoint invariants (e.g.\ Max(x,y) >= z means x >= z or y >= z)
    using Max-Plus polyhedron (MPP)
    
    * building a MPP  takes *quadratic* time, O(np^2),
    where n is the # of generator, p is the number of points
    
    """
    def __init__(self,terms,tcs1,tcs2,xinfo,do_min=False,verbose=1):
        """
        Example:
        #sage: var('rvu,a,y')
        (rvu, a, y)
        #sage: mpp = IeqMPP(terms=[rvu,a,y],tcs1=ig.tcs,tcs2=[])
        #sage: mpp.solve()
        #sage: mpp.go()

        """
        super(IeqMPP,self).__init__(
            terms   = terms,
            tcs1    = tcs1,
            tcs2    = tcs2,
            xinfo   = xinfo,
            verbose = verbose)

        self.do_min = do_min
        

    def solve(self): #mpp
        ts = [t for t in self.terms if str(t) != '1']

        if self.verbose >= 1:
            print 'Create vertices from %d data' %len(self.tcs1)


        if self.do_min == 2:
            ts = ts + [-1*t for t in ts]
            
        vts = [[t.subs(tc) for t in ts] for tc in self.tcs1]
        vts = CM.vset(vts,idfun=repr)


        #add 0 to the end of each vertex and identity to ts
        vts = [vt + [SR(0)] for vt in vts]
        ts = ts + [SR(0)]  #the identity element is 0 in MPP

        if self.do_min == 1:
            vts = [[-1*v for v in vt] for vt in vts]
            ts = [-1*t for t in ts]           


        rs = IeqMPP.build_poly(vts,verbose=self.verbose)

        if CM.is_none_or_empty(rs):
            self.sols = []
        else:
            #parse the result
            rs = map(lambda s: IeqMPP._parse(s,ts,cleanup=True),rs)
            rs = [r_ for r_ in rs if r_ is not None]
            self.sols = rs

    def refine(self):
        super(IeqMPP,self).refine()

        rf = Refine(ps=self.sols,verbose=self.verbose)
        rf.rrank()
        rf.rfilter(tcs=Miscs.keys_to_str(self.tcs1 + self.tcs2))

        self.sols = rf.ps


    ##### Helpers for IeqMPP #####
    @staticmethod
    def build_poly(vts,verbose=1):
        """
        Build a MPP convex polyhedron over vts and
        returns a set of constraints

        EXAMPLES:
        
        sage: IeqMPP.build_poly([[0,0,0],[3,3,0]])
        * INEQ: Constructing (MPP) Polyhedra with 2 (uniq) vertices in 3 dim
        ['[-oo,0,-oo,-oo,-oo,0]', '[0,-oo,-oo,-oo,-oo,0]', '[0,-oo,-oo,-oo,-oo,-oo]',
        '[-oo,0,-oo,-oo,-oo,-oo]', '[-oo,-oo,0,-oo,-oo,-oo]', '[-oo,-oo,0,-oo,-oo,0]',
        '[-oo,-oo,0,-oo,-3,-oo]', '[-oo,-oo,0,-3,-oo,-oo]', '[-oo,0,-oo,-oo,0,-oo]',
        '[-oo,0,-oo,0,-oo,-oo]', '[0,-oo,-oo,-oo,0,-oo]', '[0,-oo,-oo,0,-oo,-oo]']

        
        """

        if verbose >= 1:
            print('* INEQ: Constructing (MPP) Polyhedra with '
                  '%d (uniq) vertices in %d dim'
                  %(len(vts),len(vts[0])))

        #if any of the vertex is float
        opt_arg = ''

        if any(any(not SR(v).is_integer() for v in vt) for vt in vts):
            vts = [[RR(v).n() for v in vt] for vt in vts]
            opt_arg = '-numerical-data ocaml_float'


        #exec external program
        #important,  has to end with newline \n !!!
        vts_s = '\n'.join([str(vt).replace(' ','') for vt in vts]) + '\n'

        cmd = 'compute_ext_rays_polar %s %d'%(opt_arg, len(vts[0]))

        rs,rs_err = CM.vcmd(cmd,vts_s,verbose=verbose)
        
        if verbose >= 2:
            print 'vts_s:\n',vts_s
            print 'cmd:', cmd
            print 'rs_err:', rs_err            
            print 'rs:\n',rs
        rs = rs.split()

        return rs
    
    ##### Static methods #####
    @staticmethod
    def _parse(s,ts,cleanup=True):
        """
        Parses the return string s from
        'compute_ext_rays_polar' in TPLib into proper lambda format
        
        
        EXAMPLES:
        
        sage: var('x,y,z,d')
        (x, y, z, d)
        
        sage: IeqMPP._parse('[-oo,0,-oo,-oo,-6,-oo,-oo,-oo]',[x,y,z,d])
        'lambda x,y: y >= x - 6'
        
        
        sage: IeqMPP._parse('[-oo,-oo,-oo,9,-6,-oo,-oo,20]',[x,y,z,d])
        'lambda d,x: d + 9 >= max(x - 6,d + 20)'

        """
        
        ls = sage_eval(s.replace('oo','Infinity'))
        assert len(ts)*2 == len(ls)
        l = len(ls)/2
        
        def _add(x,y) :
            if __debug__:
                assert abs(y) != Infinity

            if abs(x) == Infinity:
                return x 
            else:
                return x + y
        
        lhs = [_add(x,y) for (x,y) in zip(ls[:l],ts)] 
        rhs = [_add(x,y) for (x,y) in zip(ls[l:],ts)]

        #clean up the result
        
        if cleanup:
            #remove -Inf since max(x,-Infinity,y) = max(x,y)
            rem_ninf = lambda ls: [l for l in ls if abs(l) != Infinity]
            lhs = rem_ninf(lhs)
            rhs = rem_ninf(rhs)

            #if lhs contains the same exact elems as rhs then remove
            #b/c it's a tautology, e.g. max(x,y) >= max(y,x)
            if set(lhs) == set(rhs):
                return None

            #if one of these is empty, i.e.\ contained only +/-Inf originally
            #then remove
            if lhs == [] or rhs == []:
                return None


        rs = IeqMPP._gen_lambda_exp(lhs,rhs)
        return rs

    @staticmethod
    def _gen_lambda_exp(lhs,rhs):
        """
        Returns the lambda expression involving max of the form
        max(x,y...) >= max(x,y...)


        EXAMPLES:
        
        sage: var('y')
        y

        sage: IeqMPP._gen_lambda_exp([x-10,y-3],[y,5])
        'lambda x,y: max(x - 10,y - 3) >= max(y,5)'

        
        """
        assert not(CM.is_none_or_empty(lhs) or CM.is_none_or_empty(rhs))
        
        vs = Miscs.get_vars(lhs+rhs)
        rs = 'lambda %s: '%(','.join(map(str,vs)))



        to_str = lambda s: 'max(%s)'%','.join(map(str,s)) \
            if len(s)>1 else str(s[0])
        lhs_s = to_str(lhs)
        rhs_s = to_str(rhs)
    
        rs = rs + (lhs_s + ' >= '  + rhs_s)

        return rs


class IeqCLPoly(Inv):
    """
    Find Inequalities using Classic Polyhedra

    Complexity: 
    * building a Classic polyhedron takes *exponential* time wrt number
    of terms, so generally a (small) number of terms need to be specified.

    Traces: Unlike other type of invariants, it's much harder to obtain
    testcases exhibiting the Inequality. I.e. it's easy to get x+y>10,
    but much harder to get x+y = 10.  And we need both to get x+y >= 10.

    """
    
    def __init__(self, terms, tcs1, tcs2, xinfo, verbose):
        """
        Example:
        #sage: var('rvu,a,y')
        (rvu, a, y)
        #sage: clp = IeqCLPoly(terms=[rvu,a,y],tcs1=ig.tcs,tcs2=[])
        #sage: clp.solve()

        """
        super(IeqCLPoly,self).__init__(
            terms   = terms,
            tcs1    = tcs1,
            tcs2    = tcs2,
            xinfo   = xinfo,
            verbose = verbose)
    
    def solve(self): #classic polyhedra

        ts = [t for t in self.terms if str(t) != '1']

        if self.verbose >= 1:
            print 'Create vertices from %d data' %len(self.tcs1)

        vts = [[QQ(t.subs(tc)) for t in ts] for tc in self.tcs1]
        vts = map(list,set(map(tuple,vts)))

        rs = self.build_poly(vts)

        if CM.is_none_or_empty(rs):
            self.sols = []
        else:
            #parse the result
            _f = lambda s: s[0] + sum(map(prod,zip(s[1:],ts)))
            rs = [_f(s) >= 0 for s in rs]

            #remove trivial (tautology) str(x) <=> str(x)
            rs = [s for s in rs
                  if not (s.is_relational() 
                          and str(s.lhs()) == str(s.rhs()))]
        
            self.sols = rs

    def refine(self):
        super(IeqCLPoly,self).refine()

        rf = Refine(ps=self.sols,verbose=self.verbose)
        rf.rrank()
        rf.rfilter(tcs=self.tcs2)
        rf.rinfer()

        self.sols = rf.ps

    ##### Helpers for IeqCLPoly #####
    def build_poly(self,vts,verbose=1):
        """
        Builds a classic convex polyhedron over vts and
        returns a set of constraints (i.e. the facets of the polyhedron)
        """
        
        if self.verbose >= 1:
            print('* INEQ: Constructing (Classic) Polyhedra with '
                  '%d (uniq) vertices in %d dim'%(len(vts),len(vts[0])))
            


        poly,_ = CM.vtime(Polyhedron,{'vertices':vts,'base_ring':QQ},s="Polyhedra")
        try:
            rs = [list(p.vector()) for p in poly.inequality_generator()]
            
            if verbose >= 1:
                print 'Sage: found %d inequalities' %len(rs)

            #remove rs of form [const_c, 0 , ..., 0]
            #because those translate to the trivial form 'const_c >= 0'
            rs = [s for s in rs if any(x != 0 for x in s[1:])]
            return rs

        except AttributeError:
            if verbose >= 1:
                print 'Sage cannot construct polyhedron'
            return []


class IeqFPoly(Inv):
    """
    Find inequalities of the *fixed* form
    c0 + c1t1 + ... + c2tn >= 0, where ti are terms 
    and  ci are coefficients, by enumerating 
    all possible ineqs.

    The complexity (# of inequalities generated) is O(|cs|^|ts|), 
    thus is exponential to the # of terms.


    EXAMPLES:

    #sage: ig = InvGen("Traces/NLA/cohendiv.tcs",verbose=1)
    *** InvGen ***
    Sat Jun  9 16:28:19 2012
    Sage Version 5.0, Release Date: 2012-05-14
    Godel.local Darwin 10.8.0 x86_64
    *** ReadFile ***
    read 'Traces/NLA/cohendiv.tcs'
    number of traces (tcs) read: 2685
    read 'Traces/NLA/cohendiv.ext'
    0. |tcs|: 2685
    1. |tcs2|: 0
    2. vs: [a, b, q, rvu, x, y]
    3. xinfo: 
    0. All: ['a', 'b', 'q', 'rvu', 'x', 'y']
    1. Assume: ['rvu >= 2*b']
    2. Const: []
    3. Expect: ['b = ay', 'x = qy+r', 'rvu >= 2*y*a']
    4. ExtFun: []
    5. Global: []
    6. Input: []
    7. Output: []
    Time elapsed: 0.0984 s (ReadFile)
    
    #sage: _ = ig.getIeqs(terms=[rvu,y*a])
    set tcs2 to 1000
    sample_traces: chose |tcs1|=100, |tcs2|=1000 (attempted 100/2685 tcs)
    Time elapsed: 0.0024 s (function sample_traces)
    *** IeqFPoly ***
    Generate approx 49 fpoly ieqs
    Time elapsed: 0.0039 s (solve)
    Refine 48 candidate invariants
    rrank (before 48, after 48, diff 0)
    * rfilter(|ps|=48,|tcs|=1100)
    rfilter (before 48, after 21, diff 27)
    * rinfer(|ps|=21)
    rinfer (before 21, after 2, diff 19)
    Time elapsed: 3.8657 s (refine)
    Detected Invariants for IeqFPoly:
    0: 3*a*y >= 0
    1: -3*a*y + 3*rvu >= 0

    """
    
    def __init__(self, terms, tcs, cs, xinfo, verbose):
        super(IeqFPoly,self).__init__(
            terms = terms,
            tcs1  = tcs,
            tcs2  = [],
            xinfo = xinfo,
            verbose = verbose)

        self.cs = cs

    def solve(self):
        ieqs = IeqFPoly.gen_fpoly_ieqs(ts=self.terms, 
                                       cs=self.cs,
                                       verbose=self.verbose)
        
        self.sols = ieqs

    def refine(self):
        super(IeqFPoly,self).refine()            

        rf = Refine(ps=self.sols, verbose=self.verbose)
        rf.rrank()
        #do not change this order (filter then infer), because 
        #rinfer will remove some of the default ones
        #e.g., [x - 1 >= 0, -x - 1 >= 0] removes y>=0  
        rf.rfilter(tcs=self.tcs1)  
        rf.rinfer()         
        self.sols = rf.ps


    ##### Helpers for IeqFPoly #####
    @staticmethod
    def gen_fpoly_ieqs(ts, cs, verbose=1):
        """
        EXAMPLES:

        sage: var('y, z')
        (y, z)

        sage: IeqFPoly.gen_fpoly_ieqs([1,x,y],[0,2],verbose=0)
        [2*y >= 0, 2*x >= 0, 2*x + 2*y >= 0, 2*y + 2 >= 0, 2*x + 2 >= 0, 2*x + 2*y + 2 >= 0]

        sage: IeqFPoly.gen_fpoly_ieqs([x,y^2],[0,2],verbose=0)
        [2*y^2 >= 0, 2*x >= 0, 2*y^2 + 2*x >= 0]

        sage: IeqFPoly.gen_fpoly_ieqs([x,y^2],[0],verbose=0)
        []

        sage: IeqFPoly.gen_fpoly_ieqs([x,y^2],[1],verbose=0)
        [y^2 + x >= 0]

        sage: IeqFPoly.gen_fpoly_ieqs([x,z],cs=(-1,1),verbose=0)
        [z >= 0, -z >= 0, x >= 0, x + z >= 0, x - z >= 0, -x >= 0, -x + z >= 0, -x - z >= 0]

        sage: IeqFPoly.gen_fpoly_ieqs([x,z],cs=(-1,1,'s'),verbose=0)
        Traceback (most recent call last):
        ...
        AssertionError: coefs must contain numerical values

        """

        assert all(CM.isnum(x) for x in cs), \
            'coefs must contain numerical values'

        #gen template of the form c0 + c1t1 + ... + c2tn >= 0
        template, vs = Miscs.gen_template(ts, rv=0, op=operator.ge,
                                          prefix=None, ret_coef_vs=True,
                                          verbose=verbose)

        if isinstance(cs, tuple):
            assert len(cs)==2, "Specify upper and lowerbound"
            assert cs[0] <= cs[1], "Lower has to be <= Upper"
            cs = srange(cs[0],cs[1]+1)

        #change the order of [-2,-1,0,1,2] to [0,1,2,-1,-2]
        ge_0,lt_0 = CM.vpartition(cs,lambda x: x < 0)
        lt_0 = sorted(lt_0,key=lambda x: abs(x))
        cs = ge_0 + lt_0


        cps = CartesianProduct(*([cs]*len(ts)))
        if verbose >= 1:
            print 'Generate approx %d (%d^%d) fpoly ieqs'\
                %(cps.cardinality(),len(cs),len(ts))

        #mults of -3,2 = [2,3]
        mults = srange(2,max(map(abs,cs))+1) 

        d = {(0,)*len(ts):None}  #[0,0,..] is filtered
        rs = []
        for cp in cps:
            if tuple(cp) not in d:
                rs.append(cp)

                d[tuple(cp)] = None                
                for m in mults:
                    w = [m*c for c in cp]
                    d[tuple(w)]=cp

        

        #instantiate coefs
        ieqs = [template.subs(dict(zip(vs,rs_))) for rs_ in rs]


        #remove ieqs of the form num <= 0
        ieqs = [ieq for ieq in ieqs if not ieq.lhs().is_numeric()]
        return ieqs    





class IeqOct(Inv):
    """
    Find inequalities of the form +/-t1 +/-t2 >= c 
    where t_i are terms and c_i are coefficients.
    These inequalities are called Octagonal constraints in
    Abstract Interpretation.

    For each pair of terms (t1,t2), the method generates exactly 
    8 constraints with linear complexity in time and space of the traces.
    
    The # of pairs of ts from a list ts of terms is choose(ts,2).
    Thus, it is exponential in the number of terms.

    EXAMPLES:

    #Read in a test case t1.tcs (extra info is in t1.ext)

    #sage: ig = InvGen("Examples/t1.tcs",verbose=1)
    *** InvGen ***
    Tue Sep 11 21:32:32 2012
    Sage Version 5.2, Release Date: 2012-07-25
    GiaoChi Darwin 10.8.0 x86_64
    *** ReadFile ***
    read 'Examples/t1.tcs'
    number of traces (tcs) read: 6
    read 'Examples/t1.tcs2'
    number of traces (tcs) read: 1
    read 'Examples/t1.ext'
    0. |_tcs|: 6
    1. |_tcs2|: 1
    2. _vs: [x, y]
    3. _xinfo: 
    0. All: ['x', 'y']
    1. Assume: [y >= x]
    2. Const: []
    3. Expect: ['2*x + 1 >= y']
    4. ExtFun: []
    5. Global: []
    6. Input: []
    7. Output: []
    Time elapsed: 0.0029 s (ReadFile)

    #Finding Octagonal constraints
    #sage: _ = ig.getInvs(inv_typ='ieq oct',seed=1,vs = ig.vs,deg=2)
    seed 1 (test 0.829402 0.595912 0.429361)
    * gen_terms(deg=2,vs=[x, y])
    Generate 6 terms
    sample_traces: chose |tcs1|=6, |tcs2|=0 (attempted 100/6 tcs)
    Time elapsed: 0.0000 s (function sample_traces)
    *** IeqOct ***
    Time elapsed: 0.0342 s (solve)
    Refine 80 candidate invariants
    rrank (before 80, after 80, diff 0)
    * rfilter(|ps|=80,|tcs|=1)
    rfilter (before 80, after 80, diff 0)
    * rinfer(|ps|=80)
    rinfer (before 50, after 7, diff 43)
    Time elapsed: 1.8314 s (refine)
    Detected Invariants for IeqOct:
    0: -1 <= y
    1: -x*y + x <= -2
    2: -x^2 + y <= 2
    3: x*y - y^2 <= 0
    4: -y^2 + y <= -2
    5: -101 <= x - y
    6: -9799 <= -x^2 + y



    """
    
    def __init__(self, terms, tcs1, tcs2, xinfo, verbose):
        super(IeqOct,self).__init__(
            terms = terms,
            tcs1  = tcs1,
            tcs2  = tcs2,
            xinfo = xinfo,
            verbose = verbose)


    def solve(self):
        ts = [t for t in self.terms if str(t) != '1']

        are_inputs = lambda vs: all(v in self.xinfo['Input'] for v in vs)
        are_self = lambda vs: len(CM.vset(vs,repr)) == 1

        termsCombs = Combinations(ts,2)
        ieqs = []
        for t1,t2 in termsCombs:
            vs = Miscs.get_vars([t1,t2])
            if are_inputs(vs):
                if self.verbose >= 1:
                    print '* skip input terms({},{})'.format(t1,t2)
                continue

            if are_self(vs):
                if self.verbose >= 1:
                    print '* skip self terms({},{})'.format(t1,t2)
                continue


            ieqs = ieqs + \
                self.gen_oct_ieqs(t1,t2,self.tcs1,verbose=self.verbose)

        
        self.sols = ieqs


    def refine(self):
        super(IeqOct,self).refine()            

        rf = Refine(ps=self.sols, verbose=self.verbose)
        rf.rrank()
        rf.rfilter(tcs=self.tcs2)
        rf.rinfer()         
        self.sols = rf.ps


    ##### Helpers for IeqOct #####

    @staticmethod
    def gen_oct_ieqs(t1,t2,tcs,verbose):
        """
        t1, t2:  terms (e.g., t1=x,t2=y, t1=v^2, t1 = w*z)
        tcs: test cases

        Generate octagonal contraints over t1,t2 of the form
        L1 <= t1 <= U1  
        L2 <= t2 <= U2
        L3 <= t1 - t2 <= U3
        L4 <= t1 + t2 <= U4

        The algorithm takes linear time in |tcs|
        """

        if __debug__:
            assert isinstance(t1,Miscs.sage_expr) and \
                isinstance(t2,Miscs.sage_expr)
            assert isinstance(tcs,list) #more precisely, list of dictionaries

        
        t1s = [t1(tc) for tc in tcs]
        t2s = [t2(tc) for tc in tcs]

        L1 = min(t1s)
        U1 = max(t1s)

        L2 = min(t2s)
        U2 = max(t2s)

        t1_minus_t2 = [(t1_ - t2_) for t1_,t2_ in zip(t1s,t2s)]
        L3 = min(t1_minus_t2)
        U3 = max(t1_minus_t2)

        t1_plus_t2 = [(t1_ + t2_) for t1_,t2_ in zip(t1s,t2s)]
        L4 = min(t1_plus_t2)
        U4 = max(t1_plus_t2)

        oct_ieqs = [L1 <= t1, t1 <= U1,
                    L2 <= t2, t2 <= U2,
                    L3 <= t1 - t2, t1 - t2 <= U3,
                    L4 <= t1 + t2, t1 + t2 <= U4]

        return oct_ieqs





# def make_binary(N,seed = [[]]):
#     if len(seed[0]) == N:
#         return seed
#     else:
#         return make_binary(N,map(lambda s: s + [0],seed)) + \
    #             make_binary(N,map(lambda s: s + [1],seed))


    
# def mine_inequalities0(t1, t2, tcs, verbose=True):
#     """
#     invariant form c1*t2 <= t1 <= c2*t2 
#     where c and d are an integer.
#     """
#     try:
#         rs = C.vuniq([(t1/t2)(t) for t in tcs])
#         return [min(rs)*t2 <= t1, t1 <= max(rs)*t2]
#     except RuntimeError:  #e.g., div by 0
#         return []


# def mine_inequalities1(t1, t2, tcs, verbose=True):
#     """
#     invariant form c <= +- t1 +- t2 <= d 
#     where c and d are an integer.
#     """
#     cs = [-1,0,1]
#     fs = [(c1,c2) for c1 in cs for c2 in cs]
#     fs_ = [(c1*t1 + c2*t2) for c1,c2 in fs if c1 != 0 or c2 !=0]

#     rs = [(f,C.vuniq([f(t) for t in tcs])) for f in fs_]
#     rs = [(min(r) <= f, f <= max(r)) for (f,r) in rs]
#     return rs


#     if len(t_v)==2 and mine_inv: #try mine_invariant detections first since it's quicker
#         rs1 = mine_inequalities0(t_v[0],t_v[1],tcs,verbose)
#         rs2 = mine_inequalities1(t_v[0],t_v[1],tcs,verbose)
#         rs = C.flatten([rs1,rs2])
#         return rs, None

#     else: 






# def mine_inequalities1(t1, t2, tcs, verbose=True):
#     """
#     invariant form c <= +- t1 +- t2 <= d 
#     where c and d are an integer.
#     """
#     cs = [3,-2,-1,0,1,2,3]
#     fs = [(c1,c2) for c1 in cs for c2 in cs]
#     fs_ = [(c1*t1 + c2*t2) for c1,c2 in fs if c1 != 0 or c2 !=0]

#     rs = [(f,C.vuniq([f(t) for t in tcs])) for f in fs_]
#     rs = [(min(r) <= f, f <= max(r)) for (f,r) in rs]
#     return rs


#     if len(t_v)==2 and mine_inv: #try mine_invariant detections first since it's quicker
#         rs1 = mine_inequalities0(t_v[0],t_v[1],tcs,verbose)
#         rs2 = mine_inequalities1(t_v[0],t_v[1],tcs,verbose)
#         rs = C.flatten([rs1,rs2])
#         return rs, None

#     else: 





    # #testing rand_pts_infer
    # if infer_f_rs == True:
    #     if rand_pts_infer(xclude_p,[p]) == False:
    #         print 'E: rand_pts_infer is False instead of True'
    #         print 'ps1: ', xclude_p
    #         print 'ps2: ', [p]
    #     else:
    #         print 'rand_pts_infer ++'


    
# def mine_inequalities0(t1, t2, tcs, verbose=True):
#     """
#     invariant form c1*t2 <= t1 <= c2*t2 
#     where c and d are an integer.
#     """
#     try:
#         rs = C.vuniq([(t1/t2)(t) for t in tcs])
#         return [min(rs)*t2 <= t1, t1 <= max(rs)*t2]
#     except RuntimeError:  #e.g., div by 0
#         return []



