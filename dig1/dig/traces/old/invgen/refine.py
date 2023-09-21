import vu_common as CM
from miscs import Miscs

from iexp import IExp
from smt_z3py import SMT_Z3

import z3

from sage.all import *


class Refine(object):
    """
    Refine result invariants using several techniques, including 

    1) filtering
    2) inferring
    3) ranking
    """

    def __init__(self,ps,verbose=1):
        self.ps = ps
        self._verbose = verbose


    def get_ps(self): return self._ps
    def set_ps(self,ps): 
        if __debug__:
            assert all(isinstance(p,IExp) for p in ps)
        self._ps = ps

    ps = property(get_ps,set_ps)

    @property
    def verbose(self): return self._verbose

    def rrank(self):
        """
        Remove unlikely properties using simple heuristic
        """

        if CM.is_none_or_empty(self.ps) or len(self.ps) == 1:
            if self.verbose >= 1:
                print '* rrank skips'
            return

        ### Begin ranking ###

        if self.verbose >= 1:
            print('* rrank(|ps|={})'.format(len(self.ps)))

        ps = CM.vset(self.ps)

        keep_ps = [p for p in ps if p.get_score() <= 100]
        
        if self.verbose >= 1:
            print "rrank (before %d, after %d, diff %d)" \
                %(len(ps), len(keep_ps), len(ps) - len(keep_ps))

        self.ps = keep_ps



    def rfilter(self, tcs):
        """
        Returns the subset of ps that satisfies all testcases tcs
        
        EXAMPLES:

        sage: var('y z')
        (y, z)

        sage: rf = Refine(map(IExp,[x^2 >= 0 , x-y >= 7]),verbose=0);rf.rfilter([{x:1,y:0}]);  sorted(rf.ps,key=str)
        [x^2 >= 0]

        sage: rf = Refine(map(IExp,[2*x -y >= 0]),verbose=0); rf.rfilter([{y: 14, x: 7}, {y: 13, x: 7}, {y: 6, x: 4}, {y: 1, x: 1}, {y: 2, x: 1}, {y: 5, x: 100}]); sorted(rf.ps,key=str)
        [2*x - y >= 0]

        sage: rf = Refine(map(IExp,[2*x -y >= 0]),verbose=0); rf.rfilter([{y: 14, x: 7}, {y: 13, x: 7}, {y: 6, x: 4}, {y: 1, x: 1},{y: 2, x: 1}, {y: 25, x: 9}, {y:25 , x*y: 15, x: 9}]); sorted(rf.ps,key=str)
        []

        ** This is by design
        sage: rf = Refine(map(IExp,[x^3 >= 0 , x-y >= 7]),verbose=0); rf.rfilter([{z:1}])
        sage: rf.ps == []
        True

        
        sage: rf = Refine(map(IExp,['lambda x: x>=10', 'lambda x,y: max(x,y)>12', 'lambda x: x>=10'])); rf.rfilter([{'x':20,'y':0},{'x':9,'y':13}]); sorted(rf.ps,key=str)
        * rfilter(|ps|=3,|tcs|=2)
        rfilter (before 2, after 1, diff 1)
        ['lambda x,y: max(x,y)>12']

        
        sage: rf = Refine(map(IExp,['lambda x: x>=10', 'lambda x,y: max(x,y)>12']),verbose=1); rf.rfilter([{'x':20,'y':0}]); sorted(rf.ps,key=str)
        * rfilter(|ps|=2,|tcs|=1)
        rfilter (before 2, after 2, diff 0)
        ['lambda x,y: max(x,y)>12', 'lambda x: x>=10']


        sage: rf = Refine(map(IExp,['lambda x: x>=10', 'lambda x,y: max(x,y)>12'])); rf.rfilter([]); sorted(rf.ps,key=str)
        * rfilter skips
        ['lambda x,y: max(x,y)>12', 'lambda x: x>=10']

        """


        if CM.is_none_or_empty(self.ps) or CM.is_none_or_empty(tcs):
            if self.verbose >= 1:
                print '* rfilter skips'
            return

        ### Begin filtering ###
        
        if self.verbose >= 1:
            print('* rfilter(|ps|=%d,|tcs|=%d)'%(len(self.ps), len(tcs)))

        ps = CM.vset(self.ps)

        keep_ps = []
        for p in ps:
            #didn't use cached() since it actually is slower
            if all(p._eval(tc) for tc in tcs):
                keep_ps.append(p)
                if self.verbose >= 3: print '-> keep ', p
            else:
                if self.verbose >= 2: print '-> remove ', p

        if self.verbose >= 1:
            print "rfilter (before %d, after %d, diff %d)" \
                %(len(ps), len(keep_ps), len(ps) - len(keep_ps))

        self.ps = keep_ps


    def rinfer(self):
        """
        Return a (preferably minimal) subset of ps that 
        infers all properties in ps.
        
        sage: var('a s t y')
        (a, s, t, y)

        sage: rf = Refine(map(IExp,[a*a - s + t == 0, t*t - 4*s + 2*t + 1 == 0,a*s - 1/2*s*t + 1/2*s == 0,  a*x - 1/2*x*t + 1/2*x == 0,a - 1/2*t + 1/2 == 0, a*t - 2*s + 3/2*t + 1/2 == 0]),verbose=1); rf.rinfer()
        * rinfer(|ps|=6)
        rinfer (before 6, after 2, diff 4)
        sage: assert \
        set([p.inv for p in rf.ps]) == set([a - 1/2*t + 1/2 == 0, t^2 - 4*s + 2*t + 1 == 0]) or \
        set([p.inv for p in rf.ps]) == set([a - 1/2*t + 1/2 == 0, a^2 - s + t == 0])


        sage: rf = Refine(map(IExp,[x-7>=0, x + y -2>=0, y+5 >= 0, -7 + x >= 0]),verbose=2); rf.rinfer(); sorted(rf.ps,key=str)
        * rinfer(|ps|=4)
        rinfer (before 3, after 2, diff 1)
        [x - 7 >= 0, y + 5 >= 0]


        sage: rf = Refine(map(IExp,[x+y==0]),verbose=1); rf.rinfer(); sorted(rf.ps,key=str)
        * rinfer skips
        [x + y == 0]
        """
        if CM.is_none_or_empty(self.ps) or len(self.ps) == 1:
            if self.verbose >= 1:
                print '* rinfer skips'
            return

        ### Begin inference ###

        if self.verbose >= 1:
            print('* rinfer(|ps|={})'.format(len(self.ps)))
        
        #Extract the expression part. It's simpler that way.
        ps = [p.inv for p in self.ps]

        assert all(isinstance(p, Miscs.sage_expr) for p in ps),\
            'cannot perform inferrence on this type of inv'
        
        ps = CM.vset(ps)

        keep_ps = Refine.rinfer_helper(ps,verbose=self.verbose)
        

        if self.verbose >= 1:
            print("rinfer (before %d, after %d, diff %d)"
                  %(len(ps), len(keep_ps), len(ps) - len(keep_ps)))

        #Convert back to IExp
        self.ps = map(IExp,keep_ps)



    ##### Helpers for Refine ###

    @staticmethod
    def rinfer_helper(ps,verbose=1):
        """
        Removes weak properties (e.g., remove q if p => q)
        
        EXAMPLES:

        sage: var('y a s t z b q d k x1')
        (y, a, s, t, z, b, q, d, k, x1)

        sage: Refine.rinfer_helper([x*x-y*y==0,x-y==0,x*x-y*y==0,2*x*y-2*y*y==0],verbose=0)
        [x - y == 0]


        #several possible (but should be equiv) solutions
        sage: Refine.rinfer_helper([a*a - s + t == 0, t*t - 4*s + 2*t + 1 == 0,a*s - 1/2*s*t + 1/2*s == 0,  a*x - 1/2*x*t + 1/2*x == 0,a - 1/2*t + 1/2 == 0, a*t - 2*s + 3/2*t + 1/2 == 0],verbose=0)
        [a^2 - s + t == 0, a - 1/2*t + 1/2 == 0]
        
        alt solutions:
        [-2*a + t - 1 == 0, a^2 + 2*a - s + 1 == 0]
        [-1/4*t^2 + s - 1/2*t - 1/4 == 0, a - 1/2*t + 1/2 == 0]
        [t^2 - 4*s + 2*t + 1 == 0, a - 1/2*t + 1/2 == 0]


        sage: Refine.rinfer_helper([a*y - b == 0,a*z - a*x + b*q == 0,q*y + z - x == 0],verbose=0)
        [a*y - b == 0, q*y - x + z == 0]

        sage: Refine.rinfer_helper([x-7>=0, x + y -2>=0, y+5 >= 0],verbose=0)
        [x - 7 >= 0, y + 5 >= 0]

        sage: Refine.rinfer_helper([a*y-b==0,q*y+k-x==0,a*x-a*k-b*q==0],verbose=0)
        [a*y - b == 0, q*y + k - x == 0]

        sage: Refine.rinfer_helper([x-1>=0 , d*y - 6 >= 0, d - 1 >= 0, y - 6 >= 0, d*y - y >= 0, d*x - x >= 0, y*x - 6*x>=0 , y^2 - 36 >= 0, d^2 - 3*d + 2 >= 0, d^2 - 5*d + 6 >= 0 , d*y - 6*d - y + 6 >= 0],verbose=0)
        [x - 1 >= 0, d - 1 >= 0, y - 6 >= 0, d^2 - 3*d + 2 >= 0, d^2 - 5*d + 6 >= 0]

        Alt Sol:
        [d*x - x >= 0, d^2 - 3*d + 2 >= 0, d^2 - 5*d + 6 >= 0, x - 1 >= 0, x*y - 6*x >= 0]

        sage: Refine.rinfer_helper([x+x1==0,x-x1==1],verbose=0)
        [x + x1 == 0, x - x1 == 1]
        
        sage: Refine.rinfer_helper([x^2-1>=0,x-1>=0],verbose=0)
        [x - 1 >= 0]

        """

        #Use the precise but expensive method when |ps| is small
        #otherwise, use the greedy method
        if len(ps) <= 10:
            ps_ = Refine.min_indep_set(ps,verbose=verbose)
        else: 
            ps_ = Refine.reduce_smt(ps,verbose=verbose)

        return ps_



    @staticmethod
    def reduce_eqts(ps,verbose=1):
        """
        DEPRECATE, use SMT directly.

        Return a minimal subset ps' of ps that infers ps. 
        The input set ps must contains equations only. 
        The method uses Groebner basis

        EXAMPLES:
        
        sage: var('a y b q k')
        (a, y, b, q, k)

        sage: rs =  Refine.reduce_eqts([a*y-b==0,q*y+k-x==0,a*x-a*k-b*q==0])
        sage: assert set(rs) == set([a*y - b == 0, q*y + k - x == 0])

        sage: rs =  Refine.reduce_eqts([x*y==6,y==2,x==3])
        sage: assert set(rs) == set([x - 3 == 0, y - 2 == 0])
        
        #Attribute error occurs when only 1 var, thus return as is
        sage: rs =  Refine.reduce_eqts([x*x==4,x==2])
        sage: assert set(rs) == set([x == 2, x^2 == 4])
        
        
        """
        assert all(p.operator() == operator.eq for p in ps)

        vs = Miscs.get_vars(ps)
        try:
            Q = PolynomialRing(QQ,vs)
            I = Q*ps
            #ps_ = I.radical().groebner_basis()
            ps = I.radical().interreduced_basis()
            ps = [(SR(p)==0) for p in ps]
        except AttributeError:
            pass

        return ps


    @staticmethod
    def reduce_smt(ps, verbose=1):
        """
        Return a minimum subset ps' of ps that infers ps
        such that ps' implies all p in ps.

        Use a greedy method to remove redundant properties. 
        Thus it's quick, but not necessary exact.


        EXAMPLES: 

        sage: var('a y b q k s t z')
        (a, y, b, q, k, s, t, z)

        sage: Refine.reduce_smt([a*y-b==0,q*y+k-x==0,a*x-a*k-b*q==0])
        [q*y + k - x == 0, a*y - b == 0]

        sage: Refine.reduce_smt([a*y-b==0,a*z-a*x+b*q==0,q*y+z-x==0])
        [q*y - x + z == 0, a*y - b == 0]

        sage: Refine.reduce_smt([x-7>=0, x + y -2>=0, y+5 >= 0])
        [x - 7 >= 0, y + 5 >= 0]

        sage: Refine.reduce_smt([x+y==0,x-y==1])
        [x + y == 0, x - y == 1]

        sage: Refine.reduce_smt([x^2-1>=0,x-1>=0])
        [x - 1 >= 0]


        sage: Refine.reduce_smt([a*a - s + t == 0, t*t - 4*s + 2*t + 1 == 0,a*s - 1/2*s*t + 1/2*s == 0,  a*x - 1/2*x*t + 1/2*x == 0,a - 1/2*t + 1/2 == 0, a*t - 2*s + 3/2*t + 1/2 == 0])
        [t^2 - 4*s + 2*t + 1 == 0, a - 1/2*t + 1/2 == 0]

        sage: Refine.reduce_smt([x*x-y*y==0,x-y==0,x*x-y*y==0,2*x*y-2*y*y==0]) 
        [x - y == 0]

        sage: Refine.reduce_smt([x-1>=0 , t*y - 6 >= 0, t - 1 >= 0, y - 6 >= 0, t*y - y >= 0, t*x - x >= 0, y*x - 6*x>=0 , y^2 - 36 >= 0, t^2 - 3*t + 2 >= 0, t^2 - 5*t + 6 >= 0 , t*y - 6*t - y + 6 >= 0])
        [x - 1 >= 0, t - 1 >= 0, y - 6 >= 0, t^2 - 3*t + 2 >= 0, t^2 - 5*t + 6 >= 0]


        sage: Refine.reduce_smt([x*y==6, y-2==0, x-3==0])
        [y - 2 == 0, x - 3 == 0]

        sage: Refine.reduce_smt([x*x==4,x==2])
        [x == 2]
        sage: Refine.reduce_smt([x==2,x*x==4])
        [x == 2]
        sage: Refine.reduce_smt([x==2,x*x==4,x==-2])
        [x == 2, x == -2]
        sage: Refine.reduce_smt([x==2,x==-2,x*x==4])
        [x == 2, x == -2]
        sage: Refine.reduce_smt([x*x==4,x==2,x==-2])
        [x == 2, x == -2]
        """

        
        
        #Remove "longer" property first (i.e. those with more variables)
        ps = sorted(ps, reverse=True, key=lambda p: len(Miscs.get_vars(p)))

        rs = list(ps) #make a copy
        for p in ps:
            if p in rs:
                #note, the use of set makes things in non order
                xclude_p = CM.vsetdiff(rs,[p])

                if SMT_Z3.imply(xclude_p,p):
                    rs = xclude_p
                    if verbose >= 2:
                        print '---> remove %s'%p
                else:
                    if verbose >= 3:
                        print '--> keep %s'%p

                        
        #assert CM.vall(ps, lambda p: SMT_Z3.imply(rs,p)) , slow
            
        return rs

    @staticmethod
    def min_indep_set(ps,verbose=1):
        """
        Return a minimum subset ps' of ps that infers ps
        such that ps' implies all p in ps.

        This algorithm is exact, but *expensive*,  O(2^|ps|)

        EXAMPLES: 

        sage: var('a y b q k s t d z')
        (a, y, b, q, k, s, t, d, z)


        sage: Refine.min_indep_set([x*y==6, y-2==0, x-3==0])
        [x*y == 6, y - 2 == 0]
        sage: Refine.min_indep_set([x*x-y*y==0,x-y==0,x*x-y*y==0,2*x*y-2*y*y==0]) 
        [x - y == 0]

        sage: Refine.min_indep_set([a*a - s + t == 0, t*t - 4*s + 2*t + 1 == 0,a*s - 1/2*s*t + 1/2*s == 0,  a*x - 1/2*x*t + 1/2*x == 0,a - 1/2*t + 1/2 == 0, a*t - 2*s + 3/2*t + 1/2 == 0])
        [a^2 - s + t == 0, a - 1/2*t + 1/2 == 0]

        #[-2*a + t - 1 == 0, a^2 + 2*a - s + 1 == 0]
        #[-1/4*t^2 + s - 1/2*t - 1/4 == 0, a - 1/2*t + 1/2 == 0]
        #[t^2 - 4*s + 2*t + 1 == 0, a - 1/2*t + 1/2 == 0]
        #[a^2 - s + t == 0, a - 1/2*t + 1/2 == 0]


        sage: Refine.min_indep_set([a*y - b == 0,a*z - a*x + b*q == 0,q*y - x + z== 0])
        [a*y - b == 0, q*y - x + z == 0]

        sage: Refine.min_indep_set([x-7>=0, x + y -2>=0, y+5 >= 0])
        [x - 7 >= 0, y + 5 >= 0]

        sage: Refine.min_indep_set([x-1>=0 , d*y - 6 >= 0, d - 1 >= 0, y - 6 >= 0, d*y - y >= 0, d*x - x >= 0, y*x - 6*x>=0 , y^2 - 36 >= 0, d^2 - 3*d + 2 >= 0, d^2 - 5*d + 6 >= 0 , d*y - 6*d - y + 6 >= 0])
        [x - 1 >= 0, d - 1 >= 0, y - 6 >= 0, d^2 - 3*d + 2 >= 0, d^2 - 5*d + 6 >= 0]
        
        Alt sol:
        [d*x - x >= 0, d^2 - 3*d + 2 >= 0, d^2 - 5*d + 6 >= 0, x - 1 >= 0, x*y - 6*x >= 0]

        sage: Refine.min_indep_set([x+y==0,x-y==1])
        [x + y == 0, x - y == 1]
        
        sage: Refine.min_indep_set([x^2-1>=0,x-1>=0])
        [x - 1 >= 0]

        sage: Refine.min_indep_set([x*x==4,x==2])
        [x == 2]
        sage: Refine.min_indep_set([x==2,x*x==4])
        [x == 2]
        sage: Refine.min_indep_set([x==2,x*x==4,x==-2])
        [x == 2, x == -2]
        sage: Refine.min_indep_set([x==2,x==-2,x*x==4])
        [x == 2, x == -2]
        sage: Refine.min_indep_set([x*x==4,x==2,x==-2])
        [x == 2, x == -2]



        """

        for k in srange(1,len(ps)):
            cbs = Combinations(ps,k)
            for cb in cbs:
                cb_diff = CM.vsetdiff(ps,cb)
                if SMT_Z3.imply(cb,cb_diff):
                    return cb

        return ps



