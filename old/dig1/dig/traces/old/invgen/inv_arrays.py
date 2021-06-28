import vu_common as CM
from miscs import Miscs, Tree, AEXP

from refine import Refine

#import z3
#from smt_z3py import SMT_Z3

from invgen import Inv

from sage.all import *

class SimpleArray(Inv):
    """
    Find Simple Array Invariants of the form 
    c1A[i][j].. + c2B[i1'][i2'].. = 0

    EXAMPLES

    ig = InvGen("Traces/AES/Simple/paper_multidim.tc",verbose=1)
    _ =  ig.getInvs(inv_typ='simple',seed=1)
    *** InvGen ***
    Sun Jun  3 21:44:39 2012
    Sage Version 5.0, Release Date: 2012-05-14
    Godel.local Darwin 10.8.0 x86_64
    *** ReadFile ***
    read 'Traces_ICSE2012/AES/Simple/paper_multidim.tc'
    number of traces (tcs) read: 9
    read 'Traces_ICSE2012/AES/Simple/paper_multidim.ext'
    0. |_tcs|: 9
    1. |_tcs2|: 0
    2. _vs: [A, B]
    3. _xinfo: 
    0. All: ['A', 'B']
    1. Assume: []
    2. Const: []
    3. Expect: ['A[i] - 7B[2i] - 3i == 0']
    4. ExtFun: []
    5. Global: []
    6. Input: []
    7. Output: []
    Time elapsed: 0.0408 s (ReadFile)
    seed 1 (test 0.829402 0.595912 0.429361)
    *** SimpleArray ***
    Create new trace format (treating array elems as seperate vars)
    Find linear equalities over 8 array elements
    sample_traces: chose |tcs1|=9, |tcs2|=0 (attempted 14/9 tcs)
    Time elapsed: 0.0000 s (function sample_traces)
    *** Eqt ***
    Create equations from 9 data
    * EQ: Solve 9 (uniq) eqts for 9 unknowns coeffs
    Time elapsed: 0.0287 s (solve)
    Refine 3 candidate invariants
    * rfilter skips
    * rinfer(|ps|=3)
    rinfer (before 3, after 3, diff 0)
    Time elapsed: 0.0492 s (refine)
    Detected Invariants for Eqt:
    0: A_0 - 7*B_0 == 0
    1: A_2 - 7*B_4 - 6 == 0
    2: -1/7*A_1 + B_2 + 3/7 == 0
    Some rels were modifed
    A_2 - 7*B_4 - 6 == 0
    A_0 - 7*B_0 == 0
    A_1 - 7*B_2 - 3 == 0
    Find rels over indices
    a_solve: Assume 'A' is pivot
    solve 'B' with respect to pivot with |tcs|=3
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    a_solve: Assume 'A' is pivot
    solve 'coef' with respect to pivot with |tcs|=3
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    Result (pivot A): lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0
    a_solve: Assume 'B' is pivot
    solve 'A' with respect to pivot with |tcs|=3
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    a_solve: Assume 'B' is pivot
    solve 'coef' with respect to pivot with |tcs|=3
    Create equations from 3 data
    * EQ: Solve 3 (uniq) eqts for 2 unknowns coeffs
    Result (pivot B): lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0
    Detected Invariants for SimpleArray:
    0: ('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 1}])
    1: ('lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0', [{'B0': 4}, {'B0': 0}, {'B0': 2}])
    Time elapsed: 0.1462 s (solve)
    Refine 2 candidate invariants
    * rfilter(|ps|=2,|tcs|=9)
    rfilter (before 2, after 2, diff 0)
    Time elapsed: 0.0051 s (refine)
    Detected Invariants for SimpleArray:
    0: ('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 1}])
    1: ('lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0', [{'B0': 4}, {'B0': 0}, {'B0': 2}])
    
    """
    
    def __init__(self,terms,tcs1,tcs2,xinfo,verbose):
 
        super(SimpleArray,self).__init__(
            terms  = terms,  #not important
            tcs1   = tcs1,
            tcs2   = Miscs.keys_to_str(tcs2), #for refinement
            xinfo  = xinfo,
            verbose= verbose)


        
    def solve(self): #simple
        print 'Create new trace format (treating array elems as seperate vars)'
        aInfo = {}  #{A_0_0=[0,0],B_1_2_3=[1,2,3]}
        
        tcs = [SimpleArray.genTracesE2V(t,aInfo=aInfo,verbose=self.verbose)
               for t in self.tcs1]

        aeterms = aInfo.keys()
        assert set(map(str,aeterms)) == set(map(str,tcs[0].keys()))
        
        print 'Find linear equalities over %d array elements'%len(aeterms)
        aeterms = [SR(1)] + aeterms 
        tcs1,tcs2 = Miscs.get_sample(tcs     = tcs,
                                     tcsN    = len(aeterms),
                                     sampleP = 150,
                                     min_    = None,
                                     verbose = self.verbose)

        from inv_polynomials import Eqt
        solverE = Eqt(terms   = aeterms,
                      tcs1    = tcs1,
                      tcs2    = tcs2,
                      xinfo   = self.xinfo,
                      verbose = self.verbose)
        solverE.go()
        ps = [s.inv for s in solverE.sols]

        #modify/reformat results if necessary
        psOld = set(map(str,ps))
        ps = SimpleArray.filterDupArrs(ps,aInfo=aInfo,verbose=self.verbose)
        ps = [Miscs.elim_denom(p) for p in ps] #Eliminating denominators if exist
        ps = SimpleArray.modifySigns(ps,verbose=self.verbose)

        if ps == []:
            self.set_sols([])
            return

        if set(map(str,ps)) != psOld:
            print 'Some rels were modifed'
            print '\n'.join(map(str,ps))

        ###
        print "Find rels over indices"
        psInfo = [SimpleArray.parseP(p,aInfo,verbose=self.verbose) for p in ps]
        sols = SimpleArray.findRels(psInfo,verbose=self.verbose)
        
        if CM.is_none_or_empty(sols):
            sols = ps
            self.do_refine = False
            
        self.set_sols(sols)
        self.print_sols()


    def refine(self):
        super(SimpleArray,self).refine()
            
        rf = Refine(ps=self.sols,verbose=self.verbose)
        rf.rrank()
        rf.rfilter(tcs=self.tcs2)

        self.set_sols(rf.ps)
        
    #######

    @staticmethod
    def genTracesE2V(d,aInfo,verbose):
        """
        Convert array elements into new variables

        
        EXAMPLES:

        sage: aInfo = {}
        
        sage: dsVals = SimpleArray.genTracesE2V({'A':[['a','b'],['c','d'],['e','f',['z','w']]],'B':[1,2,[7,8]],'C':[100]},aInfo,verbose=1)

        sage: sorted(dsVals.items(),key=lambda (x,_) : str(x))
        [(A_0_0, 'a'), (A_0_1, 'b'), (A_1_0, 'c'), (A_1_1, 'd'), (A_2_0, 'e'), (A_2_1, 'f'), (A_2_2_0, 'z'), (A_2_2_1, 'w'), (B_0, 1), (B_1, 2), (B_2_0, 7), (B_2_1, 8), (C_0, 100)]

        sage: aInfo.items()
        [(A_1_0, {'idx_': [(A0, 1), (A1, 0)], 'name': 'A'}), (B_0, {'idx_': [(B0, 0)], 'name': 'B'}), (A_2_1, {'idx_': [(A0, 2), (A1, 1)], 'name': 'A'}), (B_2_1, {'idx_': [(B0, 2), (B1, 1)], 'name': 'B'}), (A_0_1, {'idx_': [(A0, 0), (A1, 1)], 'name': 'A'}), (A_2_0, {'idx_': [(A0, 2), (A1, 0)], 'name': 'A'}), (B_2_0, {'idx_': [(B0, 2), (B1, 0)], 'name': 'B'}), (A_0_0, {'idx_': [(A0, 0), (A1, 0)], 'name': 'A'}), (A_2_2_1, {'idx_': [(A0, 2), (A1, 2), (A2, 1)], 'name': 'A'}), (C_0, {'idx_': [(C0, 0)], 'name': 'C'}), (A_1_1, {'idx_': [(A0, 1), (A1, 1)], 'name': 'A'}), (B_1, {'idx_': [(B0, 1)], 'name': 'B'}), (A_2_2_0, {'idx_': [(A0, 2), (A1, 2), (A2, 0)], 'name': 'A'})]

        #[(B_2_0, {'idx_': [(B0, 2), (B1, 0)], 'name': 'B'}), (A_0_0, {'idx_': [(A0, 0), (A1, 0)], 'name': 'A'}), (A_2_2_1, {'idx_': [(A0, 2), (A1, 2), (A2, 1)], 'name': 'A'}), (C_0, {'idx_': [(C0, 0)], 'name': 'C'}), (A_1_1, {'idx_': [(A0, 1), (A1, 1)], 'name': 'A'}), (B_1, {'idx_': [(B0, 1)], 'name': 'B'}), (A_2_2_0, {'idx_': [(A0, 2), (A1, 2), (A2, 0)], 'name': 'A'}), (A_1_0, {'idx_': [(A0, 1), (A1, 0)], 'name': 'A'}), (B_0, {'idx_': [(B0, 0)], 'name': 'B'}), (A_2_1, {'idx_': [(A0, 2), (A1, 1)], 'name': 'A'}), (B_2_1, {'idx_': [(B0, 2), (B1, 1)], 'name': 'B'}), (A_0_1, {'idx_': [(A0, 0), (A1, 1)], 'name': 'A'}), (A_2_0, {'idx_': [(A0, 2), (A1, 0)], 'name': 'A'})]


        """

        def extractValsIdxs(arrName,arrContents,aInfo,verbose=1):
            vi = Miscs.travel(arrContents,verbose)
            vals = Miscs.getVals(vi,verbose)
            idxs = Miscs.getIdxs(vi,verbose)
            aName = str(arrName)
            newVars = [var(aName + '_' + '_'.join(map(str,idx))) for idx in idxs]

            dVals = dict(zip(newVars,vals)) #{A_0_0_1:'w'}

            for nv,idx in zip(newVars,idxs):
                if nv not in aInfo:
                    idx_ = zip([var('%s%s'%(aName,li))
                                 for li in srange(len(idx))],idx)
                    aInfo[nv]={'name':aName,'idx_':idx_}

            return dVals
                       

        ds = [extractValsIdxs(k,v,aInfo,verbose) for k,v in d.items()]
        dsVals = CM.merge_dict(ds)
        return dsVals

    @staticmethod
    def filterDupArrs(ps,aInfo,verbose=1):
        """
        remove relations that involve elements from same arrays

        EXAMPLES:

        sage: var('x_0 x_1 y_0 y_1')
        (x_0, x_1, y_0, y_1)

        sage: SimpleArray.filterDupArrs([x_0 + x_1 == 0, x_1 + y_1 == 0, x_0+y_1+y_0==0, x_0+x_1-2==0],{x_0:{'name':'x','idxs':[0]},x_1:{'name':'x','idxs':[1]},y_0:{'name':'y','idxs':[0]},y_1:{'name':'y','idxs':[1]}},verbose=0)
        [x_1 + y_1 == 0]
        """
        
        getArrNames = lambda p: \
            [aInfo[v]['name'] for v in Miscs.get_vars(p,verbose)]
        
        ps = [p for p in ps if CM.vall_uniq(getArrNames(p))]
              
        return ps

    @staticmethod
    def modifySigns(ps,verbose=1):
        """
        convert equations so that they have same sign

        EXAMPLES:

        sage: var('y')
        y
        sage: SimpleArray.modifySigns([x-y==0,-2*x + 2*y ==0])
        [x - y == 0, 2*x - 2*y == 0]

        sage: SimpleArray.modifySigns([-x-y==0,2*x+2*y==0])
        [-x - y == 0, -2*x - 2*y == 0]

        sage: SimpleArray.modifySigns([-x-y==0,2*x-2*y==0])
        [-x - y == 0, -2*x + 2*y == 0]
        """

        if len(ps) <= 1 : 
            return ps

        _getSign = lambda p: Miscs.get_coefs_terms(p)[0][0]

        p0_sign = _getSign(ps[0]) #sign of the coef of the 1st term of the 1st p
        ps_ = [p if _getSign(p) == p0_sign else -1*p for p in ps[1:]]

        return [ps[0]]+ps_

        
    @staticmethod
    def parseP(p,d,verbose=1):
        """
        # sage: var('A_1_4 B_2_11_8 C_20_5_0')
        # (A_1_4, B_2_11_8, C_20_5_0)

        # sage: d = SimpleArray.a_parse(-A_1_4 + 7/2*B_2_11_8 - 8*C_20_5_0 + 100 == 0)
        # sage: sorted(d.items())
        # [('A', {'_contents_': {A_i_1: 4, A_i_0: 1, A_coef: -1}}), ('B', {'_contents_': {B_coef: 7/2, B_i_2: 8, B_i_1: 11, B_i_0: 2}}), ('C', {'_contents_': {C_i_2: 0, C_i_1: 5, C_i_0: 20, C_coef: -8}}), ('COEF', {'_contents_': {COEF_coef: 100}})]
        # sage: var('A_4 B_11')
        # (A_4, B_11)
        # sage: d = SimpleArray.a_parse(1/7*A_4+B_11==0)
        # sage: sorted(d.items())
        # [('A', {'_contents_': {A_i_0: 4, A_coef: 1/7}}), ('B', {'_contents_': {B_coef: 1, B_i_0: 11}}), ('COEF', {'_contents_': {COEF_coef: 0}})]

        """
        coefs,ts = Miscs.get_coefs_terms(p)
        
        if 1 not in ts: #e.g., A_1 + B_2 == 0
            ts = ts + [1]
            coefs = coefs + [0]

        md = {}
        for c,t in zip(coefs,ts):

            contents=[(var('coef'),c)]
            if t == 1:
                name='coef'
            else:
                t=var(t)                
                name = d[t]['name']
                idx_ = d[t]['idx_']
                contents = contents + idx_

            md[name]=dict(contents)

        return md


    @staticmethod
    def findRels(psInfo,verbose=1):
        """
        #sage: var('rvu_2_1 t_9 rvu_2_3 t_11 rvu_2_0 t_8 rvu_3_2 t_14 rvu_0_0 t_0 rvu_0_2 t_2 rvu_3_1 t_13 rvu_3_3 t_15 rvu_0_1 t_1 rvu_0_3 t_3 rvu_1_3 t_7 rvu_1_0 t_4 rvu_1_2 t_6 rvu_3_0 t_12 rvu_1_1 t_5 rvu_2_2 t_10')
        (rvu_2_1, t_9, rvu_2_3, t_11, rvu_2_0, t_8, rvu_3_2, t_14, rvu_0_0, t_0, rvu_0_2, t_2, rvu_3_1, t_13, rvu_3_3, t_15, rvu_0_1, t_1, rvu_0_3, t_3, rvu_1_3, t_7, rvu_1_0, t_4, rvu_1_2, t_6, rvu_3_0, t_12, rvu_1_1, t_5, rvu_2_2, t_10)

        #sage: SimpleArray.findRels(ps=[-rvu_2_1 + t_9 == 0, rvu_2_3 - t_11 == 0, rvu_2_0 - t_8 == 0, -rvu_3_2 + t_14 == 0, -rvu_0_0 + t_0 == 0, rvu_0_2 - t_2 == 0, -rvu_3_1 + t_13 == 0, rvu_3_3 - t_15 == 0, rvu_0_1 - t_1 == 0, -rvu_0_3 + t_3 == 0, -rvu_1_3 + t_7 == 0, -rvu_1_0 + t_4 == 0, rvu_1_2 - t_6 == 0, -rvu_3_0 + t_12 == 0, rvu_1_1 - t_5 == 0, rvu_2_2 - t_10 == 0],verbose=0)
        """

        ks = psInfo[0]
        pivots = [k for k in ks if k != 'coef']

        rs = [SimpleArray.findRelsPivot(pivot,psInfo,verbose) for pivot in pivots]
        rs = [rs_ for rs_ in rs if rs_ is not None]

        return rs


       

    @staticmethod
    def findRelsPivot(pivot,psInfo,verbose=1):
        """
        Note: we want to choose an array A as pivot only when all elements of A has relations to elements in other arrays,
        e.g.,
        assume A has 4 elements, then we only choose A as pivot if it has the below relations
        
        A[0] = B[0]
        A[1] = B[10]
        A[2] = B[20]
        A[3] = B[30]

        A[4] = B[11]
        B[11] = B[40]
        
        """
        ks = psInfo[0]

        rs = [SimpleArray.a_solve(pivot,k,psInfo,verbose=verbose)
              for k in ks if k != pivot]

        if None in rs:
            return None

        #create template, e.g. lambda p,a,b,p1,p2 = p[p1][p2] - 7a[2p1] + 8p3
        arrs = [k for k in ks if k != 'coef' and k != pivot]
        arrs = [pivot] + arrs  #pivot array is the first one
        pivotIdxs = [str(k) for k in ks[pivot] if str(k) != 'coef']

        #e.g. pivotD = {'A0':A0, 'coef': 1}
        pivotD = dict([(str(k),(c if str(k) == 'coef' else k))
                        for k,c in ks[pivot].items()])

        rs = [(pivot,pivotD)] + rs
        terms = [SimpleArray.genTemplate(name,d,verbose) for name,d in rs]

        rel = ' + '.join([t for t in terms if t is not None])
        idxStr = ', '.join(arrs + pivotIdxs)
        
        rs = 'lambda %s: %s == 0'%(idxStr,rel)

        #extract the index info since this result only works for these indices
        idxInfo = SimpleArray.extractIdxInfo(pivot,psInfo,verbose=verbose)
        
        if verbose >= 1:
            print 'Result (pivot %s): %s'%(pivot,rs)
            
        return rs,idxInfo

    @staticmethod
    def extractIdxInfo(pivot,psInfo,verbose=1):
        ps = [p[pivot] for p in psInfo]
        ps = Miscs.keys_to_str([p for p in ps])
        ps = [dict([(k,c) for k,c in p.items() if k != 'coef'])
              for p in ps]
        return ps      
        

    @staticmethod
    def a_solve(pivot, solve_for, tcs, verbose=1):
        """
        pivot = 'A'
        solve_for_arr = 'B'


        0: A_0 - 7*B_0 == 0
        1: A_1 - 7*B_2 - 3 == 0
        2: A_2 - 7*B_4 - 6 == 0

        Hypothesizes
        B_coef = c0A_i0  + c1A_i1 + ... + cnA_in  + c(n+1)
        
        B_i0 = c0A_i0  + c1A_i1 + ... + cnA_in  + c(n+1)
        
        B_i1 = c0A_i0  + c1A_i1 + ... + cnA_in  + c(n+1)
        """

        
        if verbose >= 1:
            print "a_solve: Assume '%s' is pivot"%pivot
            print "solve '%s' with respect to pivot with |tcs|=%d"%(solve_for,len(tcs))


        _getIdxs = lambda a,d: [k for k in d[a] if not 'coef' in str(k)]

        
        mytcs = [dict(tc[pivot].items() + tc[solve_for].items()) for tc in tcs]
                 
        idxs_ = _getIdxs(pivot,tcs[0])
        pivot_idxs_n_const = [SR(1)] + idxs_
        solve_for_keys= tcs[0][solve_for].keys()


        rs_ = [(pivot_idxs_n_const,k,mytcs) for k in solve_for_keys]  #todo, wtf is this line for ?
        rs = [Miscs.solve_eqts_(ts=pivot_idxs_n_const,rv=k,ds=mytcs,verbose=verbose)
              for k in solve_for_keys]

        rs = Miscs.keys_to_str(rs)  #so that the keys are string

        try:
            sol = CM.merge_dict(rs)
            sol = (solve_for,sol)
            return sol
        except Exception:
            return None

        
    @staticmethod
    def genTemplate(name,d,verbose=1):
       
        if name == 'coef':
            assert(len(d.values())==1)
            coefVal = d.values()[0]
            template = None if coefVal == 0 else '(%s)'%str(coefVal)
        else:
            idxVals= ['[%s]'%d[name+str(idx)] for idx in srange(len(d)-1)]

            if d['coef'] == -1:
                coefStr = '-'
            elif d['coef'] == 1:
                coefStr = ''
            else:
                coefStr = str(d['coef']) + '*'

            template = '(%s%s%s)'%(coefStr,name,''.join(idxVals))

        return template
           
    
class NestedArray(Inv):
    """
    Find NestedArray Invariant of the form  A[i] = B[e] where e = e1 | C[e] 

    EXAMPLES:

    sage: from invgen import InvGen
    
    sage: ig = InvGen("Traces/AES/Nested/paper_nested.tc",verbose=1)
    *** InvGen ***
    ...
    *** ReadFile ***
    read 'Traces/AES/Nested/paper_nested.tc'
    number of traces (tcs) read: 1
    0. |_tcs|: 1
    1. |_tcs2|: 0
    2. _vs: [A, B, C]
    3. _xinfo: 
    0. All: ['A', 'B', 'C']
    ...

    sage: ig.verbose = 2
    sage: _ =  ig.getInvs(inv_typ='nested',seed=1)
    seed 1 (test 0.829402 0.595912 0.429361)
    sample_traces: chose |tcs1|=1, |tcs2|=0 (attempted 1/1 tcs)
    ...
    *** NestedArray ***
    0. All: ['A', 'B', 'C']
    1. Assume: []
    2. Const: []
    3. Expect: []
    4. ExtFun: []
    5. Global: []
    6. Input: []
    7. Output: []
    8. ZDims: 
    0. A: 1
    1. B: 1
    2. C: 1
    Generate Nestings
    * gen_aexps [A,C,B]: 2 expressions generated
    * Find valid nestings using reachability analysis
    0. A[i1] == B[C[(i1)_]] has 1 relation(s)
    lambda A,C,B,i1: A[i1] == B[C[2*i1 + 1]]
    1. A[i1] == B[(i1)_] has 1 relation(s)
    lambda A,B,i1: A[i1] == B[-2*i1 + 5]
    * Relations: 2
    ...
    Refine 2 candidate invariants
    * rfilter(|ps|=2,|tcs|=1)
    rfilter (before 2, after 2, diff 0)
    ...
    Detected Invariants for NestedArray:
    0: lambda A,B,i1: A[i1] == B[-2*i1 + 5]
    1: lambda A,C,B,i1: A[i1] == B[C[2*i1 + 1]]
    

    sage: ig = InvGen("Traces/AES/Nested/aes_addroundkey_vn.tc",verbose=1)
    *** InvGen ***
    ...
    *** ReadFile ***
    read 'Traces_ICSE2012/AES/Nested/aes_addroundkey_vn.tc'
    number of traces (tcs) read: 100
    read 'Traces_ICSE2012/AES/Nested/aes_addroundkey_vn.ext'
    0. |_tcs|: 100
    1. |_tcs2|: 0
    2. _vs: [r_, rk, st]
    3. _xinfo: 
    0. All: ['r_', 'rk', 'st']
    1. Assume: []
    2. Const: []
    3. Expect: ['r[i][j]= xor(st[i,j],rk[i,j])']
    4. ExtFun: ['xor']
    5. Global: []
    6. Input: ['st', 'rk']
    7. Output: ['r_']
    ...

    sage: _ =  ig.getInvs(inv_typ='nested',seed=1)
    seed 1 (test 0.829402 0.595912 0.429361)
    sample_traces: chose |tcs1|=1, |tcs2|=99 (attempted 1/100 tcs)
    ...
    *** NestedArray ***
    * gen_extfuns: ext funs ['xor']
    * getExtFunReps(['xor'],|avals|=32,doCartesianProd=False)
    * fun: xor, fvals 152, idxs 224
    0. All: ['r_', 'rk', 'st']
    1. Assume: []
    2. Const: []
    3. Expect: ['r[i][j]= xor(st[i,j],rk[i,j])']
    4. ExtFun: ['xor']
    5. Global: []
    6. Input: ['st', 'rk']
    7. Output: ['r_']
    8. ZDims: 
    0. r_: 2
    1. rk: 2
    2. st: 2
    3. xor: 2
    Generate array expressions (nestings)
    * gen_aexps [r_,xor,st,rk]: 1 expressions generated
    * Find valid nestings using reachability analysis
    0. r_[i1][i2] == xor(st[(i1,i2)_][(i1,i2)_],rk[(i1,i2)_][(i1,i2)_]) has 1 relation(s)
    lambda r_,rk,xor,st,i1,i2: r_[i1][i2] == xor(st[i1][i2],rk[i1][i2])
    * Relations: 1
    ...
    Refine 1 candidate invariants
    * rfilter(|ps|=1,|tcs|=100)
    rfilter (before 1, after 1, diff 0)
    ...
    Detected Invariants for NestedArray:
    0: lambda r_,rk,xor,st,i1,i2: r_[i1][i2] == xor(st[i1][i2],rk[i1][i2])

    
    na = NestedArray(terms=ig.vs,tcs1=[ig.tcs[0]],tcs2=ig.tcs[1:],xinfo=ig.xinfo,verbose=1)
    na.solve()

    
    #paper_nested.tc example
    sage: var('A B C')
    (A, B, C)
    sage: na = NestedArray(terms=None,tcs1=[{C: [8, 5, 6, 6, 2, 1, 4], B: [1, -3, 5, 1, 0, 7, 1], A: [7, 1, -3]}],tcs2=[],xinfo={'All': ['A', 'B', 'C'], 'Const': [], 'Assume': [], 'Global': [], 'Expect': [], 'ExtFun': [], 'Input': [], 'Output': []},verbose=1)
    *** NestedArray ***
    0. All: ['A', 'B', 'C']
    1. Assume: []
    2. Const: []
    3. Expect: []
    4. ExtFun: []
    5. Global: []
    6. Input: []
    7. Output: []
    8. ZDims: 
    0. A: 1
    1. B: 1
    2. C: 1


    sage: na = NestedArray(terms=None,tcs1=[{'R': [128, 127, 126, 125], 'N':[128]}],tcs2=[],xinfo={'All': ['R'], 'Const': [], 'Assume': [], 'Global': [], 'Expect': ['R[i]=sub(N,i)'], 'ExtFun': ['sub'], 'Input': [], 'Output': ['R']},verbose=1)
    *** NestedArray ***
    * gen_extfuns: 1 ext funs ['sub']
    * getExtFunReps(['sub'],|avals|=5)
    * fun: sub, fvals 15, idxs 25
    sage: na.go()
    Generate array expressions (nestings)* gen_aexps [R,sub,N]: 
    2 expressions generated
    * Find valid nestings using reachability analysis
    0. R[i1] == sub(N[(i1)_],(i1)_) has 1 relation(s)
    lambda R,sub,N,i1: R[i1] == sub(N[0],i1)
    1. R[i1] == sub((i1)_,(i1)_) has 1 relation(s)
    lambda R,sub,i1: R[i1] == sub(128,i1)
    * Relations: 2
    Time elapsed: 0.0424 s (solve)
    Refine 2 candidate invariants
    * rfilter skips
    Time elapsed: 0.0001 s (refine)
    Detected Invariants for NestedArray:
    0: lambda R,sub,N,i1: R[i1] == sub(N[0],i1)
    1: lambda R,sub,i1: R[i1] == sub(128,i1)
    
    """

    def __init__(self,terms,tcs1,tcs2,xinfo,verbose):
        
        super(NestedArray,self).__init__(
            terms   = [],                      # not important
            tcs1    = Miscs.keys_to_str(tcs1), # will be modified in preprocess
            tcs2    = Miscs.keys_to_str(tcs2), # for refinement
            xinfo   = xinfo,
            verbose = verbose)

        self.preprocess(xinfo) #add ext funs, generate nodes
        

    def solve(self): #nested arrays
        
        print "Generate array expressions (nestings)"
        aexps = AEXP.gen_aexps(nodes   = self.trees,
                               xinfo   = self.xinfo,
                               data    = self.tcs1[0],
                               verbose = self.verbose)
        
        print '* Find valid nestings using reachability analysis'
        smtResults = []
        for i,ae in Miscs.senumerate(aexps):
            if self.verbose >= 2:
                print '%d. '%i, ae.lt, ' = ', ae.rt
                
            sRes = ae.peelme(data=self.tcs1[0],verbose=self.verbose)

            if sRes is not None:

                smtResults = smtResults + sRes

                if self.verbose >= 1:
                    print '%d. %s has %d relation(s)'%(i,ae,len(sRes))
                    print '\n'.join(sRes)


        print '* Relations: %d'%(len(smtResults))

        self.set_sols(smtResults)


    def refine(self):
        super(NestedArray,self).refine()

        rf = Refine(ps=self.sols, verbose=self.verbose)
        #print self.tcs2
        

        rf.rfilter(tcs=self.tcs2)

        self.set_sols(rf.ps)

    ###### Helpers Function for Nested Array #####

    def preprocess(self,xinfo):
        """
        Preprocesses input data
        1) transforms external functions to special arrays
        1) change array repr to value->index repr to speed up 
        array index lookup
        2) generate nodes
        """
        
        assert isinstance(xinfo,dict)
        
        #add new extfun variables
        from miscs import ExtFun
        tcs1 = [ExtFun.gen_extfuns(tc=tc,xinfo=xinfo,verbose=self.verbose)
                for tc in self.tcs1]

        
        #add new representations to arrs
        tcs1 = [[(k,Miscs.getListIdxs(c) if isinstance(c,list) else c)
                for k,c in tc.items()]
               for tc in tcs1]
        tcs1 = [dict(tc) for tc in tcs1]
        self.tcs1 = tcs1
        
        from miscs import ExtFun
        self.trees = [Tree({'root':k, 
                            'children': [None] * len(c.values()[0][0]),
                            'commute': ExtFun(k).is_commute()})
                      for k,c in self.tcs1[0].items()]
        self.xinfo = xinfo
