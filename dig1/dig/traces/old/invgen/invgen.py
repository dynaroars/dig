import vu_common as CM
from miscs import Miscs, ReadFile
from sage.all import *


"""
Coding style:

Function:
Top level information:   * function_name info
Other information:  info


Todo:
traces might contain both scalar and arrays -- have to partition them
arrays might not have same dims or sizes -- have to filter them


120111:  each individual Inv class should return sols in array format

120112:  attempting to find Ieqs or Eqts after read in an array format screw things up
ig = InvGen('../invs/tcs2/nested/aes_word_xor_xor.tc',seed=0,verbose=1)
ig.getEqts(deg=2)

120114:
new data for knuth is totally f*cked up .. may be just use the old program to generate trace data. My bet is the book invs are corresponding to the old program -- not the new program (while True ...)

Simple array: some of the array invs are not right ...

Nested array:  some of the array invs are not right ...

"""



class Inv(object):
    """
    Base class that is inherited by all classes of Invariants
    """

    def __init__(self,terms,tcs1,tcs2,xinfo,verbose):

        if verbose >= 1:
            print('*** %s ***'%(self.__class__.__name__))
            # if verbose >= 2:
            #     print CM.dict2str(CM.get_arguments()[0],ignores=['self'],
            #                       print_size_only=['tcs1','tcs2','terms'])
                
        self._terms   = terms
        self._tcs1    = tcs1
        self._tcs2    = tcs2
        self._xinfo   = xinfo
        self._sols    = None
        self._verbose = verbose
        self._do_refine = True

        
    @property
    def terms(self): return self._terms

    def get_tcs1(self): return self._tcs1
    def set_tcs1(self,tcs1):
        if __debug__:
            assert isinstance(tcs1,list)
        self._tcs1 = tcs1

    tcs1 = property(get_tcs1,set_tcs1)

    @property
    def tcs2(self): return self._tcs2

    def get_xinfo(self): return self._xinfo
    def set_xinfo(self,xinfo): 
        if __debug__:
            assert isinstance(xinfo,dict)
        self._xinfo = xinfo
    xinfo=property(get_xinfo,set_xinfo)

    @property
    def do_refine(self): return self._do_refine

    def get_verbose(self): return self._verbose
    def set_verbose(self,v): 
        if __debug__:
            assert v >= 1
        self._verbose = v
    verbose = property(get_verbose,set_verbose)
    

    def get_sols(self): return self._sols
    def set_sols(self,sols):
        if __debug__:
            assert isinstance(sols,list), \
                'sols ({}) must be a list'.format(sols)

        from iexp import IExp
        self._sols = [s if isinstance(s,IExp) else IExp(s) for s in sols]

    sols = property(get_sols,set_sols)


    #Class methods
    def solve(self):
        """
        Base function for finding the invariants
        This function must be defined individually
        """
        pass

    def refine(self):
        """
        Base function for refining invariants

        This function must be defined individually
        """

        if self.verbose >= 1:
            print('Refine {} candidate invariants'.format(len(self.sols)))

        

    def print_sols(self):
        """
        Print solutions
        """
        print 'Detected invariants for {}:'.format(self.__class__.__name__)

        from iexp import IExp
        IExp.print_invs(self.sols)
        

    def go(self):
        """
        Shortcut to find, refine, and print invariants
        """
        _,solve_t = CM.vtime(self.solve,{},s='solve')

        refine_t = 0.0
        if self.do_refine:
            _,refine_t = CM.vtime(self.refine,{},
                                  s='refine')

        if self.verbose >= 1:
            self.print_sols()

        self.time_t = {'solve': solve_t, 'refine':refine_t}




##### Driver #####

class InvGen(object):
    """
    Main class to generate invariants. 
    It makes calls to other classes to get different 
    types of invariants
    
    

    EXAMPLES:
    See usage example in classes Eqt, Ineqs, SimpleArray, NestedArray
    """

    def __init__(self,filename,verbose):

        if verbose >= 1:
            from datetime import datetime
            from time import time
            import platform            
            
            print('*** %s ***'%(self.__class__.__name__))
            # if verbose >= 2:
            #     print CM.dict2str(CM.get_arguments()[0],
            #                       ignores=['platform','self'])
                    
            curTime   = time()
            print datetime.fromtimestamp(curTime).ctime()
            print version()
            print ' '.join([platform.node(),platform.system(),
                            platform.release(),platform.machine()])

        
        rfile,read_t = CM.vtime(ReadFile,
                                {'filename':filename,'verbose':verbose},
                                s='ReadFile')

        self._vs       = rfile.vs
        self._tcs      = rfile.tcs
        self._tcs2     = rfile.tcs2
        self._xinfo    = rfile.xinfo
        self._filename = filename
        self._time_t   = {'read_file':read_t}
        self._verbose  = verbose


    @property
    def tcs(self): return self._tcs
    @property
    def tcs2(self): return self._tcs2
    @property
    def xinfo(self): return self._xinfo
    @property
    def filename(self): return self._filename
    @property
    def time_t(self): return self._time_t
    
    def get_vs(self): return self._vs
    def set_vs(self,vs): self._vs = vs
    vs = property(get_vs,set_vs)

    def get_verbose(self): return self._verbose
    def set_verbose(self,v): self._verbose = v
    verbose = property(get_verbose,set_verbose)
    

    def getInvs(self, inv_typ, 
                seed=0, 
                deg=2, terms=None,
                vs=None, cs=(-2,2),
                do_min=False, comb_size=None):
        """
        inv_typ:
        - eqt
        - ieq cl, ieq fpoly, ieq mpp, ieq oct
        - simple 
        - nested  

        EXAMPLES:
        ig.getInvs(inv_typ='ieq cl',seed=1,vs=[x,y],deg=1) #classic polyhedron
        ig.getInvs(inv_typ='eqt',seed=1) #equation
        
        """
        
        self.seed = time() if seed is None else seed
        set_random_seed(self.seed)

        if self.verbose >= 1:
            print('seed %g (test %g %g %g)'
                  %(self.seed,random(),random(),random()))
        
        d = self.tcs[0]
        # vOther, vList = CM.vpartition(d.keys(),
        #                               lambda k: isinstance(d[k],list))

        if vs is None:
            vs = self.vs
        vOther, vList = CM.vpartition(vs,lambda v:isinstance(d[v],list))
                        
        inv_typ = inv_typ.lower()
        
        #Array Invariants
        if any(s in inv_typ for s in ['simple','simple1','nested']):
            if vList:
                self.vs = vList
                if 'nested' in inv_typ:
                    rs, time_t = self.getNestedArray()
                elif 'simple2' in inv_typ:
                    rs, time_t = self.getSimpleArray2()
                else:
                    rs, time_t = self.getSimpleArray()
            else:
                print 'No variable of type Array/List found'
                rs, time_t = [], 0.0

        else:  
            #Polynomial type
            if vOther:
                if 'ieq' in inv_typ:
                    if __debug__:
                        assert vs is None or \
                            all(v in vOther for v in vs)

                    rs,time_t = self.getIeqs(ieq_typ=inv_typ,
                                             vs=vs,deg=deg,
                                             terms=terms,
                                             comb_size=comb_size,
                                             cs=cs,do_min=do_min)
                else: #eqt
                    self.vs = vOther
                    rs, time_t = self.getEqts(deg=deg)

            else:
                print 'No variable of type Numerical found'
                rs, time_t = [], 0.0

        return rs, time_t #+ self.time_t['read_file']
    
    def getEqts(self, deg):
        """
        EXAMPLES:
        ig = InvGen('../traces/NLA/cohendiv.tcs',seed=1)
        ps = ig.getEqts(deg=2)
        """

        terms = Miscs.gen_terms(deg,self.vs,verbose=self.verbose)
        tcs1,tcs2 = Miscs.get_sample(self.tcs,len(terms),
                                     sampleP=150,min_=None,
                                     verbose=self.verbose)

        tcs2 = self.tcs2 + tcs2
        
        from inv_polynomials import Eqt
        solver = Eqt(terms   = terms,
                     tcs1    = tcs1,
                     tcs2    = tcs2,
                     xinfo   = self.xinfo,
                     verbose = self.verbose)
        solver.go()
        sols = solver.sols
        time = sum(solver.time_t.values())
        
        if not (CM.is_none_or_empty(sols) or
                CM.is_none_or_empty(self.xinfo['Assume'])):

            #deduce new info if external knowledge (assumes) is avail
            from inv_polynomials import IeqDeduce
            solver = IeqDeduce(xinfo = self.xinfo,
                               eqts    = [s.inv for s in sols],
                               verbose = self.verbose)
            solver.go()
            sols = sols + solver.sols
            time = time + sum(solver.time_t.values())

        return sols, time

    
    def getIeqs(self, ieq_typ='ieq fpoly',
                deg=None, vs=None, terms=None,
                comb_size=None,
                cs=(-2,2),   #FPoly coef ranges, [-2,-1,0,1,2]
                do_min=False): #MPP 
        """
        If terms are specified, then just use them, ignore vs and ds.
        Otherwise, use vs and deg to generate terms.

        EXAMPLES:
        ig = InvGen('../traces/NLA/cohendiv.tcs',seed=1)
        ps = ig.getIeqs(vs=[x,y],deg=1)
        ps = ig.getIeqs(vs=[x,y,a],deg=1,comb_size=2)
        ps = ig.getIeqs(ieq_typ='ieq oct',vs=ig.vs,deg=2)
        """

        assert terms or (vs and deg),\
            'either terms or (vs and deg) must be non-empty'
        
        if terms is None:
            terms = Miscs.gen_terms(deg, vs, verbose=self.verbose)

        tcs1, tcs2 = Miscs.get_sample(self.tcs, len(terms),
                                      sampleP=300, min_=100,
                                      preserveTcs=True,
                                      verbose=self.verbose)
        tcs2 = self.tcs2 + tcs2

        if comb_size is None:
            solver = self._getIeqs(ieq_typ=ieq_typ,
                                   terms=terms,
                                   cs=cs, do_min=do_min,
                                   tcs1=tcs1, tcs2=tcs2)
            solver.go()
            return solver.sols, sum(solver.time_t.values())

        else:
            return self.getIeqsCombs(ieq_typ=ieq_typ,
                                     terms=terms,
                                     comb_size=comb_size,
                                     cs=cs, 
                                     do_min=do_min,
                                     tcs1=tcs1,
                                     tcs2=tcs2)
        
        

    def getIeqsCombs(self,ieq_typ,terms,comb_size,cs,do_min,tcs1,tcs2):
        """
        Get inequalities over subset of terms (size comb_size)
        Note that the Samples are passed directly to IeqCLPoly so
        that polyhedrons are built over the same sample
        
        EXAMPLES:
        
        see more usages in getIeqs() above which calls this function

        ig = InvGen('../traces/NLA/cohendiv.tcs',seed=1)
        ps = ig.getIeqs(terms=[a,b,a*b,a*a],comb_size=3)

        """
        
        termsCombsSiz = binomial(len(terms),comb_size)  
        
        print 'Number of subsets (size %d) over %d terms: %d\n'\
            %(comb_size,termsCombsSiz,termsCombsSiz)

        termsCombs = Combinations(terms,comb_size)
        sols = []
        time = 0
        for ctr,terms in Miscs.senumerate(termsCombs):
            
            print '\n%d/%d. Find Ieqs over terms %s'%(ctr+1,
                                                      termsCombsSiz,
                                                      terms)

            solver = self._getIeqs(ieq_typ=ieq_typ,
                                   terms=terms,
                                   cs=cs,
                                   do_min=do_min,
                                   tcs1=tcs1,tcs2=tcs2)
            
            solver.go()
            sols = sols + solver.sols
            time = time + sum(solver.time_t.values())
        

        print '\nRefine %d combined solutions'%len(sols)
        rf = Refine(ps=sols,verbose=self.verbose)
        rf.rfilter(tcs=tcs1+tcs2)
        rf.rinfer()
        sols = rf.ps

        print '\nRESULTS (combinations)'
        print '\n'.join(map(str,sols))
        return sols, time


    def _getIeqs(self,ieq_typ, terms, cs, do_min, tcs1, tcs2):
        
        if 'cl' in ieq_typ:
            from inv_polynomials import IeqCLPoly
            solver = IeqCLPoly(terms   = terms,
                               tcs1    = tcs1,
                               tcs2    = tcs2,
                               xinfo   = self.xinfo,
                               verbose = self.verbose)
            
        elif 'fpoly' in ieq_typ:
            from inv_polynomials import IeqFPoly
            solver = IeqFPoly(terms   = terms,
                              tcs     = tcs1 + tcs2,
                              cs      = cs,
                              xinfo   = self.xinfo,
                              verbose = self.verbose)

        elif 'mpp'  in ieq_typ:
            from inv_polynomials import IeqMPP
            solver = IeqMPP(terms   = terms,
                            tcs1    = tcs1,
                            tcs2    = tcs2,
                            xinfo   = self.xinfo,
                            do_min  = do_min,
                            verbose = self.verbose)   

        elif 'oct' in ieq_typ:
            from inv_polynomials import IeqOct
            solver = IeqOct(terms   = terms,
                            tcs1    = tcs1,
                            tcs2    = tcs2,
                            xinfo   = self.xinfo,
                            verbose = self.verbose)   
            

        else:
            raise AssertionError('Cannot generate inequalities %s'%ieq_typ)

        return solver

    def getSimpleArray(self):
        """
        EXAMPLES:
        ig = InvGen("Traces/AES/Simple/aes_State2Block.tc",verbose=1)
        ig.getSimpleArray()
        """
        from inv_arrays import SimpleArray
        tcs2 = self.tcs + self.tcs2 #refine on all tcs
        solver = SimpleArray(terms   = self.vs,
                             tcs1    = self.tcs,
                             tcs2    = tcs2, 
                             xinfo   = self.xinfo,
                             verbose = self.verbose)
        solver.go()

        return solver.sols, sum(solver.time_t.values())


    def getSimpleArray2(self):
        """
        EXAMPLES:
        ig = InvGen('../invs/tcs2/simple/aes_State2Block.tc',seed=0,verbose=1)
        ig.getSimpleArray()
        """

        tcs2 = self.tcs + self.tcs2 #refine on all tcs
        solver = SimpleArray2(terms   = self.vs,
                              tcs1    = self.tcs,
                              tcs2    = tcs2,
                              xinfo   = self.xinfo,
                              verbose = self.verbose)
        solver.go()

        return solver.sols, sum(solver.time_t.values())

    
    def getNestedArray(self):
        """
        EXAMPLES:
        ig = InvGen('Traces/AES/Nested/aes_mul.tc',seed=0,verbose=1)
        ps = ig.getNestedArray()
        """
        tcs1,_ = Miscs.get_sample(tcs     = self.tcs,
                                  tcsN    = 1,  #using only 1 array
                                  sampleP = 100,
                                  min_    = None,
                                  verbose = self.verbose)

        from inv_arrays import NestedArray
        #print self.tcs + self.tcs2
        

        solver = NestedArray(terms   = self.vs,
                             tcs1    = tcs1,
                             tcs2    = self.tcs + self.tcs2, #refine on all tcs
                             xinfo   = self.xinfo,
                             verbose = self.verbose)

        solver.go()
        return solver.sols, sum(solver.time_t.values())




"""
Generate simple array relations using SMT
Todo: don't use all traces -- this will make it very slow !
"""

from z3 import *

class SimpleArray2(Inv):
    """
    Find Simple Array Invariants of the form 
    c1A[i][j].. + c2B[i1'][i2'].. = 0

    EXAMPLES

    ig = InvGen("Traces/AES/Simple/paper_multidim.tc",verbose=1)
    _ =  ig.getInvs(inv_typ='simple2',seed=1)
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
    *** SimpleArray2 ***
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
    Detected Invariants for SimpleArray2:
    0: ('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 1}])
    1: ('lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0', [{'B0': 4}, {'B0': 0}, {'B0': 2}])
    Time elapsed: 0.1462 s (solve)
    Refine 2 candidate invariants
    * rfilter(|ps|=2,|tcs|=9)
    rfilter (before 2, after 2, diff 0)
    Time elapsed: 0.0051 s (refine)
    Detected Invariants for SimpleArray2:
    0: ('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 1}])
    1: ('lambda B, A, B0: (-7*B[B0]) + (A[1/2*B0]) + (-3/2*B0) == 0', [{'B0': 4}, {'B0': 0}, {'B0': 2}])
    
    """
    
    def __init__(self,terms,tcs1,tcs2,xinfo,verbose):
 
        super(SimpleArray2,self).__init__(
            terms  = terms,  #not important
            tcs1   = tcs1,
            tcs2   = Miscs.keys_to_str(tcs2), #for refinement
            xinfo  = xinfo,
            verbose= verbose)

    
        
    def solve(self): #simple
        print 'Create new trace format (treating array elems as seperate vars)'
        aInfo = {}  #{A_0_0=[0,0],B_1_2_3=[1,2,3]}
        
        tcs = [SimpleArray2.genTracesE2V(t,aInfo=aInfo,verbose=self.verbose)
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
        ps = SimpleArray2.filterDupArrs(ps,aInfo=aInfo,verbose=self.verbose)
        ps = [Miscs.elim_denom(p) for p in ps] #Eliminating denominators if exist
        ps = SimpleArray2.modifySigns(ps,verbose=self.verbose)

        if ps == []:
            self.set_sols([])
            return

        if set(map(str,ps)) != psOld:
            print 'Some rels were modifed'
            print '\n'.join(map(str,ps))

        ###
        print "Find rels over indices"
        psInfo = [SimpleArray2.parseP(p,aInfo,verbose=self.verbose) for p in ps]
        sols = SimpleArray2.findRels(psInfo,verbose=self.verbose)
        
        if CM.is_none_or_empty(sols):
            sols = ps
            self.do_refine = False
            
        self.set_sols(sols)
        self.print_sols()


    def refine(self):
        super(SimpleArray2,self).refine()
            
        #rf = Refine(ps=self.sols,verbose=self.verbose)
        #rf.rrank()
        #rf.rfilter(tcs=self.tcs2)

        #self.set_sols(rf.ps)
        
    #######

    @staticmethod
    def genTracesE2V(d,aInfo,verbose):
        """
        Convert array elements into new variables

        
        EXAMPLES:

        sage: aInfo = {}
        
        sage: dsVals = SimpleArray2.genTracesE2V({'A':[['a','b'],['c','d'],['e','f',['z','w']]],'B':[1,2,[7,8]],'C':[100]},aInfo,verbose=1)

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

        sage: SimpleArray2.filterDupArrs([x_0 + x_1 == 0, x_1 + y_1 == 0, x_0+y_1+y_0==0, x_0+x_1-2==0],{x_0:{'name':'x','idxs':[0]},x_1:{'name':'x','idxs':[1]},y_0:{'name':'y','idxs':[0]},y_1:{'name':'y','idxs':[1]}},verbose=0)
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
        sage: SimpleArray2.modifySigns([x-y==0,-2*x + 2*y ==0])
        [x - y == 0, 2*x - 2*y == 0]

        sage: SimpleArray2.modifySigns([-x-y==0,2*x+2*y==0])
        [-x - y == 0, -2*x - 2*y == 0]

        sage: SimpleArray2.modifySigns([-x-y==0,2*x-2*y==0])
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

        # sage: d = SimpleArray2.a_parse(-A_1_4 + 7/2*B_2_11_8 - 8*C_20_5_0 + 100 == 0)
        # sage: sorted(d.items())
        # [('A', {'_contents_': {A_i_1: 4, A_i_0: 1, A_coef: -1}}), ('B', {'_contents_': {B_coef: 7/2, B_i_2: 8, B_i_1: 11, B_i_0: 2}}), ('C', {'_contents_': {C_i_2: 0, C_i_1: 5, C_i_0: 20, C_coef: -8}}), ('COEF', {'_contents_': {COEF_coef: 100}})]
        # sage: var('A_4 B_11')
        # (A_4, B_11)
        # sage: d = SimpleArray2.a_parse(1/7*A_4+B_11==0)
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

        #sage: SimpleArray2.findRels(ps=[-rvu_2_1 + t_9 == 0, rvu_2_3 - t_11 == 0, rvu_2_0 - t_8 == 0, -rvu_3_2 + t_14 == 0, -rvu_0_0 + t_0 == 0, rvu_0_2 - t_2 == 0, -rvu_3_1 + t_13 == 0, rvu_3_3 - t_15 == 0, rvu_0_1 - t_1 == 0, -rvu_0_3 + t_3 == 0, -rvu_1_3 + t_7 == 0, -rvu_1_0 + t_4 == 0, rvu_1_2 - t_6 == 0, -rvu_3_0 + t_12 == 0, rvu_1_1 - t_5 == 0, rvu_2_2 - t_10 == 0],verbose=0)
        """

        ks = psInfo[0]
        pivots = [k for k in ks if k != 'coef']

        rs = [SimpleArray2.findRelsPivot(pivot,psInfo,verbose) for pivot in pivots]
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

        rs = [SimpleArray2.a_solve(pivot,k,psInfo,verbose=verbose)
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
        terms = [SimpleArray2.genTemplate(name,d,verbose) for name,d in rs]

        rel = ' + '.join([t for t in terms if t is not None])
        idxStr = ', '.join(arrs + pivotIdxs)
        
        rs = 'lambda %s: %s == 0'%(idxStr,rel)

        #extract the index info since this result only works for these indices
        idxInfo = SimpleArray2.extractIdxInfo(pivot,psInfo,verbose=verbose)
        
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


    @staticmethod
    def nested(arr,idxs):
        """
        A,[1,2,3] = > A[1][2][3]

        sage: import z3
        sage: B0 = z3.Array('B0',z3.IntSort(),z3.IntSort())
        sage: B1 = z3.Array('B1',z3.IntSort(),z3.IntSort())
        sage: B2 = z3.Array('B2',z3.IntSort(),z3.IntSort())
        sage: B = z3.Array('B',z3.IntSort(),B0.sort())
        sage: SimpleArray2.nested(B,map(lambda x:z3.IntVal(str(x)),[0,1]))
        B[0][1]
        """

        if __debug__:
            assert z3.is_expr(arr)
            assert isinstance(idxs,list) and len(idxs) >= 1 \
                and all(z3.is_expr(idx) for idx in idxs)

        return reduce(lambda rs,idx: z3.Select(rs,idx),
                      idxs[1:], z3.Select(arr,idxs[0]))

    @staticmethod
    def gen_linear_exp(s,idx_name,idx_vals):
        """
        #sage: SimpleArray2.gen_linear_exp('b0','j',map(lambda x:z3.IntVal(str(x)),[1,2,1,4]))
        b0_j_0 + 2*b0_j_1 + b0_j_2 + 4*b0_j_3 + b0_j_d
        """
        rs = [vi*z3.Int('{}_{}_{}'.format(s,idx_name,i))
              for i,vi in enumerate(idx_vals)]
        rs = reduce(lambda x,y:x+y,rs,z3.Int('{}_{}_d'.format(s,idx_name)))

        return rs

    @staticmethod
    def gen_range_constr(linear_exp,max_len,to_z3_exp=True):
        """
        #sage: lexp=  SimpleArray2.gen_linear_exp('b0','j',[1,2,1,4])
        #sage: SimpleArray2.gen_range_constr(lexp,10)
        [b0_j_0 + 2*b0_j_1 + b0_j_2 + 4*b0_j_3 + b0_j_d >= 0, 
        b0_j_0 + 2*b0_j_1 + b0_j_2 + 4*b0_j_3 + b0_j_d <= 9]

        """
        if __debug__:
            assert max_len >= 1
            
        rs = [z3.IntVal('0') <= linear_exp, linear_exp <= z3.IntVal(str(max_len - 1))]

        return rs

    @staticmethod
    def gen_arr_expr1(arr, k, dim, idx_vals):
        """
        Returns arr[][][],  range_constr
        """
        if __debug__:
            assert z3.is_expr(arr)
            assert k >= 0
            assert isinstance(dim,list) and len(dim) >= 1
            assert isinstance(idx_vals,list) and len(idx_vals) >= 1


        idxs = [SimpleArray2.gen_linear_exp('v_k{}_{}'.format(k,i),'j',idx_vals) 
                for i in range(len(dim))]

        r_constr = [SimpleArray2.gen_range_constr(idx,ml) for idx,ml in zip(idxs,dim)]

        exp_ = SimpleArray2.nested(arr,idxs)    #B[j0][j1]...

        coef = SimpleArray2.gen_linear_exp('v_k{}'.format(k),'c',idx_vals) 
        exp_ = coef * exp_     #c * B [j0][j1]...

        if __debug__:
            assert z3.is_expr(exp_)
            assert isinstance(r_constr,list)

        return exp_, r_constr

    @staticmethod
    def gen_arr_expr2(arrs,dims,idx_vals):
        """
        Returns b[][] + c[][] + ... , r_constr
        """
        if __debug__:
            assert isinstance(arrs,list) and len(arrs) >= 1 and \
                all(z3.is_expr(x) for x in arrs)
            assert isinstance(dims,list) and len(dims) == len(arrs) and \
                all(isinstance(dim,list) for dim in dims)
            assert isinstance(idx_vals,list) and len(idx_vals) >= 1
                

        rs = [SimpleArray2.gen_arr_expr1(arr,k,dim,idx_vals) 
              for k,(arr,dim) in enumerate(zip(arrs,dims))]
        rs1 = [r_[0] for r_ in rs]  #B[][],C[][], ..
        rs2 = [r_[1] for r_ in rs]  #range constraints
        coef = SimpleArray2.gen_linear_exp('v_k{}'.format(len(arrs)),'c',idx_vals)
        exp_ = z3.Sum(rs1+[coef])   #B[][] + C[][] + ...


        r_constr = z3.And(flatten(rs2))
            

        if __debug__:
            assert z3.is_expr(exp_)
            assert z3.is_expr(r_constr)

        return exp_, r_constr

    @staticmethod
    def gen_arr_expr3(a,arrs,dims,idx_vals):
        """
        a[][][] == b[][] + c[][] + ...

        sage: import z3
        sage: A = z3.Array('A',z3.IntSort(),z3.IntSort())
        sage: B0 = z3.Array('B0',z3.IntSort(),z3.IntSort())
        sage: B1 = z3.Array('B1',z3.IntSort(),z3.IntSort())
        sage: B2 = z3.Array('B2',z3.IntSort(),z3.IntSort())
        sage: B = z3.Array('B',z3.IntSort(),B0.sort())
        
        #sage: SimpleArray2.gen_arr_expr3(A,[B],[[3,4]],[z3.IntVal('1')])

        """
        if __debug__:
            assert z3.is_expr(a)
            assert isinstance(arrs,list) and len(arrs) >= 1 and \
                all(z3.is_expr(x) for x in arrs)
            assert isinstance(dims,list) and len(dims) == len(arrs) and \
                all(isinstance(dim,list) for dim in dims)
            assert isinstance(idx_vals,list) and len(idx_vals) >= 1 and \
                all(z3.is_expr(x) for x in idx_vals), str(idx_vals)
            
        rhs,r_constr = SimpleArray2.gen_arr_expr2(arrs,dims,idx_vals)  #b[][] + c[][]
        lhs = SimpleArray2.nested(a,idx_vals)   #a[][][]
        exp_ = lhs == rhs

        if __debug__:
            assert z3.is_expr(exp_)
            assert z3.is_expr(r_constr)

        return exp_, r_constr
    
    @staticmethod
    def gen_arr_expr4(a,a_dim,arrs,arrs_dims):
        """
        In [59]: rs1,rs2= ta.gen_arr_expr4(A,[2],[B],[[100,400]])

        In [60]: rs1
        Out[60]: 
        And(A[0] ==
        (B_c_d + 0*B_c_0)*
        B[B_0_j_d + 0*B_0_j_0][B_1_j_d + 0*B_1_j_0] +
        aaa_c_d +
        0*aaa_c_0,
        A[1] ==
        (B_c_d + 1*B_c_0)*
        B[B_0_j_d + 1*B_0_j_0][B_1_j_d + 1*B_1_j_0] +
        aaa_c_d +
        1*aaa_c_0)

        In [61]: rs2
        Out[61]: 
        And(And(B_0_j_d + 0*B_0_j_0 >= 0,
        B_0_j_d + 0*B_0_j_0 <= 99,
        B_1_j_d + 0*B_1_j_0 >= 0,
        B_1_j_d + 0*B_1_j_0 <= 399),
        And(B_0_j_d + 1*B_0_j_0 >= 0,
        B_0_j_d + 1*B_0_j_0 <= 99,
        B_1_j_d + 1*B_1_j_0 >= 0,
        B_1_j_d + 1*B_1_j_0 <= 399))
        """

        if __debug__:
            assert z3.is_expr(a)
            assert isinstance(a_dim,list)
            assert isinstance(arrs,list) and len(arrs) >= 1

        from itertools import product
        rs = [SimpleArray2.gen_arr_expr3(a,arrs,arrs_dims,
                                         map(lambda x: z3.IntVal(str(x)),idx_vals))
              for idx_vals in product(*map(range,a_dim))]
        rs1,rs2 = zip(*rs)
        rs1 = z3.And(rs1)
        rs2 = z3.And(rs2)
        return z3.And(rs1,rs2)


    @staticmethod
    def gen1(i,tcs):
        p = [SimpleArray2.gen_arr_expr4(tc[i][0],tc[i][1],
                                        map(lambda t: t[0],tc[:i]+tc[i+1:]),
                                        map(lambda t: t[1],tc[:i]+tc[i+1:]),
                                        )
             for tc in tcs]
        p = z3.And(p)
        return p


    @staticmethod
    def foo(tcs):

        
        tcs = Miscs.keys_to_str(tcs)#remove this line when done, not necessary
        anames = tcs[0].keys()
        tcs_ = [[SimpleArray2.init_arr('{}_tc{}'.format(k,i),v) for k,v in tc.items()]
            for i,tc in enumerate(tcs)]

        af = []
        tcs__ = []
        for tc in tcs_:
            tc_ = []
            for t in tc:
                tc_.append(t[:2])
                af.append(t[2]) #formula
            tcs__.append(tc_)

        af = z3.And(af)

        s = z3.Solver()
        s.add(af)
        #print anames
        #print tcs_
        #print af
        #print tcs__
        rs = []
        for i,aname in enumerate(anames):
            print 'Pivot: {}'.format(aname)
            f = SimpleArray2.gen1(i,tcs__)
            print 'generating formula'
            #print f
            s.push()
            s.add(f)
            print 'begin checking'
            res = s.check()
            print 'after checking'
            if res == z3.sat:
                rs.append(s.model())
                SimpleArray2.print_model(s.model())
                CM.pause('sat')
            else:
                print res
            s.pop()

        return rs

    @staticmethod
    def print_model(m):
        m = sorted([(f,m[f]) for f in m],key=lambda (a,_): str(a))
        m = [(k,v) for (k,v) in m if not str(v).startswith('[')]
        print '\n'.join(['{}: {}'.format(k,v) for (k,v) in m])

    @staticmethod
    def init_arr(a,vs):
        RS_f=[]
        RS_v=[]
        RS_l=[]
        (_,d) = SimpleArray2.to_z3(a,vs,RS_f,RS_v,0)
        a = RS_v[-1]
        f = z3.And(RS_f)

        rs = vs
        for d_ in range(d):
            RS_l.append(len(rs))
            rs = rs[0]

        return a,RS_l,f

    @staticmethod
    def to_z3(Aname,A,RS_f,RS_v,d):

        if __debug__:
            assert isinstance(Aname,str)
            assert isinstance(RS_f,list)
            assert isinstance(RS_v,list)

        if CM.is_iterable(A):
            assert len(A)>=1

            vs = [SimpleArray2.to_z3(Aname+str(i),a,RS_f,RS_v,d) for 
                  i,a in enumerate(A)]
            A_ = z3.Array(Aname,z3.IntSort(),vs[0][0].sort())

            rs_f = [z3.Select(A_,i) == v for i,(v,_) in enumerate(vs)]
            RS_f.extend(rs_f)
            RS_v.append(A_)
            d = vs[0][1] + 1
        else:
            A_ =  z3.IntVal(str(A))  #todo 1

        if __debug__:
            assert z3.is_expr(A_)

        return A_,d
