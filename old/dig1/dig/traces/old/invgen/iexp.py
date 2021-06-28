import vu_common as CM
from miscs import Miscs, ExtFun

from sage.all import *

class IExp(object):
    def __init__(self, inv):
        """
        EXAMPLES:
        
        """
        if __debug__:
            assert isinstance(inv,str) or \
                isinstance(inv,Miscs.sage_expr) or\
                (isinstance(inv,tuple) and len(inv) == 2 and \
                     isinstance(inv[0],str) and \
                     all(isinstance(inv_,dict) for inv_ in inv[1])),\
                 "unsupported inv type {}".format(inv)

        #' lambda x: x+1 ' strip off empty space
        if isinstance(inv,str):
            inv = inv.strip() 

        if isinstance(inv,tuple):
            inv = (inv[0].strip(),inv[1])

        self._inv = inv

    def __str__(self, simple=True):
        return self.inv.__str__()

    def __repr__(self):
        return self.inv.__repr__()

    def __hash__(self):
        """
        Potential error here since I only consider the hash value of the first part
        sage: IExp(('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 1}])).__hash__()
        -242286530765552022

        sage: IExp(('lambda A, B, A0: (A[A0]) + (-7*B[2*A0]) + (-3*A0) == 0', [{'A0': 2}, {'A0': 0}, {'A0': 100}])).__hash__()
        -242286530765552022
        """
        if isinstance(self.inv,tuple):
            return self.inv[0].__hash__()
        else:
            return self.inv.__hash__()

    def __eq__(self,other):
        return self.inv.__eq__(other.inv)

    def __ne__(self,other):
        return self.inv.__ne__(other.inv)

    @property
    def inv(self): return self._inv
    
    def get_score(self):
        """
        Gives higher scores to invs with 'nicer' shapes
        
        Examples:
        sage: var('rvu a q y')
        (rvu, a, q, y)
        
        sage: from iexp import IExp
        
        sage: rs = IExp((1/2)*x**2 + 134.134234*y + 1 >= 0); rs.get_score()
        12

        sage: rs = IExp(x**3 + 2.432*x + 8 == 0); rs.get_score()
        6

        sage: rs = IExp(x**2+x+7 >0); rs.get_score()
        3

        In case we cannot compute the score, returns the strlen of the inv

        sage: IExp(rvu + 2*a/q >= 0).get_score()
        -1

        sage: rs = IExp('lambda x: x**2+x+7 >0'); rs.get_score()
        -1
        """
        
        try:
            return self.score
        except AttributeError:
            score = IExp.compute_score(self.inv)
            self.score = score
            return score
            

    @staticmethod
    def compute_score(inv):
        try:
            Q = PolynomialRing(QQ,Miscs.get_vars(inv))
            rs = Q(inv.lhs()).coefficients()
            rs = [abs(r_.n()).str(skip_zeroes=True)
                  for r_ in rs if r_ != 0.0]
            rs = [sum(map(len,r_.split('.'))) for r_ in rs]
            rs = sum(rs)
            return rs
        except Exception:
            return -1
        

    @staticmethod
    def print_invs(invs,ignore_size=500):
        """
        If inv has len >= 500, then ignore it
        """
        
        if CM.is_none_or_empty(invs):
            print 'NONE'
        else:
            invs = sorted(invs,key=lambda inv: inv.get_score())
            rs = '\n'.join(['%3d: %s'%s for s in Miscs.senumerate(invs)])
            print rs


    def _eval(self,tc):

        if isinstance(self.inv, Miscs.sage_expr):
            return bool(self.inv.subs(tc))

        elif isinstance(self.inv,str) and '[' not in self.inv:
            return IExp._eval_lambda(self.inv,tc)
            
        else:
            return IExp._eval_lambda_array(self.inv,tc)


    @staticmethod
    def _eval_lambda(f,d):
        """
        Evaluates lambda function f

        Examples:

        sage: from iexp import IExp
        
        sage: IExp._eval_lambda('lambda x,y: x+y',{'x':2,'y':3,'d':7})
        5
        """
        assert isinstance(f,str) and 'lambda' in f, "improper input f '%s'"%f
        assert isinstance(d,dict)
        assert all(isinstance(k,str) for k in d.keys()), 'keys must be string'
        #assert CM.vall(d.keys(),lambda k: isinstance(k,str)), 'keys must be string'
        #assert(isinstance(k,str) for k in d.keys()), 'keys must be string'
        
        f = sage_eval(f)
        vs = f.func_code.co_varnames
        assert set(vs) <= set(d.keys()), 'E: not subset'

        #if d has more keys than variables in f then remove those extra keys
        d=dict([(k,d[k]) for k in vs])

        return f(**d)

        
    @staticmethod
    def _eval_lambda_array(p,tc):
        """
        Evaluate array expression p, e.g. p:  A[i,j,k]=B[2i+3j+k]
        
        If p is a tuple, then idxInfo is specified, i.e., p=(lambda ..,idxInfo),
        in this case then only test p on the elements from these indices from idxInfo
        
        
        Assumes:
        the first array in lambda is the pivot
        lambda A,B,i,j,k: ...  =>  i,j,k  belong to A

        
        
        inv = 'lambda B,C,D,i,j: B[i][j]=C[D[2i+3]]'
        returns true if inv is true on tc

        Examples:

        sage: from iexp import IExp

        sage: var('a,b,c,i,j')
        (a, b, c, i, j)

        sage: IExp._eval_lambda_array('lambda a,b,c,i,j: a[i][j]==2*b[i]+c[j]', {'a':[[4,-5],[20,11]],'b':[1,9],'c':[2,-7]})
        True
        
        sage: IExp._eval_lambda_array('lambda c,a,b,xor,i: c[i] == xor(a[i],b[i])', {'a': [147, 156, 184, 76], 'b': [51, 26, 247, 189], 'c': [160, 334, 79, 281]})
        False
        
        sage: IExp._eval_lambda_array('lambda c,a,b,xor,i1: c[i1] == xor(a[i1],b[i1])', {'a': [147, 156, 184, 76], 'b': [51, 26, 247, 189], 'c': [160, 134, 79, 241]})
        True

        
        sage: IExp._eval_lambda_array('lambda rvu, t, rvu1, rvu0: (rvu[rvu0][rvu1]) + (-t[4*rvu0 + rvu1]) == 0',{'t': [28, 131, 11, 85, 133, 46, 179, 20, 227, 148, 225, 197, 38, 221, 221, 126], 'rvu': [[28, 131, 11, 85], [133, 46, 179, 20], [227, 148, 225, 197], [38, 221, 221, 126]]})
        True

        #The following illustrate the use of idxVals,
        #i.e. p is only true under certain array rages

        sage: IExp._eval_lambda_array('lambda st, rvu, st0, st1: (-st[st0][st1]) + (rvu[4*st0 + st1]) == 0', {'rvu': [28, 131, 11, 85, 193, 124, 103, 215, 66, 26, 68, 54, 176, 102, 15, 237], 'st': [[28, 131, 11, 85, 133, 46, 179, 20, 227, 148, 225, 197, 38, 221, 221, 126], [193, 124, 103, 215, 106, 229, 162, 168, 166, 78, 144, 234, 199, 254, 152, 250], [66, 26, 68, 54, 206, 16, 155, 248, 231, 198, 240, 43, 208, 205, 213, 26], [176, 102, 15, 237, 49, 141, 213, 97, 137, 155, 50, 243, 112, 51, 124, 107]]})
        False

        sage: IExp._eval_lambda_array(('lambda st, rvu, st0, st1: (-st[st0][st1]) + (rvu[4*st0 + st1]) == 0',[{'st0': 0, 'st1': 0}, {'st0': 0, 'st1': 1}, {'st0': 2, 'st1': 2}, {'st0': 2, 'st1': 3}, {'st0': 3, 'st1': 0}, {'st0': 3, 'st1': 1}, {'st0': 3, 'st1': 2}, {'st0': 3, 'st1': 3}, {'st0': 0, 'st1': 2}, {'st0': 0, 'st1': 3}, {'st0': 1, 'st1': 0}, {'st0': 1, 'st1': 1}, {'st0': 1, 'st1': 2}, {'st0': 1, 'st1': 3}, {'st0': 2, 'st1': 0}, {'st0': 2, 'st1': 1}]), {'rvu': [28, 131, 11, 85, 193, 124, 103, 215, 66, 26, 68, 54, 176, 102, 15, 237], 'st': [[28, 131, 11, 85, 133, 46, 179, 20, 227, 148, 225, 197, 38, 221, 221, 126], [193, 124, 103, 215, 106, 229, 162, 168, 166, 78, 144, 234, 199, 254, 152, 250], [66, 26, 68, 54, 206, 16, 155, 248, 231, 198, 240, 43, 208, 205, 213, 26], [176, 102, 15, 237, 49, 141, 213, 97, 137, 155, 50, 243, 112, 51, 124, 107]]})
        True

        """
        if isinstance(p,tuple):
            assert len(p)==2
            idxInfo = p[1]
            p = p[0]
        else:
            idxInfo = None


        """
        Note: sage_eval vs eval
        sage_eval works on str of the format 'lambda x,y: 2*x+y'
        whereas eval works on str of the format 2*x+y directly (no lambda)
        Also, the result of sage_eval can apply on dicts whose keys are str
        e.g.  f(**{'x':2,'y':3})
        whereas the result of eval applies on dict whose keys are variables
        e.g.  f(**{x:2,y:3})
        """
        f = sage_eval(p)
        vs = f.func_code.co_varnames

        arrs    = [v for v in vs if v in tc]        #A,B
        extfuns = [v for v in vs if v in ExtFun.efdict]
        idxStr  = [v for v in vs if v not in arrs+extfuns]  #i,j,k
        
        d_tc    = dict([(v,tc[v]) for v in arrs])
        d_extfun= dict([(v,ExtFun(v).get_fun()) for v in extfuns])
        d_      = CM.merge_dict([d_tc,d_extfun])

        if idxInfo is None: #obtain idxsVals from the pivot array
            pivotContents = tc[arrs[0]] 
            idxVals  = [idx for idx,_ in Miscs.travel(pivotContents)]
            idxInfo = [dict(zip(idxStr,idxV)) for idxV in idxVals]
            
        ds = [CM.merge_dict([d_,idxInfo_]) for idxInfo_ in idxInfo]

        try:
            # for args in ds:
            #     print args
            #     print '%d,%d,res:%s'\
            #         %(args['st0'],args['st1'],str(f(**args)))
                                        
                
            #return CM.vall(ds, lambda args: f(**args))
            return all(f(**args) for args in ds)#, lambda args: f(**args))
        except IndexError:
            return False
        except TypeError:
            return False





