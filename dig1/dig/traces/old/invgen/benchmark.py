import common as CM
from miscs import Miscs
from iexp import IExp
from invgen import InvGen
from sage.all import *

"""
Benchmark Scripts

"""



def execDir(dir_, inv_typ='eqt', runs=1, verbose=1):
    """
    sols = execDir('../traces/NLA/',inv_typ='eqts')
    sols = execDir('../invs/tcs2/nested/',inv_typ='nested',verbose=0)
    sols = execDir('../invs/tcs2/simple/',inv_typ='simple',verbose=0)
    """

    print '\n********** BEGIN BENCHMARK **********'
    print 'Invariant Type: %s'%inv_typ
    print 'Trace Directory: %s'%dir_
    print 'Number of runs for each trace file: %s'%runs
    print '********** *************** **********\n\n'
    

    tcsFiles = os.listdir(dir_)
    tcsFiles = [fn for fn in tcsFiles if
                (fn.endswith('.tcs') or fn.endswith('.tc'))]




    sols = []
    for fn in tcsFiles:
        file_ = os.path.join(dir_,fn)
        expect, sols_fn = execFile(file_,inv_typ,runs,verbose)
        sols = sols + [(file_,expect,sols_fn)]


    print '\n\n***** BENCHMARK SUMMARY (inv_typ "%s")*****\n\n'%inv_typ
    for i,(f,expect,sols_fn) in Miscs.senumerate(sols):
        print_summary(f,expect,sols_fn,inv_typ)


        

def execFile(file_,inv_typ='eqt',runs=1,verbose=1):
    def getDeg(fn):
        deg3=['freire2','cohencu','prod4br','knuth','geo3','ps3']
        deg4=['ps4']
        deg1=['AesKeySetupEnc_LRA','AesKeySetupDec_LRA']
        
        if CM.vany(deg4,lambda x: x in fn):
            return 4
        elif CM.vany(deg3,lambda x: x in fn):
            return 3
        elif CM.vany(deg1,lambda x: x in fn):
            return 1
        else:
            return 2


    def getInvs(ig,seed,inv_typ):
        vs = None
        deg = None
        terms = None
        combSiz = None
        
        if 'eqt' in inv_typ:
            deg = getDeg(ig.filename)

        if 'ieq' in inv_typ:
             #W: these default values will not give any useful results
            terms = ig.vs
            combSiz = 3
        
        rs,time = ig.getInvs(seed=seed,inv_typ=inv_typ,
                             vs=vs,deg=deg,terms=terms,comb_size=combSiz)
        return rs,time


    inv_typ = inv_typ.lower()
    sols_fn = []
    print "\n***** Generate Invs From File '%s' *****\n"%file_
    ig = InvGen(file_,verbose=verbose)
    
    for nr in srange(runs):
        print '\n*** Run %d ***\n'%nr
        try:
            rs,time = getInvs(ig,seed=nr,inv_typ=inv_typ)
        except Exception as msg:
            print 'E:', msg
            rs = []
            time = 0.0
        sols_fn = sols_fn + [(nr,rs,time)]

    expect = ig.xinfo['Expect']
    print_summary(file_,expect,sols_fn,inv_typ)
    return expect, sols_fn


def print_summary(file_,expect,sols_fn,inv_typ):

    print "\n\nSUMMARY (inv_typ '%s')"%inv_typ
    print "Invariants Generated from '%s'"%(file_)
    print "Expect %s"%(str(expect))
    time_total = 0.0
    for (nr,rs,time) in sols_fn:
        print '* Run %d (time %f)'%(nr,time)
        IExp.print_invs(rs)
        time_total = time_total + time
        
    print 'TIME AVG %.1f (%s)\n'%(time_total/len(sols_fn),file_)

    
#block2State   r[i][j] = t[4i+j]  this result is correct but being filtered out        







#[[-9,-9,-9,0],[-5,-6,-6,0],[-0,-6,-6,0],[-3,-6,-6,0],[-3,-6,-12,0],[-6,-6,-6,0],[-6,-9,-9,0],[-7,-9,-9,0],[-8,-9,-9,0],[-8,-9,-16,0],[-10,-10,-10,0]]
