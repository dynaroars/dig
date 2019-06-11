import os.path
from collections import OrderedDict
import time

import vu_common as CM
from miscs import Miscs

from klee import KLEE

import settings
logger = CM.VLog('prover')
logger.level = settings.logger_level  
logger.printtime = settings.logger_printtime

from ds import Inp, Inps, DTraces, Inv,  DInvs, Invs
from src import Src

def merge(ds):
    newD = {}
    for d in ds:
        for loc in d:
            assert d[loc]
            if loc not in newD: newD[loc] = {}
            for inv in d[loc]:
                assert d[loc][inv]
                if inv not in newD[loc]: newD[loc][inv] = set()
                for e in d[loc][inv]:
                    newD[loc][inv].add(e)
    return newD

class Prover(object):
    def __init__(self, src, inpdecls, invdecls, tmpdir):
        assert isinstance(src, Src), src
        self.src = src
        self.inpdecls = inpdecls
        self.invdecls = invdecls
        self.tmpdir = tmpdir

    def getInpsSafe(self, dinvs, inps, inpsd):
        """call verifier on each inv"""
        def wprocess(tasks, Q):
            rs = [(loc, inv,
                   self.src.instrAsserts(
                       {loc:set([inv])}, inps, inpsd,self.invdecls))
                     for loc, inv in tasks]
            rs = [(loc, inv, KLEE(isrc, self.tmpdir).getDInps())
                  for loc, inv, isrc in rs]
            if Q is None: #no multiprocessing
                return rs
            else:
                Q.put(rs)

        tasks = [(loc, inv) for loc in dinvs for inv in dinvs[loc]
                 if inv.stat is None]
        wrs = Miscs.runMP("prove", tasks, wprocess, chunksiz=1,
                          doMP=settings.doMP and len(tasks) >= 2)

        mInps, mCexs, mdinvs = [], [], DInvs()
        for loc, inv, (klDInps, klDCexs, isSucc) in wrs:
            mInps.append(klDInps)
            mCexs.append(klDCexs)
            try:                    
                _ = klDInps[loc][str(inv)]
                stat = Inv.DISPROVED
            except KeyError:
                stat = Inv.PROVED if isSucc else Inv.UNKNOWN
            inv.stat = stat
            
            if loc not in mdinvs: mdinvs[loc] = Invs()
            mdinvs[loc].add(inv)

        return merge(mInps), merge(mCexs), mdinvs

    def check(self, dinvs, inps, minv, maxv):
        """
        Check invs.
        Also update traces, inps
        """
        assert isinstance(dinvs, DInvs), dinvs
        assert inps is None or (isinstance(inps, Inps) and inps), inps        
        
        if self.inpdecls:
            inpsd = OrderedDict((vname, (vtyp, (minv, maxv)))
                                for vname, vtyp in self.inpdecls.iteritems())
        else:
            inpsd = None
            
        logger.detail("checking {} invs:\n{}".format(
            dinvs.siz, dinvs.__str__(printStat=True)))
        return self.getInpsSafe(dinvs, inps, inpsd)

    def checkRange(self, dinvs, inps):
        minv, maxv = -1*DTraces.inpMaxV, DTraces.inpMaxV,         
        return self.check(dinvs, inps, minv, maxv)

    def checkNoRange(self, dinvs, traces, inps):
        minv, maxv = -1*DTraces.inpMaxV*10, DTraces.inpMaxV*10,
        return self.check(dinvs, inps, minv, maxv)

