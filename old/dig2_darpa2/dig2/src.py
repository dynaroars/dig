import os
from collections import OrderedDict
import sage.all
from klee import KLEE

import vu_common as CM
import settings
logger = CM.VLog('src')
logger.level = settings.logger_level

stripTo = lambda s, to_s: s[s.find(to_s) + 1:].strip() #e.g., ...:x  -> x
class Src(object):
    
    def __init__(self, filename):
        assert os.path.isfile(filename), filename
        self.filename = filename
        
    def parse(self): return self._parse(self.filename)
    
    def instrPrintfs(self, invdecls):
        assert isinstance(invdecls, dict) and invdecls, invdecls
        return self.instr(self.filename, ".printf.c", invdecls, self.mkPrintfs)
    
    def instrAsserts(self, invs, inps, inpsd, invdecls, startFun="mainQ"):
        assert isinstance(invs, dict), invs
        assert (inpsd is None or
                (isinstance(inpsd, OrderedDict) and inpsd)), inpsd
        assert isinstance(invdecls, OrderedDict) and invdecls, invdecls
        assert inps is None or (isinstance(inps, set) and inps), inps

        inpParts = self.mkPrintfArgs(inpsd) if inpsd else (None, None)
        
        _mk = lambda invs, loc: KLEE.mkAssertInvs(
            invs, loc, inpParts, self.mkPrintfArgs(invdecls[loc]))
        
        stmts = self.mkProgStmts(self.filename, invs, _mk)
        #comment startFun(..argv[]) and add symbolic input
        stmts_ = []
        for stmt in stmts:
            if startFun in stmt and "argv" in stmt:
                # stmt = "//" + stmt
                # stmts_.append(stmt)
                for varname, (vartyp, (minV, maxV)) in inpsd.iteritems():
                    stmt = KLEE.mkSymbolic(varname, vartyp)
                    stmts_.append(stmt)
                    if minV is not None and maxV is not None:
                        stmts__ = KLEE.mkAssumeRanges(varname, minV, maxV)
                        stmts_.extend(stmts__)

                #klee_assume(x!=0 || y!=1); klee_assume(x!=2 || y!=3);
                if inps:
                    ss = inpsd.keys()
                    #so that assertions are in order
                    #(KLEE will give diff outputs based on order)
                    inps = sorted(inps)
                    stmts__ = KLEE.mkAssumeInps(ss, inps)
                    stmts_.extend(stmts__)
                    
                #call mainQ(inp0, ..);
                stmt = "{}({});".format(
                    startFun, ",".join(map(str, inpsd.iterkeys())))
                stmts_.append(stmt)
            else:
                stmts_.append(stmt)

        stmts = stmts_
            
        #add header
        stmts = ["#include <klee/klee.h>"] + stmts
        uid = str(hash(str(invs))).replace("-", "_")
        fname = "{}_{}.{}".format(self.filename, uid, "klee_assert.c")
        CM.vwrite(fname, '\n'.join(stmts))
        CM.vcmd("astyle -Y {}".format(fname))
        return fname

    @classmethod
    def _parse(cls, filename, startFun="mainQ", traceIndicator="//%%%traces:"):
        """
        Return 
        inpdecls = {'x':'int', 'y':'double', ..}
        invdecls = {'lineno' : {'x':'int'; 'y':'double'}}
        """
        def mkVarsDict(s):
            #%%%indicator double x , double y .. ->  {x: int, y: double}
            #where x and y are SAGE's symbolic variables
            contents = (x.split() for x in s.split(','))
            try:
                return OrderedDict(
                    (sage.all.var(k.strip()), t.strip()) for t,k in contents )
            except ValueError:
                return None

        inpdecls = OrderedDict()
        invdecls = OrderedDict()
        for i,l in enumerate(CM.iread(filename)):            
            i = i + 1
            l = l.strip()
            if not l: continue

            if startFun in l and l.endswith('{'):  #void startFun(int x, double y) {
                l = l.split('(')[1].split(')')[0]  #int x, double y
                inpdecls = mkVarsDict(l)

            elif l.startswith(traceIndicator):
                vars_d = mkVarsDict(stripTo(l, ':'))
                linePrefix = 'l' + str(i)
                invdecls[linePrefix] = vars_d
                
        assert invdecls
        assert (inpdecls is None or
                (isinstance(inpdecls, OrderedDict) and inpdecls)), inpdecls
        return inpdecls, invdecls


    @classmethod
    def mkPrintfArgs(cls, vars_d):
        """
        Return 2 strings representing 2 args to a printf stmt
        sage: vars_d = OrderedDict([('x','int'),('y','double')])
        sage: Src.mkPrintfArgs(vars_d)
        ('%d %g', 'x, y')
        """
        assert isinstance(vars_d, OrderedDict) and vars_d, vars_d
        p1 = []
        for k in vars_d:
            typ = vars_d[k]
            if isinstance(vars_d[k], tuple): #(typ, (minV, maxV))
                typ = vars_d[k][0]
                
            if typ == "int":
                a = "%d"
            else:
                a = "%g"
            p1.append(a)
        p1 = ' '.join(p1)
        p2 = ', '.join(map(str, vars_d.iterkeys()))
        return p1, p2
    
    @classmethod
    def mkPrintfs(cls, vars_d, linePrefix):
        """
        sage: vars_d = OrderedDict([('x','int'),('y','double')])
        sage: Src.mkPrintfs(vars_d, "l12")
        ['printf("l12: %d %g\\n", x, y);']
        """
        assert (isinstance(linePrefix, str) and
                linePrefix.startswith("l")), linePrefix
        p1, p2 = cls.mkPrintfArgs(vars_d)
        stmt = 'printf("{}: {}\\n", {});'.format(linePrefix, p1, p2)
        return [stmt]

    @classmethod
    def mkAsserts(cls, invs, linePrefix):
        stmts = []
        stmts.append("/* {}: DIG generated {} invs */"
                     .format(linePrefix, len(invs)))
        for inv in invs:
            assertStmt = "assert({}); /*DIG generated*/".format(inv)
            stmts.append(assertStmt)
        return stmts

    @classmethod
    def mkProgStmts(cls, filename, locs_d, mk_f):
        stmts = []
        for i, l in enumerate(CM.iread(filename)):
            i = i + 1
            l = l.strip()
            if not l: continue
            stmts.append(l)
            
            linePrefix = 'l' + str(i)
            if linePrefix in locs_d and locs_d[linePrefix]:
                stmts_ = mk_f(locs_d[linePrefix], linePrefix)
                stmts.extend(stmts_)
                
        return stmts
    
    @classmethod
    def instr(cls, filename, filePostfix, locs_d, mkStmts):
        stmts = cls.mkProgStmts(filename, locs_d, mkStmts)
        
        fname = filename + filePostfix
        CM.vwrite(fname, '\n'.join(stmts))
        CM.vcmd("astyle -Y {}".format(fname))
        return fname
