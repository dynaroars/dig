from collections import OrderedDict
import os.path
from sage.all import var as savar

import vu_common as CM
import settings
logger = CM.VLog('src')
logger.level = settings.logger_level  


import miscs
from cpa import RT   #Reachability Tool

class Src(object):
    def __init__(self, filename):
        assert os.path.isfile(filename), filename
        self.filename = filename

    def parse(self): return self._parse(self.filename)
    
    def instrDisproves(self, invs, invdecls, lineno):
        return self.instr(self.filename, ".dp.c",
                          invs, invdecls, lineno, self.mkDisproves)
    
    def instrAssertsRT(self, invs, inps, inps_d, invdecls, lineno, startFun="mainQ"):
        assert isinstance(invs, set) and invs, dinvs
        assert isinstance(inps, set), inps
        assert (inps_d is None or
                (isinstance(inps_d, OrderedDict) and inps_d)), inps_d

        
        #mk_f(invs, invdecls, lineno)            
        _mk = lambda myinvs, _, loc: RT.mkAssertInvs(myinvs, loc)
        stmts = self.mkProgStmts(self.filename, invs, invdecls, lineno, _mk)

        #comment startFun(..argv[]) and add symbolic input
        stmts_ = []
        for stmt in stmts:
            if startFun in stmt and "argv" in stmt:
                for varname, (vartyp, (minV, maxV)) in inps_d.iteritems():
                    stmt = RT.mkSymbolic(varname, vartyp)
                    stmts_.append(stmt)
                    if minV is not None and maxV is not None:
                        stmts__ = RT.mkAssumeRanges(varname, minV, maxV)
                        stmts_.extend(stmts__)

                #klee_assume(x!=0 || y!=1); klee_assume(x!=2 || y!=3);
                if inps:
                    stmts__ = RT.mkAssumeInps(inps)
                    stmts_.extend(stmts__)
                
                #call mainQ(inp0, ..);
                stmt = "{}({});".format(
                    startFun, ",".join(map(str, inps_d.iterkeys())))
                stmts_.append(stmt)
                
            elif (all(x in stmt for x in ['assert', '(', ')', ';']) and
                '//' not in stmt):
                
                stmt = RT.mkAssert(stmt);
                stmts_.append(stmt)
            else:
                stmts_.append(stmt)

        stmts = stmts_
            
        #add header, e.g., #include ...
        stmts = RT.mkHeaders() + stmts
        
        fname = self.filename + ".assert.c"
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
                    (savar(k.strip()), t.strip()) for t,k in contents )
            except ValueError:
                return None

        inpdecls, invdecls, lineno = OrderedDict(), OrderedDict(), None
        for i,l in enumerate(CM.iread(filename)):            
            i = i + 1
            l = l.strip()
            if not l: continue

            if startFun in l and l.endswith(' {'):  #void startFun(int x, double y) {
                l = l.split('(')[1].split(')')[0]  #int x, double y
                inpdecls = mkVarsDict(l)

            elif l.startswith(traceIndicator):
                invdecls = mkVarsDict(miscs.stripTo(l, ':'))
                lineno = i
                
        assert invdecls
        assert (inpdecls is None or
                (isinstance(inpdecls, OrderedDict) and inpdecls)), inpdecls
        assert lineno
        return inpdecls, invdecls, lineno


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
                
            a = "%d" if typ == "int" else "%g"
            p1.append(a)
        p1 = ' '.join(p1)
        p2 = ', '.join(map(str, vars_d.iterkeys()))
        return p1, p2

    @classmethod
    def mkDisproves(cls, invs, vars_d, lineno):
        """
        sage: vars_d = OrderedDict([('x','int'),('y','double')])
        sage: Src.mkPrintfVarStr(vars_d, 12)
        '12: %d %g\\n", x, y'
        """
        assert lineno > 0, lineno
        p1, p2 = cls.mkPrintfArgs(vars_d)
        vstr = '@ line {}: {}\\n", {}'.format(lineno, p1, p2)
        stmts = []
        for inv in invs:
            dStmt = "if(!((int){})) printf(\"disproved {} {});".format(
                inv, inv, vstr)
            stmts.append(dStmt)
        return stmts

    @classmethod
    def mkProgStmts(cls, filename, invs, invdecls, lineno, mk_f):
        assert invs, invs
        assert lineno > 0;
        
        stmts = []
        for i, l in enumerate(CM.iread(filename)):
            i = i + 1
            l = l.strip()
            if not l: continue
            stmts.append(l)
            
            if i == lineno:
                assert invdecls
                stmts_ = mk_f(invs, invdecls, lineno)
                stmts.extend(stmts_)
                
        return stmts
    
    @classmethod
    def instr(cls, filename, filePostfix, invs, invdecls, lineno, mkStmts):
        stmts = cls.mkProgStmts(filename, invs, invdecls, lineno, mkStmts)
        
        fname = filename + filePostfix
        CM.vwrite(fname, '\n'.join(stmts))
        CM.vcmd("astyle -Y {}".format(fname))
        return fname
