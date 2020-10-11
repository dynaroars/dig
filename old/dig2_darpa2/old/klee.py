"""
Given as input a Klee src file,  returns a set of inputs [[v1,...], [v3,..]] 
that hit the desired locations
"""

import os
import subprocess as sp
import shutil
import vu_common as CM
import settings
logger = CM.VLog('klee')
logger.level = settings.logger_level

class RT(object):

    cexStr = "counterexample"
    haltStr = "halting execution, dumping remaining states"
    failedStr = "failed."
    
    def __init__(self, filename, tmpdir):
        assert os.path.isfile(filename)
        assert os.path.isdir(tmpdir)
        
        self.filename = CM.getpath(filename)
        import tempfile
        self.tmpdir = tmpdir
        
        logger.detail("running KLEE on {}, tmpdir {}"
                      .format(self.filename, self.tmpdir))
                      
    def compile(self):

        #compile file with llvm
        includePath = "~/Src/Devel/KLEE/klee/include"
        clangOpts =  "-emit-llvm -c"
        obj = os.path.basename(self.filename) + os.extsep + 'o'
        obj = os.path.join(self.tmpdir, obj)

        cmd = ("clang -I {} {} {} -o {}"
               .format(includePath, clangOpts, self.filename, obj))
        logger.detail("$ {}".format(cmd))

        rs,rsErr = CM.vcmd(cmd)
        assert not rs, rs
        assert "clang" not in rsErr and "error" not in rsErr, rsErr
        if rsErr: logger.detail(rsErr)
        return obj

    def run(self, obj):
        #run klee and monitor its output
        kleeOutdir = "{}-klee-out".format(obj)
        if os.path.exists(kleeOutdir): shutil.rmtree(kleeOutdir)

        #"-optimize "  causes problems with prod4br
        timeout = 5
        kleeOpts = ("--allow-external-sym-calls "                    
                    "--max-time={}. "
                    "-output-dir={} "
                    .format(timeout,kleeOutdir))

        cmd = "klee {} {}".format(kleeOpts, obj).strip()
        logger.detail("$ {}".format(cmd))
        
        proc = sp.Popen(cmd,shell=True,stdout=sp.PIPE, stderr=sp.STDOUT)
        rs, rsErr = proc.communicate()
        assert not rsErr, rsErr
        return rs

    @classmethod
    def parseLog(cls, rs):
        """
        parse Klee run log
        """
        if not rs: return []

        ignoresDone = ['KLEE: done: total instructions',
                        'KLEE: done: completed paths',
                        'KLEE: done: generated tests']

        ignoresRun = [ 
            'KLEE: WARNING: undefined reference to function: printf',
            'KLEE: WARNING ONCE: calling external: printf',
            'KLEE: ERROR: ASSERTION FAIL: 0',
            'KLEE: ERROR: (location information missing) ASSERTION FAIL: 0'
            ]

        ignoresMiscs = ['KLEE: NOTE: now ignoring this error at this location',
                         'GOAL: ']        

        lines = [line for line in rs.split('\n') if line]
        
        dinps = {}
        isSucc = True
        for line in lines:
            if all(x not in line for x in
                   ignoresDone + ignoresMiscs + ignoresRun):
                logger.detail("rs: {}".format(line))

            #input refuting ...: v1, v2
            if cls.cexStr in line:
                loc, inv, inp = cls.parseCex(line)
                if loc not in dinps: dinps[loc] = {}
                if inv not in dinps[loc]: dinps[loc][inv] = set()
                dinps[loc][inv].add(inp)
                
            elif any(s in line for s in [cls.haltStr, cls.failedStr]):
                isSucc = False

        return dinps, isSucc
    

    def getDInps(self):
        obj = self.compile()
        rs = self.run(obj)
        dinps, isSucc = self.parseLog(rs)
        return dinps, isSucc

    @classmethod
    def parseCex(cls, s):
        """
        sage: KLEE.parseCex("counterexample @ l8 @ 0 : 512 65")
        ('l8', '0', ('512', '65'))

        sage: KLEE.parseCex("counterexample @ l0 @ 0 + 1 > 0: 512 65")
        ('l0', '0 + 1 > 0', ('512', '65'))

        sage: KLEE.parseCex("counterexample @ l0 @ 0 + 1 > 0")
        ('l0', '0 + 1 > 0', None)
        """
        assert cls.cexStr in s, s

        if ":" in s:
            p1,p2 = s.split(":")
            inp = tuple(p2.strip().split())
        else:
            p1 = s
            inp = None
        _,loc,inv = map(lambda x: x.strip(), p1.strip().split("@"))
        
        assert loc, loc
        assert inv, inv
        if ':' in s: assert inp
        else: assert inp is None

        return loc, inv, inp
        

    #Make statements
    @classmethod
    def mkHeaders(cls):
        return ["#include <klee/klee.h>"]
    
    @classmethod
    def mkSymbolic(cls, varname, vartyp):
        """
        vartype varname;
        klee_make_symbolic(&vartype, sizeof(var1), "varname");
        """
        vdeclStr = "{} {};".format(vartyp, varname)
        ksymStr = ('klee_make_symbolic(&{}, sizeof({}), "{}");'
                   .format(varname, varname, varname))
        return vdeclStr + "\n" + ksymStr
    

    @classmethod
    def mkAssumeInps(cls, inps):
        """
        klee_assume(! ( (x==0 && y==1) || (x==2 && y==3) || ..))

        klee_assume(x!=0 || y!=1);
        klee_assume(x!=2 || y!=3);
        """

        mkOrExpr = lambda inp: "({})".format(
            " || ".join("{} != {}".format(vname, vval)
                      for vname, vval in inp.iteritems()))
        mkAssumeOr = lambda inp: cls.mkAssume(mkOrExpr(inp))
        return map(mkAssumeOr, inps)

    @classmethod
    def mkAssumeRanges(cls, varname, minV, maxV):
        assert minV <= maxV, (minV, maxV)
        if minV == maxV:
            stmts = [cls.mkAssume("{} == {}".format(minV, varname))]
        else:
            stmt_gt = cls.mkAssume("{} <= {}".format(minV, varname))
            stmt_lt = cls.mkAssume("{} <= {}".format(varname, maxV))
            stmts = [stmt_gt, stmt_lt]
        return stmts
    
    @classmethod
    def mkAssume(cls, s): return  "klee_assume({});".format(s)
        

    @classmethod
    def mkAssertInvs(cls, invs, loc, (p1,p2)):
        """
        sage: print '\n'.join(KLEE.mkAssertInvs(["z>=0", "k==1"], "l2", (None, None)))
        if (!(z>=0)){printf("counterexample @ l2 @ z>=0\n");
        klee_assert(0);
        }
        if (!(k==1)){printf("counterexample @ l2 @ k==1\n");
        klee_assert(0);
        }

        sage: print '\n'.join(KLEE.mkAssertInvs(["z>=0", "k==1"], "l2", ("%d, %g","x, y")))
        if (!(z>=0)){printf("counterexample @ l2 @ z>=0: %d, %g\n", x, y);
        klee_assert(0);
        }
        if (!(k==1)){printf("counterexample @ l2 @ k==1: %d, %g\n", x, y);
        klee_assert(0);
        }
        """

        if p1 and p2:
            s = 'printf("{} @ {} @ {}: {}\\n", {});\n'
            _mkPrintf = lambda inv: s.format(cls.cexStr, loc, inv, p1, p2)
        else:
            s = 'printf("{} @ {} @ {}\\n");\n'
            _mkPrintf = lambda inv: s.format(cls.cexStr, loc, inv)

        _mkKleeAssert = lambda inv: ("if (!({})){{".format(inv) +
                                     _mkPrintf(inv) + 
                                     "klee_assert(0);\n}")
        stmts = []
        for inv in invs:
            assertStmt = _mkKleeAssert(inv)
            stmts.append(assertStmt)
        return stmts
    
    
