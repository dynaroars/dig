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
logger.printtime = settings.logger_printtime

# if settings.logger_level > 0:
#     logger.level = settings.logger_level - 1
# else:
#     logger.level = settings.logger_level

class KLEE(object):

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
        timeout = settings.solver_timeout
        kleeOpts = ("-allow-external-sym-calls "
                    "-solver-backend=z3 "
                    "-max-solver-time={}. "
                    "-max-time={}. "
                    "-no-output "
                    "-output-dir={} "
                    .format(timeout,timeout, kleeOutdir))

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
        dcexs = {}
        isSucc = True
        for line in lines:
            if all(x not in line for x in
                   ignoresDone + ignoresMiscs + ignoresRun):
                logger.detail("rs: {}".format(line))

            #input refuting ...: v1, v2
            if cls.cexStr in line and \
               all(x in line for x in ["loc", "inv", "inp", "cex"]):
                
                rs = cls.parseCex(line)
                loc = rs['loc']
                inv = rs['inv']
                
                #this could happen, not sure how though
                #e.g.,counterexample @ loc: l24 @ inv: t <= 10 @ cex: 20 16 340 @ inp
                inp = rs['inp'] if 'inp' in rs else None  
                cex = rs['cex']
                
                if loc not in dinps: dinps[loc] = {}
                if inv not in dinps[loc]: dinps[loc][inv] = set()

                if loc not in dcexs: dcexs[loc] = {}
                if inv not in dcexs[loc]: dcexs[loc][inv] = set()

                if inp: dinps[loc][inv].add(inp)
                dcexs[loc][inv].add(cex)
                
            elif any(s in line for s in [cls.haltStr, cls.failedStr]):
                isSucc = False

        return dinps, dcexs, isSucc
    

    def getDInps(self):
        obj = self.compile()
        rs = self.run(obj)
        dinps, dcexs, isSucc = self.parseLog(rs)
        return dinps, dcexs, isSucc

    @classmethod
    def parseCex(cls, s):
        """
        s: could be incomplete in the case SMT solver timeout

        sage: KLEE.parseCex("counterexample @ loc : l8 @ inv : 0 @ inp : 512 65 @ cex : 1 78 9 1")
        {'cex': ['1', '78', '9'], 'inp': ['512', '65'], 'inv': '0', 'loc': 'l8'}
        sage: KLEE.parseCex("counterexample @ loc : l0 @ inv : x + 1 > 0 @ inp : 512 65")
        {'inp': ['512', '65'], 'inv': 'x + 1 > 0', 'loc': 'l0'}
        sage: KLEE.parseCex("counterexample @ loc : l0 @ inv: 0 + 1 > 0")
        {'inv': '0 + 1 > 0', 'loc': 'l0'}
        """
        parts = s.split("@")
        #[[' loc ', ' l8 '], [' inv ', ' 0 '], [' inp ', ' 512 65 '], [' cex ', ' 1 78 9 ']]
        parts = [p.split(':') for p in parts if ':' in p]
        #[('loc', ['l8']), ('inv', ['0']), ('inp', ['512', '65']), ('cex', ['1', '78', '9'])]
        parts = [(p[0].strip(),p[1].strip()) for p in parts]


        singleSet = set(['loc', 'inv'])
        #[('loc', 'l8'), ('inv', '0'), ('inp', ['512', '65']), ('cex', ['1', '78', '9'])]
        d = dict((key, (contents if key in singleSet else tuple(contents.split())))
                 for key, contents in parts)

        assert d['loc']
        assert d['inv']
        assert d['inp']
        assert d['cex']
        return d

    #Make klee statements
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
    def mkAssumeInps(cls, ss, inps):
        """
        inps = [(1,2,3), (4,5,6)]
        ss = ('x','y','z')

        klee_assume(! ( (x==0 && y==1) || (x==2 && y==3) || ..))

        klee_assume(x!=0 || y!=1);
        klee_assume(x!=2 || y!=3);
        """

        mkOrExpr = lambda inp: "({})".format(
            " || ".join("{} != {}".format(vname, vval)
                        for vname, vval in zip(ss, inp)))
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
    def mkAssertInvs(cls, invs, loc, inpParts, invParts):
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
        
        (inpPart1,inpPart2) = inpParts
        (invPart1,invPart2) = invParts        
        if inpPart1 and inpPart2:
            s = 'printf("{} @ loc: {} @ inv: {} @ cex: {} @ inp: {}\\n", {});\n'
            _mkPrintf = lambda inv: s.format(cls.cexStr, loc, inv,
                                             invPart1, inpPart1, invPart2 + ", " + inpPart2)
        else:
            s = 'printf("{} @ loc: {} @ inv: {} @ cex: {} \\n", {});\n'
            _mkPrintf = lambda inv: s.format(cls.cexStr, loc, inv, invPart1, invPart2)

        _mkKleeAssert = lambda inv: (
            "if (!({})){{".format(inv) + _mkPrintf(inv) + "klee_assert(0);\n}")
            
        stmts = []
        for inv in invs:
            assertStmt = _mkKleeAssert(inv)
            stmts.append(assertStmt)
        return stmts
    
    
