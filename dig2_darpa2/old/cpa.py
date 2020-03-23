"""
Given as input a Klee src file,  returns a set of inputs [[v1,...], [v3,..]] 
that hit the desired locations
"""
import os
import subprocess as sp
import shutil
import vu_common as CM
import settings
logger = CM.VLog('cpa')
logger.level = settings.logger_level

class RT(object):
    assume_f = "__VERIFIER_assume"
    error_f = "ERROR: __VERIFIER_error();"
    
    cexStr = "counterexample"
    
    def __init__(self, filename, maxtime, tmpdir):
        assert os.path.isfile(filename)
        assert os.path.isdir(tmpdir)
        
        self.filename = CM.getpath(filename)
        import tempfile
        self.tmpdir = tmpdir
        self.maxtime = maxtime
        
        logger.detail("running CPA on {}, tmpdir {}"
                      .format(self.filename, self.tmpdir))
                      
    def run(self, obj):
        outdir = "{}-cpa-out".format(obj)
        if os.path.exists(outdir): shutil.rmtree(outdir)

        prog = "/home/tnguyen/Src/Devel/CPA/scripts/cpa.sh"
        timeout = self.maxtime

        opts = ("-predicateAnalysis-bitprecise "
                "-preprocess "
                "-nolog "
                "-disable-java-assertions "
                "-timelimit {} "
                "-outputpath {} "
                .format(timeout, outdir))
        
        cmd = "{} {} {}".format(prog, opts, obj).strip()
        logger.detail("$ {}".format(cmd))
        
        proc = sp.Popen(cmd,shell=True,stdout=sp.PIPE, stderr=sp.STDOUT)
        rs, rsErr = proc.communicate()
        assert not rsErr, rsErr
        assert rs
        return cmd, rs, outdir

    @classmethod
    def parseLog(cls, rs, cmd, outdir):
        """
        parse run log
        Running CPAchecker with default heap size (1200M). Specify a larger value with -heap if you have more RAM.
        Running CPAchecker with default stack size (1024k). Specify a larger value with -stack if needed.
        Verification result: FALSE. Property violation (assertion in line 7) found by chosen configuration.
        More details about the verification run can be found in the directory "/var/tmp/DIG2_L84bTq/prod4br.c.assert.c-cpa-out".
        Run /home/tnguyen/Src/Devel/CPAchecker-1.6.1-unix/scripts/report-generator.py to show graphical report.
        """

        assert rs, rs
        assert cmd, cmd
        assert os.path.isdir(outdir), outdir

        statStr = 'Verification result:'
        ignoresStart = [statStr,
                        'Running CPAchecker with default',
                        'Verification result:',
                        'More details about the verification']
        ignoresEnd = ['to show graphical report']
        lines = [line for line in rs.split('\n') if line]

        #output unrecognized lines
        ukLines = [l for l in lines
                   if (all(not l.startswith(x) for x in ignoresStart)
                       and all(not l.endswith(x) for x in ignoresEnd))]
        if ukLines:
            logger.detail("rs: {}".format('\n'.join(ukLines)))

        #status
        for statLine in lines:
            if statLine.startswith(statStr):
                break

        if statStr not in statLine:
            logger.warn("'{}': has no result (probably timeout)".format(cmd))
            print rs

        inps = []

        _af = lambda f: (f.endswith('assignment.txt')
                         and f.startswith('Counterexample') )
        
        if "FALSE" in statLine: #reached (disproved)
            assert any(f.startswith("Counterexample")
                       for f in os.listdir(outdir))

            cexFiles = [f for f in os.listdir(outdir) if _af(f)]
            assert len(cexFiles) == 1, outdir

            for cf in cexFiles:
                inp = cls.parseCex(os.path.join(outdir,cf))
                inps.append(inp)
            proved = False
            
        else:
            assert all(not _af(f) for f in os.listdir(outdir)), outdir
            proved = True if "TRUE" in statLine else None #timeout 
            
        return proved, inps

    def getDInps(self):
        cmd, rs, outdir = self.run(self.filename)
        proved, inps = self.parseLog(rs, cmd, outdir)
        return proved, inps

    @classmethod
    def parseCex(cls, cexFile):
        """
        sage: KLEE.parseCex("counterexample @ l8 @ 0 : 512 65")
        ('l8', '0', ('512', '65'))

        sage: KLEE.parseCex("counterexample @ l0 @ 0 + 1 > 0: 512 65")
        ('l0', '0 + 1 > 0', ('512', '65'))

        sage: KLEE.parseCex("counterexample @ l0 @ 0 + 1 > 0")
        ('l0', '0 + 1 > 0', None)

        __VERIFIER_nondet_int@2: 4294966300
        __VERIFIER_nondet_int@3: 0
        main::__CPAchecker_TMP_0@3: 1
        main::__CPAchecker_TMP_1@3: 1
        main::__CPAchecker_TMP_2@3: 1
        main::__CPAchecker_TMP_3@3: 1
        main::x@3: 4294966300
        main::y@3: 0
        mainQ::x@2: 4294966300
        mainQ::y@2: 0

        __VERIFIER_nondet_int@2: 2
        __VERIFIER_nondet_int@3: 2
        main::__CPAchecker_TMP_0@3: 1
        main::__CPAchecker_TMP_1@3: 1
        main::__CPAchecker_TMP_2@3: 1
        main::__CPAchecker_TMP_3@3: 1
        main::x@3: 2
        main::y@3: 2
        mainQ::a@3: 2
        mainQ::b@3: 2
        mainQ::p@3: 1
        mainQ::x@2: 2
        mainQ::y@2: 2

        """
        assert os.path.isfile(cexFile)

        def _parse(s):
            """
            main::x@3: 2 => x,2
            """
            s = s.split('::')[1]  #x@3:2
            vname, rest = s.split('@')
            vval = rest.split(':')[1].strip()
            return vname, vval

        
        inp = {}
        lines = list(CM.iread_strip(cexFile))
        for l in lines:
            if '__' in l:  #__CPAchecker_TMP_3@3: 1 ...
                continue 
            if l.startswith("main::"): #main::x@3: 7
                vname, vval = _parse(l)

                assert vname not in inp, '\n'.join(lines)
                inp[vname] = vval
                
        return inp
        

    #Make statements
    @classmethod
    def mkHeaders(cls):
        return ["extern void __VERIFIER_error();",
                "extern void {}();".format(cls.assume_f),
                "extern int __VERIFIER_nondet_int();"]
    
    @classmethod
    def mkSymbolic(cls, varname, vartyp):
        """
        vartype varname = __VERIFIER_nondet_int();
        """
        assert vartyp == "int", vartyp
        
        vdeclStr = "{} {} = __VERIFIER_nondet_int();".format(vartyp, varname)
        return vdeclStr

    @classmethod
    def mkAssumeInps(cls, inps):
        """
        assume_f(! ( (x==0 && y==1) || (x==2 && y==3) || ..))

        assume_f(x!=0 || y!=1);
        assume_f(x!=2 || y!=3);
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
    def mkAssume(cls, s): return  "{}({});".format(cls.assume_f, s)

    @classmethod
    def mkAssert(cls, s):
        """
        assert(f);  => assume(f);
        """
        s = s[s.find('(') + 1 : s.rfind(')')].strip()
        return cls.mkAssume(s)

    @classmethod
    def mkAssertInvs(cls, invs, loc):
        _mkAssert = lambda inv: ("if (!({})){{".format(inv) +
                                 "{}\n}}".format(cls.error_f))
        stmts = []
        for inv in invs:
            assertStmt = _mkAssert(inv)
            stmts.append(assertStmt)
        return stmts
    
    



#/home/tnguyen/Src/Devel/CPA/scripts/cpa.sh -predicateAnalysis-bitprecise -preprocess -nolog -disable-java-assertions -timelimit 5 -outputpath /var/tmp/DIG2_jUu2bE/knuth.c.assert.c-cpa-out  /var/tmp/DIG2_jUu2bE/knuth.c.assert.c
#Assertion
