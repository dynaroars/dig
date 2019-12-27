import pdb
from pathlib import Path
import helpers.vcommon as CM
import settings
from data.miscs import Symbs, DSymbs

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


class Src:
    def __init__(self, filename, tmpdir):
        assert filename.is_file(), filename
        assert tmpdir.is_dir(), tmpdir

        filename, basename, funname = self.check(filename, tmpdir)

        tracedir = self.mkdir(tmpdir / settings.TRACE_DIR)
        tracefile = tracedir / basename
        symexedir = self.mkdir(tmpdir / settings.SYMEXE_DIR)
        symexefile = symexedir / basename

        cmd = self.instrument_cmd(filename=filename,
                                  tracefile=tracefile,
                                  symexefile=symexefile)
        rmsg, errmsg = CM.vcmd(cmd)
        assert not errmsg, "'{}': {}".format(cmd, errmsg)

        inp_decls, inv_decls, mainQ_name = self.parse_type_info(rmsg)

        self.filename, self.basename, self.funname = filename, basename, funname
        self.tracedir, self.tracefile = tracedir, tracefile
        self.symexedir, self.symexefile = symexedir, symexefile
        self.inp_decls, self.inv_decls, self.mainQ_name = \
            inp_decls, inv_decls, mainQ_name

    def parse_type_info(self, msg):
        # vtrace2: I x, I y, I q, I r,
        # vtrace1: I q, I r, I a, I b, I x, I y,
        # mainQ_cohendiv: I x, I y,
        lines = [l.split(':') for l in msg.split('\n')
                 if settings.MAINQ_FUN in l
                 or settings.TRACE_INDICATOR in l]

        lines = [(fun.strip(), Symbs.mk(sstyps)) for fun, sstyps in lines]

        # mainQ
        inp_decls = [(fun, symbs) for fun, symbs in lines
                     if fun.startswith(settings.MAINQ_FUN)]
        assert len(inp_decls) == 1

        inp_decls = inp_decls[0]
        mainQ_name, inp_decls = inp_decls[0], inp_decls[1]
        inv_decls = DSymbs([(fun, symbs) for fun, symbs in lines
                            if fun.startswith(settings.TRACE_INDICATOR)])

        return inp_decls, inv_decls, mainQ_name,

    def mkdir(self, d):
        assert not d.exists(), d
        d.mkdir()
        return d


class Java(Src):

    def check(self, filename, tmpdir):
        basename = Path(filename.name)  # c.class
        funname = basename.stem  # c

        if basename.suffix == ".java":
            cmd = settings.Java.COMPILE(filename=filename, tmpdir=tmpdir)
            rmsg, errmsg = CM.vcmd(cmd)
            assert not errmsg, "cmd: {} gives err:\n{}".format(cmd, errmsg)
            filename = (tmpdir / funname).with_suffix('.class')
            basename = Path(filename.name)

        return filename, basename, funname

    @property
    def instrument_cmd(self):
        return settings.Java.INSTRUMENT

    def mk_JPF_runfile(funname, symfun, dirname, nInps, maxInt, depthLimit):
        assert isinstance(funname, str) and funname, funname
        assert isinstance(symfun, str) and symfun, symfun
        assert dirname.is_dir(), dirname
        assert nInps >= 0, nInps
        assert maxInt >= 0, depthLimit
        assert depthLimit >= 0, depthLimit

        symargs = ['sym'] * nInps
        symargs = '#'.join(symargs)
        stmts = [
            "target={}".format(funname),
            "classpath={}".format(dirname),
            "symbolic.method={}.{}({})".format(funname, symfun, symargs),
            "listener=gov.nasa.jpf.symbc.InvariantListenerVu",
            "vm.storage.class=nil",
            "search.multiple_errors=true",
            "symbolic.min_int={}".format(-maxInt),
            "symbolic.max_int={}".format(maxInt),
            "symbolic.min_long={}".format(-maxInt),
            "symbolic.max_long={}".format(maxInt),
            "symbolic.min_short={}".format(-maxInt),
            "symbolic.max_short={}".format(maxInt),
            "symbolic.min_float={}.0f".format(-maxInt),
            "symbolic.max_float={}.0f".format(maxInt),
            "symbolic.min_double={}.0".format(-maxInt),
            "symbolic.max_double={}.0".format(maxInt),
            "symbolic.dp=z3bitvector",
            "search.depth_limit={}".format(depthLimit)]
        contents = '\n'.join(stmts)

        filename = dirname / "{}_{}_{}.jpf".format(funname, maxInt, depthLimit)

        assert not filename.is_file(), filename
        CM.vwrite(filename, contents)
        return filename


class C(Src):

    def __init__(self, filename, tmpdir):
        super().__init__(filename, tmpdir)

        self.traceexe = self.tracefile.with_suffix('.exe')
        self.compile_test(self.tracefile, self.traceexe)

    def check(self, filename, tmpdir):
        basename = Path(filename.name)
        funname = basename.stem
        self.compile_test(filename, tmpdir / "{}.exe".format(funname))
        return filename, basename, funname

    @classmethod
    def compile_test(cls, filename, out):
        cmd = settings.C.COMPILE(filename=filename, tmpfile=out)
        rmsg, errmsg = CM.vcmd(cmd)
        assert not errmsg, "cmd: {} gives err:\n{}".format(cmd, errmsg)
        assert out.exists(), out

    @property
    def instrument_cmd(self):
        return settings.C.INSTRUMENT
