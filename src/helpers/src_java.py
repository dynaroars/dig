import pdb
from pathlib import Path
import helpers.vcommon as CM
import settings
from data.miscs import Symbs, DSymbs

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.logger_level)


def parse(filename, tmpdir):
    assert filename.is_file(), filename
    assert tmpdir.is_dir(), tmpdir

    basename = Path(filename.name)  # c.class
    clsname = basename.stem
    ext = basename.suffix  # .class

    if ext == ".java":
        cmd = settings.COMPILE_RUN(filename=filename, tmpdir=tmpdir)
        rmsg, errmsg = CM.vcmd(cmd)
        assert not errmsg, "cmd: {} gives err:\n{}".format(cmd, errmsg)
        filename = (tmpdir / clsname).with_suffix('.class')
        basename = Path(filename.name)

    # mkdir trace and jpf dirs

    def mkdir(name):
        d = tmpdir / name
        d.mkdir()
        n = d / basename
        return d, n

    tracedir, tracefile = mkdir(settings.TRACE_DIR)
    jpfdir, jpffile = mkdir(settings.JPF_DIR)
    cmd = settings.INSTRUMENT_RUN(
        filename=filename, tracefile=tracefile, jpffile=jpffile)

    rmsg, errmsg = CM.vcmd(cmd)

    assert not errmsg, "'{}': {}".format(cmd, errmsg)
    # vtrace2: I x, I y, I q, I r,
    # vtrace1: I q, I r, I a, I b, I x, I y,
    # mainQ_cohendiv: I x, I y,
    lines = [l.split(':') for l in rmsg.split('\n') if l]
    lines = [(fun.strip(), Symbs.mk(sstyps)) for fun, sstyps in lines]

    # mainQ
    inp_decls = [(fun, symbs) for fun, symbs in lines
                 if fun.startswith(settings.MAINQ_FUN)]
    assert len(inp_decls) == 1
    inp_decls = inp_decls[0]
    mainQName, inp_decls = inp_decls[0], inp_decls[1]
    inv_decls = DSymbs([(fun, symbs) for fun, symbs in lines
                        if fun.startswith(settings.TRACE_INDICATOR)])
    return (inp_decls, inv_decls, clsname, mainQName,
            jpfdir, jpffile, tracedir, tracefile)


def mk_JPF_runfile(clsname, symfun, dirname, nInps, maxInt, depthLimit):
    assert isinstance(clsname, str) and clsname, clsname
    assert isinstance(symfun, str) and symfun, symfun
    assert dirname.is_dir(), dirname
    assert nInps >= 0, nInps
    assert maxInt >= 0, depthLimit
    assert depthLimit >= 0, depthLimit

    symargs = ['sym'] * nInps
    symargs = '#'.join(symargs)
    stmts = [
        "target={}".format(clsname),
        "classpath={}".format(dirname),
        "symbolic.method={}.{}({})".format(clsname, symfun, symargs),
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

    filename = dirname / "{}_{}_{}.jpf".format(clsname, maxInt, depthLimit)

    assert not filename.is_file(), filename
    CM.vwrite(filename, contents)
    return filename
