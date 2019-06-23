import os.path
import helpers.vcommon as CM
import settings
from ds import Symbs, DSymbs
mlog = CM.getLogger(__name__, settings.logger_level)


def parse(filename, tmpdir):
    assert os.path.isfile(filename), filename
    assert os.path.isdir(tmpdir), tmpdir

    baseName = os.path.basename(filename)  # c.class
    clsName, ext = os.path.splitext(baseName)  # c, class
    if ext == ".java":
        cmd = settings.COMPILE_RUN(filename=filename, tmpdir=tmpdir)
        rmsg, errmsg = CM.vcmd(cmd)
        assert not errmsg, "cmd: {} gives err:\n{}".format(cmd, errmsg)

        filename = os.path.join(tmpdir, clsName + ".class")
        baseName = os.path.basename(filename)

    # mkdir trace and jpf dirs
    def mkdir(name):
        d = os.path.join(tmpdir, name)
        os.mkdir(d)
        n = os.path.join(d, baseName)
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
    return (inp_decls, inv_decls, clsName, mainQName,
            jpfdir, jpffile, tracedir, tracefile)


def mk_JPF_runfile(clsName, symFun, dirName, nInps, maxInt, depthLimit):
    assert isinstance(clsName, str) and clsName, clsName
    assert isinstance(symFun, str) and symFun, symFun
    assert os.path.isdir(dirName), dirName
    assert nInps >= 0, nInps
    assert maxInt >= 0, depthLimit
    assert depthLimit >= 0, depthLimit

    symargs = ['sym'] * nInps
    symargs = '#'.join(symargs)
    stmts = [
        "target={}".format(clsName),
        "classpath={}".format(dirName),
        "symbolic.method={}.{}({})".format(clsName, symFun, symargs),
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

    filename = os.path.join(dirName, "{}_{}_{}.jpf"
                            .format(clsName, maxInt, depthLimit))
    assert not os.path.isfile(filename), filename
    CM.vwrite(filename, contents)
    return filename
