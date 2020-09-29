import pdb
from functools import partial
import os.path
from pathlib import Path

DBG = pdb.set_trace

tmpdir = Path("/var/tmp/")
logger_level = 2
DO_MP = True  # use multiprocessing
DO_SIMPLIFY = True  # simplify results, e.g., removing weaker invariants
DO_FILTER = True  # remove ieqs and min/max terms that unlikely interesting
DO_SS = True  # use symbolic states to check results
DO_EQTS = True  # support equalities
DO_IEQS = True  # support (octagonal) inequalities
DO_MINMAXPLUS = True  # support minmax-plus inequalities
DO_PREPOSTS = False  # support prepostconditions #TODO not well-tested
DO_INCR_DEPTH = True
DO_SOLVER_STATS = False  # collect solver usage stats

BENCHMARK_TIMEOUT = 15 * 60  # mins

INP_MAX_V = 300
SE_DEPTH_NOCHANGES_MAX = 3
SE_MAXDEPTH = 30
SOLVER_TIMEOUT = 3 * 1000  # secs
EQT_REDUCE_TIMEOUT = 20  # secs
EQT_RATE = 1.5
MAX_LARGE_COEF = 20
MAX_TERM = 200

LARGE_N = 200000  # powersum programs can go up to very large vals
TRACE_MULTIPLIER = 5
INP_RANGE_V = 4  # use more inp ranges when # of inputs is <= this
UTERMS = None  # terms that the user's interested in, e.g., "y^2 xy"

# Iequalities
IUPPER = 20  # t <= iupper
IUPPER_MP = 2  # for min/max ieqs
IDEG = 1  # deg (if 1 then linear)
ITERMS = 2  # octagonal
ICOEFS = 1  # from -ICOEFS to ICOEFS, e.g., -1,0,1

# options for full specs analysis
CTR_VAR = "Ct"  # counter variable contains this string
POST_LOC = "post"  # vtraceX_post  indicates postconditions

# Program Paths
SRC_DIR = Path(__file__).parent

TRACE_DIR = "traces"
SYMEXE_DIR = "symexe"
TRACE_INDICATOR = "vtrace"
MAINQ_FUN = "mainQ"

# Must be Java 8 because JPF requires Java 8
JAVA_HOME = Path(os.path.expandvars("$JAVA_HOME"))
JAVAC_CMD = JAVA_HOME / "bin/javac"
JAVA_CMD = JAVA_HOME / "bin/java"
assert JAVAC_CMD.is_file(), JAVAC_CMD
assert JAVA_CMD.is_file(), JAVA_CMD


class Java:
    SE_MIN_DEPTH = 7
    # SE_DEPTH_INCR = 20  # maxdepth = mindepth + depth_incr

    JAVA_INSTRUMENT_DIR = SRC_DIR / "java"
    ASM_JAR = JAVA_INSTRUMENT_DIR / "asm-all-5.2.jar"
    assert JAVA_INSTRUMENT_DIR.is_dir(), JAVA_INSTRUMENT_DIR
    assert ASM_JAR.is_file(), ASM_JAR
    CLASSPATH = f"{JAVA_INSTRUMENT_DIR}:{ASM_JAR}"

    JPF_HOME = Path(os.path.expandvars("$JPF_HOME")) / "jpf-core"
    JPF_JAR = JPF_HOME / "build/RunJPF.jar"
    assert JPF_JAR.is_file(), JPF_JAR
    JVM_FLAGS = "-Xmx1024m -ea"

    JPF_RUN = f"{JAVA_CMD} {JVM_FLAGS} -jar {JPF_JAR} " "{jpffile}"
    JPF_RUN = partial(JPF_RUN.format)

    COMPILE = f"{JAVAC_CMD} " "-g {filename} -d {tmpdir}"
    COMPILE = partial(COMPILE.format)

    INSTRUMENT = (
        f"{JAVA_CMD} -cp {CLASSPATH} " "Instrument {filename} {tracefile} {symexefile}"
    )
    INSTRUMENT = partial(INSTRUMENT.format)

    JAVA_RUN = f"{JAVA_CMD} " "-ea -cp {tracedir} {funname}"
    JAVA_RUN = partial(JAVA_RUN.format)


class C:
    GCC_CMD = "gcc"
    CIL_INSTRUMENT_DIR = SRC_DIR / "ocaml"
    assert CIL_INSTRUMENT_DIR.is_dir(), CIL_INSTRUMENT_DIR

    COMPILE = "{gcc} {filename} -o {tmpfile}"
    COMPILE = partial(COMPILE.format, gcc=GCC_CMD)

    INSTRUMENT_EXE = CIL_INSTRUMENT_DIR / "instr.exe"
    INSTRUMENT = "{instrument_exe} {filename} {symexefile} {tracefile}"
    INSTRUMENT = partial(INSTRUMENT.format, instrument_exe=INSTRUMENT_EXE)

    C_RUN = "{exe}"
    C_RUN = partial(C_RUN.format)

    SE_MIN_DEPTH = 20
    # SE_DEPTH_INCR = 5

    CIVL_HOME = Path(os.path.expandvars("$CIVL_HOME"))
    CIVL_JAR = CIVL_HOME / "lib" / "civl-1.20_5259.jar"
    CIVL_RUN = "{java} -jar {jar} verify -maxdepth={maxdepth}  {file}"
    CIVL_RUN = partial(CIVL_RUN.format, java=JAVA_CMD, jar=CIVL_JAR)


def setup(settings, args):
    import helpers.vcommon

    opts = []
    if args.nosimplify:
        if settings:
            settings.DO_SIMPLIFY = not args.nosimplify
        else:
            opts.append("-nosimplify")

    if args.nofilter:
        if settings:
            settings.DO_FILTER = not args.nofilter
        else:
            opts.append("-nofilter")

    if args.noss:
        if settings:
            settings.DO_SS = not args.noss
        else:
            opts.append("-noss")

    if args.nomp:
        if settings:
            settings.DO_MP = not args.nomp
        else:
            opts.append("-nomp")

    if args.noeqts:
        if settings:
            settings.DO_EQTS = not args.noeqts
        else:
            opts.append("-noeqts")

    if args.noieqs:
        if settings:
            settings.DO_IEQS = not args.noieqs
        else:
            opts.append("-noieqs")

    if args.nominmaxplus:
        if settings:
            settings.DO_MINMAXPLUS = not args.nominmaxplus
        else:
            opts.append("-nominmaxplus")

    if args.nopreposts:
        if settings:
            settings.DO_PREPOSTS = not args.nopreposts
        else:
            opts.append("-nopreposts")

    if args.noincrdepth:
        if settings:
            settings.DO_INCR_DEPTH = not args.noincrdepth
        else:
            opts.append("-noincredepth")

    if args.dosolverstats:
        if settings:
            settings.DO_SOLVER_STATS = args.dosolverstats
        else:
            opts.append("-dosolverstats")

    if 0 <= args.log_level <= 4:
        if settings:
            settings.logger_level = args.log_level
            settings.logger_level = helpers.vcommon.getLogLevel(settings.logger_level)
            mlog = helpers.vcommon.getLogger(__name__, settings.logger_level)
        else:
            opts.append(f"-log_level {args.log_level}")

    if args.inpMaxV and args.inpMaxV >= 1:
        if settings:
            settings.INP_MAX_V = args.inpMaxV
        else:
            opts.append(f"-inpMaxV {args.inpMaxV}")

    if args.iupper and args.iupper >= 1:
        if settings:
            settings.IUPPER = args.iupper
        else:
            opts.append(f"-iupper {args.iupper}")

    if args.ideg and args.ideg >= 1:
        if settings:
            settings.IDEG = args.ideg
        else:
            opts.append(f"-ideg {args.ideg}")

    if args.iterms and args.iterms >= 1:
        if settings:
            settings.ITERMS = args.iterms
        else:
            opts.append(f"-iterms {args.iterms}")

    if args.icoefs and args.icoefs >= 1:
        if settings:
            settings.ICOEFS = args.icoefs
        else:
            opts.append(f"-icoefs {args.icoefs}")

    if args.maxterm and args.maxterm >= 1:
        if settings:
            settings.MAX_TERM = args.maxterm
        else:
            opts.append(f"-maxterm {args.maxterm}")

    if args.uterms:
        if settings:
            settings.UTERMS = set(args.uterms.split())
        else:
            opts.append(f'-uterms "{args.uterms}"')  # not tested

    se_mindepth = None
    if args.se_mindepth and args.se_mindepth >= 1:
        if settings:
            se_mindepth = args.se_mindepth
        else:
            opts.append(f"-se_mindepth {args.se_mindepth}")

    if args.tmpdir:
        if settings:
            settings.tmpdir = Path(args.tmpdir)
            assert settings.tmpdir.is_dir()
        else:
            opts.append(f"-tmpdir {args.tmpdir}")

    return (mlog, se_mindepth) if settings else " ".join(opts)
