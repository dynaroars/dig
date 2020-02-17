import pdb
from functools import partial
import os.path
from pathlib import Path
DBG = pdb.set_trace

tmpdir = Path("/var/tmp/")
logger_level = 2
DO_EQTS = True
DO_IEQS = True
DO_MINMAXPLUS = True
DO_PREPOSTS = True
DO_RMTMP = True  # remove temporary dir
doMP = True
INP_MAX_V = 300
SOLVER_TIMEOUT = 5 * 1000  # 5 secs
EQT_SOLVER_TIMEOUT = 120  # secs
EQT_RATE = 1.5
MAX_LARGE_COEF = 50
MAX_TERM = 200
OCT_MAX_V = 10  # t <= 10
LARGE_N = 200000  # powersum programs can go up to very large vals
TRACE_MULTIPLIER = 5
INP_RANGE_V = 4  # use more inp ranges when # of inputs is <= this

# options for full specs analysis
CTR_VAR = 'Ct'  # counter variable contains this string
POST_LOC = 'post'  # vtraceX_post  indicates postconditions

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
    SE_MIN_DEPTH = 9
    SE_DEPTH_INCR = 4  # maxdepth = mindepth + depth_incr

    JAVA_INSTRUMENT_DIR = SRC_DIR / "java"
    ASM_JAR = JAVA_INSTRUMENT_DIR / "asm-all-5.2.jar"
    assert JAVA_INSTRUMENT_DIR.is_dir(), JAVA_INSTRUMENT_DIR
    assert ASM_JAR.is_file(), ASM_JAR
    CLASSPATH = "{}:{}".format(JAVA_INSTRUMENT_DIR, ASM_JAR)

    JPF_HOME = Path(os.path.expandvars("$JPF_HOME")) / "jpf-core"
    JPF_JAR = JPF_HOME / "build/RunJPF.jar"
    assert JPF_JAR.is_file(), JPF_JAR
    JVM_FLAGS = "-Xmx1024m -ea"

    JPF_RUN = "{java} {flags} -jar {jar} {jpffile} > {tracefile}"
    JPF_RUN = partial(JPF_RUN.format, java=JAVA_CMD,
                      flags=JVM_FLAGS, jar=JPF_JAR)

    COMPILE = "{javac} -g {filename} -d {tmpdir}"
    COMPILE = partial(COMPILE.format, javac=JAVAC_CMD)

    INSTRUMENT = ("{java} -cp {cp} Instrument {filename} "
                  "{tracefile} {symexefile}")
    INSTRUMENT = partial(INSTRUMENT.format, java=JAVA_CMD, cp=CLASSPATH)

    JAVA_RUN = "{java} -ea -cp {tracedir} {funname}"
    JAVA_RUN = partial(JAVA_RUN.format, java=JAVA_CMD)


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
    SE_DEPTH_INCR = 4

    CIVL_HOME = Path(os.path.expandvars("$CIVL_HOME")) 
    CIVL_JAR = CIVL_HOME / "lib" / "civl-1.20_5259.jar"
    # -seed={seed}
    CIVL_RUN = "{java} -jar {jar} verify -maxdepth={maxdepth}  {file} > {tracefile}"
    CIVL_RUN = partial(CIVL_RUN.format, java=JAVA_CMD, jar=CIVL_JAR)
