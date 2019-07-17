from functools import partial
import os.path

tmpdir = "/var/tmp/"
logger_level = 2
DO_EQTS = True
DO_IEQS = True
DO_MINMAXPLUS = True
DO_PREPOSTS = True
doMP = True
INP_MAX_V = 300
SOLVER_TIMEOUT = 5 * 1000  # 5 secs
EQT_SOLVER_TIMEOUT = 120  # secs
JPF_MIN_DEPTH = 9
JPF_DEPTH_INCR = 4  # jpfmaxdepth = jpfmindepth + jpfdepth_incr
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
SRC_DIR = os.path.dirname(
    os.path.realpath(os.path.expanduser(__file__)))
JAVA_INSTRUMENT_DIR = os.path.join(SRC_DIR, 'java')
ASM_JAR = os.path.join(JAVA_INSTRUMENT_DIR, "asm-all-5.2.jar")
assert os.path.isdir(JAVA_INSTRUMENT_DIR), JAVA_INSTRUMENT_DIR
assert os.path.isfile(ASM_JAR), ASM_JAR
CLASSPATH = "{}:{}".format(JAVA_INSTRUMENT_DIR, ASM_JAR)

# Must be Java 8 because JPF requires Java 8
JAVA_HOME = os.path.expandvars("$JAVA_HOME")
JAVAC_CMD = os.path.join(JAVA_HOME, "bin/javac")
JAVA_CMD = os.path.join(JAVA_HOME, "bin/java")
assert os.path.isfile(JAVAC_CMD), JAVAC_CMD
assert os.path.isfile(JAVA_CMD), JAVA_CMD

JPF_HOME = os.path.join(os.path.expandvars("$JPF_HOME"), "jpf-core")
JPF_JAR = os.path.join(JPF_HOME, "build/RunJPF.jar")
assert os.path.isfile(JPF_JAR), JPF_JAR
JVM_FLAGS = "-Xmx1024m -ea"

JPF_RUN = "{java} {flags} -jar {jar} {jpffile} > {tracefile}"
JPF_RUN = partial(JPF_RUN.format, java=JAVA_CMD, flags=JVM_FLAGS, jar=JPF_JAR)

COMPILE_RUN = "{javac} -g {filename} -d {tmpdir}"
COMPILE_RUN = partial(COMPILE_RUN.format, javac=JAVAC_CMD)

INSTRUMENT_RUN = "{java} -cp {cp} Instrument {filename}  {tracefile} {jpffile}"
INSTRUMENT_RUN = partial(INSTRUMENT_RUN.format, java=JAVA_CMD, cp=CLASSPATH)

JAVA_RUN = "{java} -ea -cp {tracedir} {clsname}"
JAVA_RUN = partial(JAVA_RUN.format, java=JAVA_CMD)


# tmpdirs, created inside tmpdir, e.g., /path/to/tmpdir/...

TRACE_DIR = "traces"
JPF_DIR = "jpf"


TRACE_INDICATOR = "vtrace"
MAINQ_FUN = "mainQ"
