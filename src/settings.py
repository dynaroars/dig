import os.path

src_dir = None
tmpdir = "/var/tmp/"
logger_level = 3
doMP = True
INP_MAX_V = 300
SOLVER_TIMEOUT = 3
JPF_MIN_DEPTH = 9
JPF_DEPTH_INCR = 4  # jpfmaxdepth = jpfmindepth + jpfdepth_incr
EQT_RATE = 1.5
MAX_LARGE_COEFS = 50
MAX_TERM = 200
OCT_MAX_V = 10  # t <= 10
LARGE_N = 200000  # powersum programs can go up to very large vals
TRACE_MULTIPLIER = 5

# options for full specs analysis
CTR_VAR = 'Ct'  # counter variable contains this string
POST_LOC = 'post'  # vtraceX_post  indicates postconditions


# Program Paths

# Must be Java 8 because JPF requires Java 8
JAVA_HOME = os.path.expandvars("$JAVA_HOME")
JAVAC_CMD = os.path.join(JAVA_HOME, "bin/javac")
JAVA_CMD = os.path.join(JAVA_HOME, "bin/java")


JPF_HOME = os.path.join(os.path.expandvars("$JPF_HOME"), "jpf-core")
JPF_JAR = os.path.join(JPF_HOME, "build/RunJPF.jar")
JVM_FLAGS = "-Xmx1024m -ea"
JPF_CMD = "{} {} -jar {}".format(JAVA_CMD, JVM_FLAGS, JPF_JAR)
JPF_CMD1 = os.path.join(JPF_HOME, "bin/jpf")
