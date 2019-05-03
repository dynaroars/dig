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
counterVar = 'Ct'  # counter variable contains this string
postLoc = 'post'  # vtraceX_post  indicates postconditions
