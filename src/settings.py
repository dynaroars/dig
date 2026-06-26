import pdb
from functools import partial
from pathlib import Path

DBG = pdb.set_trace

TMPDIR = Path("/var/tmp/")
LOGGER_LEVEL = 3
DO_MP = True  # use multiprocessing
DO_SIMPLIFY = True  # simplify results, e.g., removing weaker invariants
DO_FILTER = True  # remove ieqs and min/max terms that unlikely interesting
DO_SS = True  # use symbolic states to check results
DO_EQTS = True  # support equalities
DO_IEQS = True  # support (octagonal) inequalities
DO_CONGRUENCES = True  # support congruence relations
DO_ARRAYS = True  # support array relations
DO_MINMAXPLUS = True  # support minmax-plus inequalities
DO_INCR_DEPTH = True
DO_SOLVER_STATS = False  # collect solver usage stats
WRITE_VTRACES = None  # write vtraces to csv
WRITE_SSTATES = None  # write symbolic states to a json file
READ_SSTATES = None  # read symbolic states from a json file
BENCHMARK_TIMEOUT = 15 * 60  # mins

N_RAND_INPS = 100  # number of random inputs, only used when DO_SS is False
INP_MAX_V = 300
SE_DEPTH_NOCHANGES_MAX = 3
SE_MAX_DEPTH = 30
SE_MAX_DEPTH_PYTHON = 8  # default for --python_symex; overridden by --se_maxdepth
# Deterministic z3 work-unit budget: the *real* cutoff for solver calls.
# Unlike wall-clock timeout, rlimit counts solver work, so results are
# reproducible regardless of CPU contention under multiprocessing.
# Calibrated to ~3s of CPU work on a typical core (see create_solver).
SOLVER_RLIMIT = 15_000_000
EQT_RATE = 1.5
# Groebner-basis reduction (Miscs.reduce_eqts) can hang on degree-2/many-var
# candidate eqts (e.g. egcd, 8 vars). Bound it; on timeout we fall back to the
# unreduced eqts, which is reduce_eqts's documented behavior anyway.
GROEBNER_TIMEOUT = 5  # secs
UGLY_FACTOR = 20  # remove equalities that have lots of terms and "large" coefficients
MAX_TERM = 200

TRACE_MAX_VAL = 1_000_000_000
TRACE_MULTIPLIER = 5
INP_RANGE_V = 4  # use more inp ranges when # of inputs is <= this
UTERMS = None  # terms that the user's interested in, e.g., "y^2 xy"

# Iequalities
IUPPER = 50  # t <= iupper
IUPPER_MMP = 1  # for min/max ieqs
# Cap on the # of operands inside a min/max-plus term, i.e. max(y1,..,yk).
# Term generation is O(n*2^n) in the # of vars; without a cap, programs with
# many vars (e.g. egcd, 8 vars) explode into thousands of mostly-spurious terms
# and time out in generation + simplify. Large-subset mp terms are rarely true.
MP_MAX_SUBSET = 2
IDEG = 1  # deg (if 1 then linear)
ITERMS = 2  # octagonal
ICOEFS = 1  # from -ICOEFS to ICOEFS, e.g., -1,0,1
# min # of distinct term values required to trust a congruence mod n.
# guards against a large modulus inferred from too few values (gcd overfit):
# the chance of a spurious shared divisor is ~1/2^(nvals-1), so a flat
# minimum suffices (large moduli are self-protecting).
CONGRUENCE_MIN_NVALS = 5

# options for full specs analysis
CTR_VAR = "Ct"  # counter variable contains this string
POST_LOC = "post"  # vtraceX_post  indicates postconditions

# Program Paths
TRACE_DIR = "traces"
SYMEXE_DIR = "symexe"
TRACE_INDICATOR = "vtrace"
MAINQ_FUN = "mainQ"

class C:
    SE_MIN_DEPTH = 20

    GCC_CMD = "gcc"

    COMPILE = "{gcc} {filename} -o {tmpfile}"
    COMPILE = partial(COMPILE.format, gcc=GCC_CMD)

    C_RUN = "{exe}"
    C_RUN = partial(C_RUN.format)


# Declarative tables driving setup(). Each entry maps an argparse attribute to
# the settings attribute it overrides and the CLI flag used to reconstruct it
# when re-invoking dig.py as a subprocess (benchmark mode).

# store_true flags: when present, force the named DO_* setting to a fixed value.
# The "no..." flags disable a feature (set False); -dosolverstats enables one.
_BOOL_FLAGS = (
    # (arg_attr, setting_attr, cli_flag, value_when_present)
    ("nosimplify", "DO_SIMPLIFY", "-nosimplify", False),
    ("nofilter", "DO_FILTER", "-nofilter", False),
    ("noss", "DO_SS", "-noss", False),
    ("nomp", "DO_MP", "-nomp", False),
    ("noeqts", "DO_EQTS", "-noeqts", False),
    ("noieqs", "DO_IEQS", "-noieqs", False),
    ("nocongruences", "DO_CONGRUENCES", "-nocongruences", False),
    ("noarrays", "DO_ARRAYS", "-noarrays", False),
    ("nominmaxplus", "DO_MINMAXPLUS", "-nominmaxplus", False),
    ("noincrdepth", "DO_INCR_DEPTH", "-noincrdepth", False),
    ("dosolverstats", "DO_SOLVER_STATS", "-dosolverstats", True),
)

# String options: applied verbatim when truthy. (Subprocess reconstruction emits
# the bare flag without its value, matching the original behavior.)
_STR_FLAGS = (
    # (arg_attr, setting_attr, cli_flag)
    ("writevtraces", "WRITE_VTRACES", "-writevtraces"),
    ("writesstates", "WRITE_SSTATES", "-writesstates"),
    ("readsstates", "READ_SSTATES", "-readsstates"),
)

# Int options: applied when given and >= 1; reconstructed as "-flag <value>".
_INT_FLAGS = (
    # (arg_attr, setting_attr, cli_flag)
    ("inpMaxV", "INP_MAX_V", "-inpMaxV"),
    ("iupper", "IUPPER", "-iupper"),
    ("ideg", "IDEG", "-ideg"),
    ("iterms", "ITERMS", "-iterms"),
    ("icoefs", "ICOEFS", "-icoefs"),
    ("maxterm", "MAX_TERM", "-maxterm"),
    ("nrandinps", "N_RAND_INPS", "-nrandinps"),
)


def setup(settings, args):
    """
    Apply command-line ``args`` to the global ``settings`` module.

    Two modes:
    - ``settings`` truthy: mutate the settings module in place and return a
      configured logger.
    - ``settings`` falsy (None): collect the equivalent CLI flags and return
      them as a string, used to re-invoke dig.py as a benchmark subprocess.
    """
    import helpers.vcommon

    opts = []

    for arg_attr, set_attr, flag, value in _BOOL_FLAGS:
        if getattr(args, arg_attr):
            if settings:
                setattr(settings, set_attr, value)
            else:
                opts.append(flag)

    for arg_attr, set_attr, flag in _STR_FLAGS:
        val = getattr(args, arg_attr)
        if val:
            if settings:
                setattr(settings, set_attr, val)
            else:
                opts.append(flag)

    for arg_attr, set_attr, flag in _INT_FLAGS:
        val = getattr(args, arg_attr)
        if val is not None and val >= 1:
            if settings:
                setattr(settings, set_attr, val)
            else:
                opts.append(f"{flag} {val}")

    if args.uterms:
        if settings:
            settings.UTERMS = set(args.uterms.split(';'))
        else:
            opts.append(f'-uterms "{args.uterms}"')  # not tested

    if args.se_mindepth is not None and args.se_mindepth >= 1:
        if settings:
            settings.C.SE_MIN_DEPTH = args.se_mindepth
        else:
            opts.append(f"-se_mindepth {args.se_mindepth}")

    if args.se_maxdepth is not None and args.se_maxdepth >= 1:
        if settings:
            settings.SE_MAX_DEPTH = args.se_maxdepth
            settings.SE_MAX_DEPTH_PYTHON = args.se_maxdepth
        else:
            opts.append(f"-se_maxdepth {args.se_maxdepth}")

    if args.tmpdir:
        if settings:
            settings.TMPDIR = Path(args.tmpdir)
            assert settings.TMPDIR.is_dir()
        else:
            opts.append(f"-tmpdir {args.tmpdir}")

    if settings:
        settings.LOGGER_LEVEL = helpers.vcommon.getLogLevel(args.log_level)
        mlog = helpers.vcommon.getLogger(__name__, settings.LOGGER_LEVEL)
        return mlog
    else:
        opts.append(f"-log_level {args.log_level}")
        return " ".join(opts)
