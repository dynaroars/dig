import shlex
from dataclasses import dataclass, asdict
from functools import partial
from pathlib import Path


TMPDIR = Path("/var/tmp/")
LOGGER_LEVEL = 3
DO_MP = True  # use multiprocessing
# DO_SIMPLIFY / DO_FILTER are always-on constants (their -no… flags were
# removed); flip them here if you ever need to debug what they drop.
DO_SIMPLIFY = True  # simplify results, e.g., removing weaker invariants
DO_FILTER = True  # remove ieqs and min/max terms that unlikely interesting
DO_SS = True  # use symbolic states to check results
DO_EQTS = True  # support equalities
DO_IEQS = True  # support (octagonal) inequalities
DO_CONGRUENCES = True  # support congruence relations
DO_MINMAXPLUS = True  # support minmax-plus inequalities
DO_RECURRENCE = True  # static (recurrence-based) equalities for solvable loops
# Houdini pass over the union of LLM-proposed candidates (llm mode only): prove
# the largest jointly/k-inductive subset unboundedly, catching mutually
# inductive sets the per-candidate bounded check misses. Additive to verify().
DO_LLM_HOUDINI = True
WRITE_VTRACES = None  # write vtraces to csv

# Lean 4 certification of C invariants (src/certify, LEAN_CERTIFICATION_PLAN.md)
DO_CERTIFY_LEAN = False  # extra Lean 4 certification pass over Z3-checked invariants
# How candidate invariants are verified:
#   "z3":   (default) classic DIG: z3 checks candidates against symbolic states
#           (combine with --certify-lean for unbounded Lean 4 proofs)
#   "lean": (--lean-only) candidates are not checked with z3; Lean proves them
#           and unproved ones are dropped
VERIFIER = "z3"
LEAN_KEEP_UNVERIFIED = False  # lean mode: also report invs Lean couldn't prove
# Lean mode: z3 only *searches for counterexamples* (new inputs/traces) to
# candidates, under a short budget; unsat/unknown decide nothing (Lean does).
CEX_SEARCH_SOLVER_TIMEOUT_MS = 300
CEX_SEARCH_SOLVER_RLIMIT = 1_000_000
LEAN_BIN = None        # explicit lean binary; default: lean on PATH, then elan
LEAN_TIMEOUT = 120.0   # seconds per Lean run (one drop-pass round)
LEAN_MAX_ROUNDS = 8    # drop-pass round cap; hitting it means "not certified"
LEAN_CERT_OUT = None   # copy the final .lean certificate here
# also use DIG's pre-simplify invariants as (never reported) loop-head helpers;
# off by default: the extra conjuncts make large certificates much slower
LEAN_PRESIMPLIFY_HELPERS = False

N_RAND_INPS = 100  # number of random inputs, only used when DO_SS is False
INP_MAX_V = 300
SE_DEPTH_NOCHANGES_MAX = 3
SE_MAX_DEPTH = 8  # max symbolic-execution depth; override with --se_maxdepth
# Deterministic z3 work-unit budget, plus a safety timeout for native arithmetic.
# The work budget is independent of CPU contention; timeout fallbacks can
# affect optional results and are recorded separately in benchmark settings.
# Calibrated to ~3s of CPU work on a typical core (see create_solver).
SOLVER_RLIMIT = 15_000_000
SOLVER_TIMEOUT_MS = 5000  # fallback when native arithmetic exceeds the work budget
# Optional bound searches and redundancy removal must not consume the whole
# run budget after equality discovery. Unknown optimization results are
# omitted; unknown implications retain the original invariant.
OPT_SOLVER_RLIMIT = 500_000
OPT_SOLVER_TIMEOUT_MS = 1000  # safety fallback for expensive native NIA operations
SIMPLIFY_SOLVER_RLIMIT = 100_000
SIMPLIFY_SOLVER_TIMEOUT_MS = 1000
FEASIBILITY_SOLVER_RLIMIT = 100_000
FEASIBILITY_SOLVER_TIMEOUT_MS = 100


@dataclass(frozen=True)
class SolverPolicy:
    rlimit: int
    timeout_ms: int


def solver_policy(phase="checking"):
    """Resolve each phase's immutable policy at use time, not import time."""
    values = {
        "checking": (SOLVER_RLIMIT, SOLVER_TIMEOUT_MS),
        "optimization": (OPT_SOLVER_RLIMIT, OPT_SOLVER_TIMEOUT_MS),
        "simplification": (SIMPLIFY_SOLVER_RLIMIT, SIMPLIFY_SOLVER_TIMEOUT_MS),
        "feasibility": (FEASIBILITY_SOLVER_RLIMIT, FEASIBILITY_SOLVER_TIMEOUT_MS),
        "cex_search": (CEX_SEARCH_SOLVER_RLIMIT, CEX_SEARCH_SOLVER_TIMEOUT_MS),
    }
    return SolverPolicy(*values[phase])


def effective_settings():
    """Serializable effective configuration for a result, including policies."""
    result = {name: value for name, value in globals().items()
              if name.isupper() and not name.startswith("_")
              and isinstance(value, (str, int, float, bool, type(None)))}
    result["solver_policies"] = {phase: asdict(solver_policy(phase)) for phase in
                                 ("checking", "optimization", "simplification",
                                  "feasibility", "cex_search")}
    return result
EQT_RATE = 1.5
# Groebner-basis reduction (Miscs.reduce_eqts) can hang on degree-2/many-var
# candidate eqts (e.g. egcd, 8 vars). Bound it; on timeout we fall back to the
# unreduced eqts, which is reduce_eqts's documented behavior anyway.
GROEBNER_TIMEOUT = 5  # secs
UGLY_FACTOR = 20  # remove equalities that have lots of terms and "large" coefficients
MAX_TERM = 200

TRACE_MULTIPLIER = 5
INP_RANGE_V = 4  # use more inp ranges when # of inputs is <= this
SOURCE_TEMPLATES = True  # automatic hints; explicit template controls opt out

# Inequalities
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
# the chance of a spurious shared divisor is ~1/2^SE_MAX_D(nvals-1), so a flat
# minimum suffices (large moduli are self-protecting).
CONGRUENCE_MIN_NVALS = 5

# Program Paths
TRACE_DIR = "traces"
SYMEXE_DIR = "symexe"
TRACE_INDICATOR = "vtrace"
MAINQ_FUN = "mainQ"

class C:
    GCC_CMD = "gcc"

    # Symbolic inference uses mathematical integer arithmetic. Reject native
    # executions that overflow signed C integers instead of fitting wrapped
    # values that contradict that arithmetic.
    COMPILE = "{gcc} -ftrapv {filename} -o {tmpfile}"
    COMPILE = partial(COMPILE.format, gcc=GCC_CMD)

    C_RUN = "{exe}"
    C_RUN = partial(C_RUN.format)

    # max wall-clock seconds a single program run may take. Inputs that don't
    # terminate within this bound are killed and contribute no traces, so a
    # non-terminating program can't hang DIG.
    RUN_TIMEOUT = 2

    # function calls that are rejected by the static safety scan before a file
    # is compiled/run: file deletion/modification, process spawning, etc. The
    # input programs are pure numeric computations, so none of these are needed.
    FORBIDDEN_CALLS = (
        "system", "popen",
        "exec", "execl", "execlp", "execle", "execv", "execvp", "execvpe",
        "fork", "vfork", "clone",
        "remove", "unlink", "unlinkat", "rmdir", "rename", "renameat",
        "fopen", "freopen", "open", "openat", "creat",
        "truncate", "ftruncate",
        "socket", "connect", "kill",
    )


# Declarative tables driving setup(). Each entry maps an argparse attribute to
# the settings attribute it overrides and the CLI flag used to reconstruct it
# when re-invoking dig.py as a subprocess (benchmark mode).

# -types/-only allowlist: canonical name -> the DO_* setting it enables. When
# -types is given, every governed type is turned off and only the listed ones
# back on, replacing the seven -no<type> flags with one positive selector.
# (The -no<type> flags still work as hidden aliases for back-compat.)
_TYPE_ALIASES = {
    "eqt": "DO_EQTS", "eqts": "DO_EQTS", "eq": "DO_EQTS",
    "ieq": "DO_IEQS", "ieqs": "DO_IEQS", "oct": "DO_IEQS",
    "minmax": "DO_MINMAXPLUS", "mmp": "DO_MINMAXPLUS", "minmaxplus": "DO_MINMAXPLUS",
    "congruence": "DO_CONGRUENCES", "cong": "DO_CONGRUENCES", "congruences": "DO_CONGRUENCES",
    "recurrence": "DO_RECURRENCE", "rec": "DO_RECURRENCE",
}
# every type governed by -types (all turned off before the allowlist re-enables)
_TYPE_SETTINGS = (
    "DO_EQTS", "DO_IEQS", "DO_MINMAXPLUS",
    "DO_CONGRUENCES", "DO_RECURRENCE",
)


def _parse_types(spec):
    """Comma/space-separated type spec -> set of DO_* setting names to enable.
    Raises ValueError on an unknown type name (with the valid names listed)."""
    names = [t.strip() for t in spec.replace(",", " ").split() if t.strip()]
    enabled = set()
    for n in names:
        setting = _TYPE_ALIASES.get(n.lower())
        if setting is None:
            valid = ", ".join(sorted({k for k in _TYPE_ALIASES}))
            raise ValueError(f"unknown type '{n}' in -types (valid: {valid})")
        enabled.add(setting)
    return enabled


# store_true flags: when present, force the named DO_* setting to a fixed value.
_BOOL_FLAGS = (
    # (arg_attr, setting_attr, cli_flag, value_when_present)
    ("noss", "DO_SS", "-noss", False),
    ("nomp", "DO_MP", "-nomp", False),
    ("nollmhoudini", "DO_LLM_HOUDINI", "-nollmhoudini", False),
    ("certify_lean", "DO_CERTIFY_LEAN", "--certify-lean", True),
    ("z3_check", "VERIFIER", "--z3-check", "z3"),
    ("lean_only", "VERIFIER", "--lean-only", "lean"),
    ("keep_unverified", "LEAN_KEEP_UNVERIFIED", "--keep-unverified", True),
)

# String options: apply verbatim.
_STR_FLAGS = (
    # (arg_attr, setting_attr, cli_flag)
    ("writevtraces", "WRITE_VTRACES", "-writevtraces"),
    ("lean_bin", "LEAN_BIN", "--lean-bin"),
    ("lean_out", "LEAN_CERT_OUT", "--lean-out"),
)


def setup(settings, args):
    """Apply command-line ``args`` to the global ``settings`` module."""
    import helpers.vcommon

    types_spec = getattr(args, "types", None)
    if types_spec:
        enabled = _parse_types(types_spec)
        for set_attr in _TYPE_SETTINGS:
            setattr(settings, set_attr, set_attr in enabled)

    for arg_attr, set_attr, _flag, value in _BOOL_FLAGS:
        if getattr(args, arg_attr, False):
            setattr(settings, set_attr, value)

    for arg_attr, set_attr, _flag in _STR_FLAGS:
        val = getattr(args, arg_attr, None)
        if val:
            setattr(settings, set_attr, val)

    if getattr(args, "lean_timeout", None):
        settings.LEAN_TIMEOUT = float(args.lean_timeout)
    if getattr(args, "lean_max_rounds", None):
        settings.LEAN_MAX_ROUNDS = int(args.lean_max_rounds)

    if args.se_maxdepth is not None and args.se_maxdepth >= 1:
        settings.SE_MAX_DEPTH = args.se_maxdepth

    if args.tmpdir:
        settings.TMPDIR = Path(args.tmpdir)
        assert settings.TMPDIR.is_dir()

    settings.LOGGER_LEVEL = helpers.vcommon.getLogLevel(args.log_level)
    mlog = helpers.vcommon.getLogger(__name__, settings.LOGGER_LEVEL)
    return mlog
