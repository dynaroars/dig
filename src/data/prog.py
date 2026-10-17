"""
Modelling a program, including running the program on inputs and 
collecting traces
"""

import abc
import re
import shlex
import itertools
import random
from functools import lru_cache
from pathlib import Path
import pdb
from collections import namedtuple
import subprocess

import sympy
import z3

import settings
from helpers.miscs import MP
from helpers.z3utils import Z3
import helpers.vcommon as CM

import data.traces

from beartype import beartype

DBG = pdb.set_trace
mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


class Symb(namedtuple("Symb", ("name", "typ"))):
    """
    Symbolic variable and its type,
    e.g., (x, 'I') means x is an integer
    """

    @beartype
    @property
    def is_array(self) -> bool:
        return self.typ == "array"

    @beartype
    def __str__(self) -> str:
        return f"{self.typ} {self.name}"

    @property
    def symbolic(self):
        try:
            ret = self._symbolic
            return ret
        except AttributeError:
            self._symbolic = sympy.Symbol(self.name)
            return self._symbolic

    @property
    def expr(self):
        try:
            ret = self._expr
            return ret
        except AttributeError:
            self._expr = Z3.parse(str(self.symbolic))
            return self._expr


class Symbs(tuple):
    def __new__(cls, ss):
        # mainQ(void) has a legitimate empty input signature.
        assert all(isinstance(s, Symb) for s in ss), ss
        return super().__new__(cls, ss)

    def __str__(self):
        return "; ".join(map(str, self))

    @property
    def array_only(self):
        return all(s.is_array for s in self)

    @property
    def names(self):
        return tuple(s.name for s in self)

    @property
    def symbolic(self):
        return tuple(s.symbolic for s in self)

    @beartype
    @property
    def exprs(self) -> list:
        try:
            ret = self._exprs
            return ret
        except AttributeError:
            self._exprs = [s.expr for s in self]
            return self._exprs 

    @beartype
    @classmethod
    def mk(cls, ls: list[str]) -> tuple:
        """
        I x , D y .. ->  {x: int, y: double}

        x , y .. ->  {x: int, y: double}
        """
        symbs = []
        for x in ls:
            x = x.strip()
            if not x:
                continue
            vs = x.split()
            
            assert len(vs) == 2, vs  # I, x
            t, k = vs[0], vs[1]
            symbs.append(Symb(k, t))
        return cls(symbs)


# inv_decls = {loc: Symbs}
class DSymbs(dict):
    pass


@lru_cache(maxsize=16)
def _precondition_of(text: str, filename: str) -> tuple:
    """
    (constraint, complete) for a C source: the vassume precondition over
    mainQ's inputs, as z3, cached on the source text (cf.
    infer.source_hints._candidates). Any failure to obtain one is reported as
    "no precondition", which leaves input generation exactly as it was.
    """
    del text  # only part of the cache key, so an edited source re-extracts
    try:
        from data.symex_c import CSymEx
        engine = CSymEx(Path(filename), 1)
        engine._parse()
        return engine.input_precondition()
    except Exception as ex:
        mlog.debug(f"no input precondition for '{filename}': {ex}")
        return None, False


class Prog:
    @beartype
    def __init__(self, exe_cmd: str, inp_decls: Symbs, inv_decls: DSymbs,
                 source: Path | None = None) -> None:
        self.exe_cmd = exe_cmd
        self.inp_decls = inp_decls
        self.inv_decls = inv_decls
        self._cache = {}  # inp -> traces (str)
        self.execution_outcomes = {}
        self.source = source
        # blocked in later calls, so asking again yields new values
        self._solver_found = set()

    @beartype
    @property
    def locs(self): 
        return self.inv_decls.keys()

    # PUBLIC METHODS
    
    @beartype
    def get_traces(self, inps: data.traces.Inps) -> data.traces.DTraces:
        """
        front end to obtain traces from inps
        """
        traces = self._get_traces_mp(inps)
        traces = itertools.chain.from_iterable(traces.values())
        traces = data.traces.DTraces.parse(traces, self.inv_decls)
        assert all(loc in self.inv_decls for loc in traces), traces.keys()
        return traces

    @beartype
    def gen_rand_inps(self, n_needed: int = 1) -> set[tuple]:
        """
        Random inputs for the program, guided by its vassume precondition when
        one can be extracted: a candidate the precondition provably rejects is
        dropped before it costs a process execution, and when the sampling
        windows rarely (or never) hit the admissible set, a bounded solver
        phase supplies the rest. A program without a usable precondition takes
        exactly the path it always did.
        """
        assert n_needed >= 1, n_needed
        try:
            valid_ranges = self._valid_ranges
            inps = set()
        except AttributeError:
            valid_ranges, inps = self._get_valid_inp_ranges()
            self._valid_ranges = valid_ranges

        constraint, complete = self.precondition
        n_rejected = n_draws = 0
        # tested once per pass, so one pass may overshoot it; range
        # validation's own draws are not counted here
        budget = settings.INP_ATTEMPT_FACTOR * n_needed

        while len(inps) < n_needed:
            old_siz = len(inps)
            n_rejected_pass = 0
            # iterate in a canonical order so RNG is consumed deterministically:
            # set iteration order is not stable across processes (it forks via
            # _get_traces_mp), which otherwise makes generated inps vary run-to-run.
            for inp_range in sorted(valid_ranges):
                # an admissible input per window per pass, so what a pass
                # contributes does not depend on how much of the window the
                # precondition rules out
                myinp, drawn = self._draw_admissible(inp_range)
                n_draws += drawn
                if myinp is None:
                    n_rejected_pass += drawn
                    continue
                n_rejected_pass += drawn - 1
                inps.add(myinp)

            n_rejected += n_rejected_pass
            # nothing added *and* nothing rejected is the original stopping
            # condition; a rejection means the window is still live
            if len(inps) == old_siz and not n_rejected_pass:
                mlog.debug(f"can't gen new rand inps (current {len(inps)})")
                break
            if constraint is not None and n_draws >= budget:
                break

        status, n_calls = "ok", 0
        if constraint is not None and len(inps) < n_needed:
            extra, status, n_calls = self._solver_sample(
                n_needed - len(inps), inps, constraint)
            inps |= extra
            if not inps and status == "exhausted":
                # handed out by an earlier call; returning nothing would make
                # the caller give up on random inputs altogether
                inps = set(self._solver_found)

        if constraint is not None:
            self._log_rand_inps(n_needed, len(inps), n_rejected, n_draws,
                                status, n_calls, complete)
        return inps

    @property
    def precondition(self) -> tuple:
        """
        (constraint, complete): the program's vassume precondition over the
        inputs, as a z3 expression, or (None, _) when there is no source, the
        source cannot be parsed, or no condition is usable. `complete` is
        False when the constraint is weaker than the real precondition (see
        CSymEx.input_precondition), in which case it may only rule inputs out.
        """
        try:
            return self._precondition
        except AttributeError:
            self._precondition = (None, False)
            if self.source is not None:
                try:
                    self._precondition = _precondition_of(
                        self.source.read_text(), str(self.source))
                except OSError as ex:
                    mlog.debug(f"cannot read '{self.source}': {ex}")
            return self._precondition

    def _admits(self, inp: tuple):
        """
        Three-valued test of a candidate against the precondition:
        True (satisfies it), False (violates it) or None (cannot tell, e.g. a
        division by a candidate 0 -- z3 leaves that uninterpreted).

        Only a False verdict is acted on. None, and conditions that could not
        be translated at all, are never read as "satisfied": running the
        program stays the oracle for every candidate that is kept, so an
        input is never claimed admissible on the strength of this check.
        """
        constraint, _ = self.precondition
        if constraint is None:
            return None
        subs = [(z3.Int(name), z3.IntVal(v))
                for name, v in zip(self.inp_decls.names, inp)
                if isinstance(v, int)]
        if not subs:
            return None
        try:
            simplified = z3.simplify(z3.substitute(constraint, *subs))
        except z3.Z3Exception as ex:
            mlog.debug(f"cannot evaluate assumptions on {inp}: {ex}")
            return None
        if z3.is_true(simplified):
            return True
        if z3.is_false(simplified):
            return False
        return None

    # PRIVATE METHODS
    @beartype
    def _get_traces(self, inp: data.traces.Inp) -> list[str]:

        inp_ = (v if isinstance(v, int) or v.is_integer() else v.n()
                for v in inp.vs)
        inp_ = " ".join(map(str, inp_))
        cmd = f"{self.exe_cmd} {inp_}"
        mlog.debug(cmd)

        # do not check cmd status, could get error status due to incorrect input
        try:
            cp = subprocess.run(shlex.split(cmd), capture_output=True,
                                text=True, timeout=settings.C.RUN_TIMEOUT)
        except subprocess.TimeoutExpired:
            # the program did not terminate within the budget on this input
            # (e.g. an infinite loop); skip it rather than hang forever.
            mlog.warning(
                f"run timed out after {settings.C.RUN_TIMEOUT}s, no traces: {cmd}")
            self.execution_outcomes[inp] = "timeout"
            return []
        # Assertions, signed-overflow traps, and arithmetic faults can occur
        # after printf has emitted part of a trace. Reject the whole failed
        # execution so those partial states cannot pollute fitting/testing.
        if cp.returncode < 0:
            self.execution_outcomes[inp] = f"signal:{-cp.returncode}"
            return []
        traces = cp.stdout.splitlines()
        self.execution_outcomes[inp] = "traces" if traces else f"empty:exit:{cp.returncode}"
        return traces

    @beartype
    def _get_traces_mp(self, inps: data.traces.Inps) -> dict:
        """
        run program on inps and obtain traces in parallel
        return {inp: traces}
        """

        tasks = [inp for inp in inps if inp not in self._cache]

        def f(tasks):
            results = []
            for inp in tasks:
                traces = self._get_traces(inp)
                results.append((inp, traces, self.execution_outcomes.get(inp, "unknown")))
            return results

        wrs = MP.run_mp("get traces", tasks, f, settings.DO_MP)

        for inp, traces, outcome in wrs:
            assert inp not in self._cache
            self._cache[inp] = traces
            self.execution_outcomes[inp] = outcome

        return {inp: self._cache[inp] for inp in inps}

    def _get_valid_inp_ranges(self):


        dr = {}  # Inp => range
        di = {}  # Inp => inp
        inp_ranges = list(self._get_inp_ranges(len(self.inp_decls)))
        live = []

        def record(inp_range, inp):
            my_inp = data.traces.Inp(self.inp_decls.names, inp)
            dr[my_inp] = inp_range
            di[my_inp] = inp

        for inp_range in inp_ranges:
            inp, _ = self._draw_admissible(inp_range)
            if inp is None:
                mlog.debug(f"inp range {inp_range} excluded by assumptions")
                continue
            live.append(inp_range)
            record(inp_range, inp)

        # The windows spread the sample, so a precondition that rules most of
        # them out must not shrink it. Without a precondition nothing is
        # excluded and this loop does not run, leaving the draws untouched.
        for i in range(len(inp_ranges) - len(live)):
            if not live:
                break
            inp_range = live[i % len(live)]
            inp, _ = self._draw_admissible(inp_range)
            if inp is not None:
                record(inp_range, inp)

        my_inps = data.traces.Inps(di.keys())
        mytraces = self._get_traces_mp(my_inps)

        valid_ranges, valid_inps = set(), set()
        for my_inp in mytraces:
            if mytraces[my_inp]:
                valid_ranges.add(dr[my_inp])
                valid_inps.add(di[my_inp])
            else:
                mlog.debug(f"inp range {dr[my_inp]} invalid")

        return valid_ranges, valid_inps

    @classmethod
    def _get_inp_from_range(cls, inp_range):
        return tuple(random.randrange(ir[0], ir[1]) for ir in inp_range)

    def _draw_admissible(self, inp_range) -> tuple:
        """
        (input, n_draws) for `inp_range`: an input the precondition does not
        reject, or (None, n) if every attempt was rejected.

        Without a precondition this is one _get_inp_from_range draw, so
        generation is unchanged. With one, a bounded number of re-draws keeps
        a window that is only partly admissible contributing an input per
        pass, instead of that window's share of the sample being lost.
        """
        inp = self._get_inp_from_range(inp_range)
        if self.precondition[0] is None or self._admits(inp) is not False:
            return inp, 1
        for n in range(2, settings.INP_PROBE_REDRAWS + 2):
            inp = self._get_inp_from_range(inp_range)
            if self._admits(inp) is not False:
                return inp, n
        return None, settings.INP_PROBE_REDRAWS + 1

    def _solver_sample(self, k: int, found, constraint) -> tuple:
        """
        Ask z3 for up to `k` further inputs satisfying `constraint`, in at most
        2*k + settings.INP_SOLVER_CALL_SLACK + 1 calls (the cap is tested once
        per sample and a sample may spend two) under the "feasibility" policy,
        whose work budget keeps the outcome independent of machine load.

        Returns (inps, status, n_calls), status one of: "ok", "budget",
        "unsolvable" (the constraint mentions no input of this program),
        "unsat", "exhausted", "outside"/"outside-<reason>" (nothing within
        -inpMaxV satisfies it, so the whole C int range was searched) or
        "unknown". The last three carry claims, so: "unsat" comes from one
        dedicated check, never from a window, bound or blocking clause;
        "exhausted" only when the assumptions constrain *every* input, since a
        free input always admits more tuples; and "unknown" concludes nothing.

        Diversity, which equality fitting needs, comes from solving inside a
        randomly placed window per sample and blocking what is already in hand.
        Inputs the precondition never mentions keep coming from the sampling
        windows, since model completion would pin all of them to 0.
        """
        from data.symex_c import INT_MIN, INT_MAX

        names = self.inp_decls.names
        mentioned = {str(v) for v in Z3.get_vars(constraint)}
        solve_for = [i for i, name in enumerate(names) if name in mentioned]
        if not solve_for:
            return set(), "unsolvable", 0

        free = [i for i in range(len(names)) if i not in set(solve_for)]
        maxv = settings.INP_MAX_V
        cap = 2 * k + settings.INP_SOLVER_CALL_SLACK
        blocked = set(found) | self._solver_found
        out: set = set()
        calls = 0

        def check(extra):
            nonlocal calls
            calls += 1
            solver = Z3.create_solver(maximize=False)
            solver.add(constraint, *extra)
            res = solver.check()
            return res, (solver.model() if res == z3.sat else None)

        def blocking():
            return [z3.Not(z3.And([z3.Int(names[i]) == int(inp[i])
                                   for i in solve_for]))
                    for inp in (blocked | out)]

        def sample(lo, hi):
            bounds = [c for i in solve_for
                      for c in (z3.Int(names[i]) >= lo, z3.Int(names[i]) <= hi)]
            while len(out) < k and calls < cap:
                target = [random.randrange(0, maxv + 1) for _ in solve_for]
                half = 1 + random.randrange(0, max(1, maxv // 4))
                window = [c for i, t in zip(solve_for, target)
                          for c in (z3.Int(names[i]) >= t - half,
                                    z3.Int(names[i]) <= t + half)]
                res, model = check(bounds + window + blocking())
                if res == z3.unsat:
                    # the window missed: retry without it before concluding
                    res, model = check(bounds + blocking())
                if res == z3.unknown:
                    return "unknown"
                if res == z3.unsat:
                    if free:
                        # out of assignments for the constrained inputs, but
                        # the free ones still admit new tuples
                        return "values"
                    return "exhausted" if (out or blocked) else "outside"
                out.add(self._inp_from_model(model, solve_for))
            return "ok" if len(out) >= k else "budget"

        with Z3.use_policy(settings.solver_policy("feasibility")):
            res, _ = check([])
            if res == z3.unsat:
                return set(), "unsat", calls
            if res == z3.unknown:
                return set(), "unknown", calls

            status = sample(0, maxv)
            if status == "outside":
                # satisfiable, but not inside -inpMaxV: look beyond it, and
                # keep that in the status whatever ends the wider search
                relaxed = sample(INT_MIN, INT_MAX)
                status = ("outside" if relaxed in ("ok", "budget")
                          else f"outside-{relaxed}")
        if status == "values":
            status = self._fill_free(out, blocked, k, solve_for, free)

        self._solver_found |= out
        return out, status, calls

    def _fill_free(self, out, blocked, k, solve_for, free) -> str:
        """
        Top up `out` once the solver has no further assignment for the inputs
        the precondition constrains: reuse an assignment already known to be
        admissible and draw fresh values for the free inputs. Bounded by
        settings.INP_ATTEMPT_FACTOR draws per input still wanted, and every
        candidate still goes through the precondition check.
        """
        known = sorted({tuple(inp[i] for i in solve_for) for inp in (out | blocked)
                        if self._admits(inp) is not False})
        if not known:
            return "budget"
        attempts, cap = 0, settings.INP_ATTEMPT_FACTOR * max(1, k - len(out))
        while len(out) < k and attempts < cap:
            attempts += 1
            base = known[random.randrange(len(known))]
            cand = [0] * len(self.inp_decls.names)
            for pos, i in enumerate(solve_for):
                cand[i] = base[pos]
            for i in free:
                cand[i] = random.randrange(0, settings.INP_MAX_V)
            myinp = tuple(cand)
            if (myinp not in out and myinp not in blocked
                    and self._admits(myinp) is not False):
                out.add(myinp)
        return "ok" if len(out) >= k else "budget"

    def _inp_from_model(self, model, solve_for):
        """
        Read one candidate input off a model: inputs the precondition
        constrains come from the model, the rest stay random -- model
        completion would pin every unconstrained input to 0, which costs the
        trace diversity the inference needs.
        """
        chosen = set(solve_for)
        return tuple(
            model.eval(z3.Int(name), model_completion=True).as_long()
            if i in chosen else random.randrange(0, settings.INP_MAX_V)
            for i, name in enumerate(self.inp_decls.names))

    def _log_rand_inps(self, n_needed, n_got, n_rejected, n_draws,
                       status, n_calls, complete):
        """One line per generation call, so a shortfall is never silent."""
        src = self.source.name if self.source else "?"
        what = "the assumptions" if complete else "the assumptions extracted"
        detail = (f"{n_draws} draws, {n_rejected} rejected by assumptions"
                  + (f", {n_calls} solver call{'s' if n_calls > 1 else ''}"
                     if n_calls else ""))
        if status == "unsat":
            # a weaker constraint being unsatisfiable means the real
            # precondition is too, so this holds even if extraction was partial
            mlog.error(f"{src}: {what} are unsatisfiable, so no input can "
                       f"produce traces ({detail})")
        elif status.startswith("outside"):
            why = {"outside-exhausted": "; no further input satisfies them at all",
                   "outside-unknown": "; the solver then gave up",
                   "outside-values": ""}.get(status, "")
            mlog.warning(f"{src}: no input within -inpMaxV {settings.INP_MAX_V} "
                         f"satisfies {what}; sampled beyond it, got {n_got} of "
                         f"{n_needed} inps{why} ({detail})")
        elif status == "exhausted":
            mlog.info(f"{src}: no further input satisfies {what} within "
                      f"-inpMaxV {settings.INP_MAX_V}, got {n_got} of "
                      f"{n_needed} inps ({detail})")
        elif status == "unknown":
            mlog.warning(f"{src}: solver gave up while sampling inputs, got "
                         f"{n_got} of {n_needed} inps ({detail})")
        elif status == "unsolvable":
            mlog.warning(f"{src}: {what} constrain no input of this program, so "
                         f"only the sampling windows apply; got {n_got} of "
                         f"{n_needed} inps ({detail})")
        elif n_got < n_needed:
            mlog.warning(f"{src}: generated {n_got} of {n_needed} inps, "
                         f"could not find more within the search budget "
                         f"({detail})")
        else:
            mlog.debug(f"{src}: generated {n_got} inps ({detail})")

    @classmethod
    def _get_inp_ranges(cls, n_inps):
        small = 0.10
        large = 1 - small
        maxV = settings.INP_MAX_V
        rinps = [(0, int(maxV * small)), (int(maxV * large), maxV)]
        if n_inps <= settings.INP_RANGE_V:
            # consider some ranges for smaller #'s of inps
            tiny = 0.05
            rinps.extend([(0, int(maxV * tiny))])
            # Small/high-only sampling misses whole middle regions (e.g.
            # Knuth's divisor-search paths), leaving spurious polynomial
            # bases that shallow symbolic execution also cannot refute.
            rinps.append((int(maxV*0.25), int(maxV*0.75)))

        # [((0, 30), (0, 30)), ((0, 30), (270, 300)), ...]
        rinps = list(dict.fromkeys((lo, hi) for lo, hi in rinps if lo < hi))
        rinps_i = itertools.product(*itertools.repeat(rinps, n_inps))
        return rinps_i



class Src(metaclass=abc.ABCMeta):
    def __init__(self, filename:Path, tmpdir:Path) -> None:
        assert filename.is_file(), filename
        assert tmpdir.is_dir(), tmpdir

        filename, basename, funname = self.check(filename, tmpdir)

        tracedir = self.mkdir(tmpdir / settings.TRACE_DIR)
        tracefile = tracedir / basename
        symexedir = self.mkdir(tmpdir / settings.SYMEXE_DIR)

        self.filename, self.basename, self.funname = filename, basename, funname
        self.tracedir, self.tracefile = tracedir, tracefile
        self.symexedir = symexedir
         

    @abc.abstractmethod
    def check(self, filename, tmpdir):
        pass

    @classmethod
    def parse_type_info(cls, msg):
        # vtrace2; I x; I y; I q; I r
        # vtrace1; I q; I r; I a; I b; I x; I y
        # mainQ_cohendiv; I x; I y,
        
        mainQ_name = None
        inp_decls = None
        inv_decls = []

        for l in msg.split("\n"):
            if not (settings.MAINQ_FUN in l or settings.TRACE_INDICATOR in l):
                continue
            contents = l.split(';')  # ['vtraceX', 'I x', 'I y']

            symbs = Symbs.mk(contents[1:])
            if contents[0].startswith(settings.MAINQ_FUN):
                mainQ_name = contents[0]
                inp_decls = symbs
            else:
                assert contents[0].startswith(
                    settings.TRACE_INDICATOR), contents
                inv_decls.append((contents[0], symbs))
        inv_decls = DSymbs(inv_decls)

        return inp_decls, inv_decls, mainQ_name,

    def mkdir(self, d):
        assert not d.exists(), d
        d.mkdir()
        return d

class C(Src):
    @beartype
    def __init__(self, filename: Path, tmpdir: Path) -> None:
        super().__init__(filename, tmpdir)

        self._safety_scan(self.filename)

        from c_instrument import instrument
        typ = instrument(self.filename, self.tracefile)
        self.inp_decls, self.inv_decls, self.mainQ_name = \
            self.parse_type_info('\n'.join(typ))

        # register real-valued (float/double) vars so z3 builds them as Reals
        # consistently across candidate invariants and symbolic states
        real_names = {s.name for s in self.inp_decls if s.typ in ("D", "F")}
        for loc in self.inv_decls:
            real_names |= {s.name for s in self.inv_decls[loc]
                           if s.typ in ("D", "F")}
        Z3.set_real_vars(real_names)

        self.traceexe = self.tracefile.with_suffix(".exe")
        self._compile_test(self.tracefile, self.traceexe)

    @beartype
    def check(self, filename: Path, tmpdir: Path) -> tuple[Path, Path, str]:
        basename = Path(filename.name)
        funname = basename.stem
        self._compile_test(filename, tmpdir / f"{funname}.exe")
        return filename, basename, funname

    @beartype
    @staticmethod
    def _safety_scan(filename: Path) -> None:
        """
        Quick static guard run before a file is compiled/executed: DIG runs the
        input program as a real subprocess, so reject sources that call out to
        anything with side effects (deleting files, spawning processes, opening
        sockets, etc.). The benchmarks are pure numeric computations and never
        need these, so any occurrence is treated as untrusted.
        """
        src = filename.read_text()
        # strip // and /* */ comments so a call name in a comment isn't flagged
        src = re.sub(r"//[^\n]*", "", src)
        src = re.sub(r"/\*.*?\*/", "", src, flags=re.DOTALL)
        # drop `extern ...;` prototype declarations: in preprocessed sources the
        # expanded system headers declare these names (e.g. `extern int system(
        # const char *)`) without ever calling them.
        src = re.sub(r"\bextern\b[^;{}]*;", "", src)

        found = sorted({
            call for call in settings.C.FORBIDDEN_CALLS
            # match a call site: name followed by '(' (allowing whitespace)
            if re.search(rf"\b{re.escape(call)}\s*\(", src)
        })
        if found:
            raise ValueError(
                f"refusing to run '{filename}': contains potentially unsafe "
                f"call(s): {', '.join(found)}")

    @beartype
    @classmethod
    def _compile_test(cls, filename: Path, out: Path) -> None:
        cmd = settings.C.COMPILE(filename=filename, tmpfile=out)
        subprocess.run(shlex.split(cmd), check=True)
        assert out.is_file(), out
