"""
Python symbolic execution engine for simple C programs.

Handles invariant inference on programs using:
  - Integer arithmetic (+ - * / %)
  - while loops with break
  - if/else branching
  - vassume(cond) for preconditions
  - vtraceN(...) for observation points
  - vassert(cond) checked with z3 per path (results in self.assert_results;
    a violation's model is a concrete counterexample input)
  - unknown()/nondet() as fresh symbolic values
  - C semantics for int / and % (truncation toward zero, remainder takes
    the dividend's sign), side effects in conditions (while (i++ < n)),
    and the ternary operator
  - 1-D arrays as z3 arrays: a[i] reads/writes, {…} initializers (rest 0),
    int a[]/int* parameters to mainQ become symbolic input arrays
  - structs by value, lowered field-sensitively (env entry per nested field:
    p.x, p.inner.y): field reads/writes, {…} inits, q = p copies, typedefs
  - user-defined function calls, inlined (branches fork the caller; loops
    unroll; recursion capped at MAX_INLINE_DEPTH -> fresh value); only
    global writes survive a call (no pointers)
  - global variables (zero-initialized per C static-storage rules)
  - #define/#if directives, expanded via cpp when available (includes are
    stripped first so system headers never enter)

Opt-in modes (all default-off so DIG-facing symstates are untouched):
  - check_safety: auto-check division by zero and array bounds (declared
    sizes only) at every site; violations land in self.safety_results with
    concrete counterexample inputs
  - check_overflow: check written int values against the 32-bit range
    (inputs are constrained to that range so findings are meaningful)
  - merge_states: merge simple if/else diamonds into one state with
    If-valued variables (2^n paths over n diamonds become 1)

Not modeled: pointers/&, '->' (no heap), 2-D arrays, struct params to mainQ.

Post-run APIs: gen_inputs() (concrete inputs covering every explored path),
gen_test_harness() (compilable C driver replaying every path concretely),
unreached_locs() (vtrace points no feasible path hits), check_inv(loc, expr)
(bounded per-path invariant check), prove_inductive(inv, loop, k) — UNBOUNDED
loop-invariant proof by k-induction (base + step; k>1 proves invariants that
are not 1-inductive), the sound complement to depth-bounded vassert/check_inv
— houdini(invs, loop) (largest mutually inductive subset of candidate
invariants, e.g. DIG's output), prove_termination(rank, loop, assume) —
unbounded termination proof via a ranking function (bounded below while
iterating + strict decrease) — and parse_c_expr("q*y + r == x") to build
invariants from C syntax. CLI: --prove [--k N], --check-inv, --houdini,
--terminates RANK [--assume INV, verified inductive first].

Violated vasserts and safety checks carry a witness trace (the sequence of
branch decisions with source locations leading to the violation), printed
by the CLI under "witness trace:".

run() returns z3 path conditions directly (consumed in-process by
SymStatesMakerC), so no text serialization/parsing round-trip is needed.

Standalone: this file has no DIG dependencies — copy it anywhere and run
`python symex_c.py prog.c [--depth N] [--gen-tests]` with just z3-solver
and pycparser installed (Python 3.10+).
"""

from __future__ import annotations

import operator as op_module
from dataclasses import dataclass, field, replace
from enum import Enum, auto
from pathlib import Path

import z3
from pycparser import c_ast, c_parser

# ─────────────────────────────────────────────────────────── helpers ──

_REAL = z3.RealSort()

# 32-bit C int range, used by the opt-in signed-overflow check
INT_MIN = -2**31
INT_MAX = 2**31 - 1


def _is_real(e: z3.ExprRef) -> bool:
    return e.sort() == _REAL


def _to_real(e: z3.ExprRef) -> z3.ExprRef:
    return e if _is_real(e) else z3.ToReal(e)


def _to_int(e: z3.ExprRef) -> z3.ExprRef:
    return z3.ToInt(e) if _is_real(e) else e


def _as_bool(e: z3.ExprRef) -> z3.ExprRef:
    """C truthiness: a numeric expression used as a condition means e != 0."""
    return e if z3.is_bool(e) else op_module.ne(e, 0)


def _short(e, n: int = 50) -> str:
    """Compact one-line rendering of a z3 expr for witness traces."""
    s = " ".join(str(e).split())
    return s if len(s) <= n else s[:n] + "..."


def _coerce(a: z3.ExprRef, b: z3.ExprRef) -> tuple[z3.ExprRef, z3.ExprRef]:
    """Bring a numeric pair to a common z3 sort: if either is Real, promote both."""
    if a.sort() == b.sort():
        return a, b
    if _is_real(a) or _is_real(b):
        return _to_real(a), _to_real(b)
    return a, b


def _type_name(node) -> str | None:
    """Innermost C type name of a Decl/Typename node, e.g. 'int' or 'double'."""
    t = getattr(node, "type", None)
    while t is not None and not isinstance(t, c_ast.IdentifierType):
        t = getattr(t, "type", None)
    return t.names[-1] if isinstance(t, c_ast.IdentifierType) else None


def _param_ctype(p: c_ast.Decl) -> str:
    """C type of a mainQ parameter: 'int', 'double', or 'int[]'/'double[]'
    for array and pointer parameters (both model as a symbolic z3 array)."""
    base = _type_name(p) or "int"
    if isinstance(p.type, (c_ast.ArrayDecl, c_ast.PtrDecl)):
        return base + "[]"
    return base


def _elem_sort(ctype: str) -> z3.SortRef:
    return _REAL if ctype.startswith(("double", "float")) else z3.IntSort()


def _input_var(name: str, ctype: str) -> z3.ExprRef:
    """The X_* input symbol for a mainQ parameter of the given C type."""
    if ctype.endswith("[]"):
        return z3.Array(f"X_{name}", z3.IntSort(), _elem_sort(ctype))
    if ctype in ("double", "float"):
        return z3.Real(f"X_{name}")
    return z3.Int(f"X_{name}")


# ─────────────────────────────────────────────────── symbolic state ──

class Exit(Enum):
    NORMAL = auto()
    BREAK = auto()
    CONTINUE = auto()
    RETURN = auto()


@dataclass
class SymState:
    """One symbolic execution path."""
    env: dict[str, z3.ExprRef] = field(default_factory=dict)
    pc: list[z3.ExprRef] = field(default_factory=list)
    loop_depth: int = 0
    exit: Exit = Exit.NORMAL
    ret: z3.ExprRef | None = None   # return value (used by call inlining)
    trace: tuple[str, ...] = ()     # witness: branch decisions on this path

    def with_trace(self, event: str) -> SymState:
        return replace(self, trace=self.trace + (event,))

    def add_constraint(self, cond: z3.ExprRef) -> SymState:
        return replace(self, pc=self.pc + [z3.simplify(cond)])

    def set_var(self, name: str, val: z3.ExprRef) -> SymState:
        return replace(self, env={**self.env, name: z3.simplify(val)})

    def with_exit(self, reason: Exit) -> SymState:
        return replace(self, exit=reason)

    def inc_loop(self) -> SymState:
        return replace(self, loop_depth=self.loop_depth + 1)

    def reset_exit(self) -> SymState:
        return replace(self, exit=Exit.NORMAL)


# ─────────────────────────────────────────────────── path record ──

@dataclass
class PathRecord:
    loc: str
    param_names: list[str]
    env_snapshot: dict[str, z3.ExprRef]
    pc_snapshot: list[z3.ExprRef]


@dataclass
class AssertResult:
    """Outcome of one vassert(cond) check on one symbolic path.

    status: "valid"    — pc ⇒ cond (holds on every input reaching here;
                          bounded by max_depth loop unrolling)
            "violated" — pc ∧ ¬cond is sat; cex maps the X_* input symbols
                          (and any fresh symbols) to concrete failing values
            "unknown"  — solver hit its rlimit; inconclusive
    """
    coord: str            # source location, e.g. "prog.c:12:5"
    cond: z3.ExprRef      # the asserted condition, evaluated in the path env
    status: str
    cex: dict[str, str] | None = None
    kind: str = "vassert"  # or an auto check: "division-by-zero", "array-bounds"
    trace: tuple[str, ...] = ()   # witness: branch decisions to this point


# ─────────────────────────────────────────────── symex engine ──────

class CSymEx:
    """
    Symbolic execution engine for a small subset of C.

    After calling run(), self.records holds one PathRecord per
    vtrace observation collected along every feasible symbolic path.
    """

    MAX_STATES = 5000  # hard cap on total active states to prevent explosion
    SOLVER_RLIMIT = 15_000_000  # default; DIG passes settings.SOLVER_RLIMIT

    def __init__(self, filename: Path, max_depth: int,
                 solver_rlimit: int | None = None,
                 check_safety: bool = False,
                 check_overflow: bool = False,
                 merge_states: bool = False) -> None:
        self.filename = filename
        self.max_depth = max_depth
        # auto safety checks (division by zero, array bounds); off by default
        # so DIG-facing symstates and timing are untouched
        self.check_safety = check_safety
        # signed-overflow check: separate opt-in because it constrains the
        # X_* inputs to the 32-bit int range (changing the symstates)
        self.check_overflow = check_overflow
        # merge if/else joins into one state with If-valued vars; off by
        # default for the same reason
        self.merge_states = merge_states
        self.records: list[PathRecord] = []
        self.assert_results: list[AssertResult] = []
        self.safety_results: list[AssertResult] = []  # auto-check findings
        self._fresh_ctr = 0  # for naming fresh vars from modeled calls
        self._cur_coord = ""          # coord of the statement being executed
        self._capture_node = None     # used by prove_inductive()
        self._captured: list[SymState] = []
        # side effects (i++/--i) collected while evaluating one expression,
        # applied to the state by _eval_expr_effects afterwards
        self._pending_effects: list[tuple[str, int]] = []

        # Solver for feasibility (reused with push/pop). Deterministic
        # work-unit cutoff, not wall-clock: a timeout makes path feasibility
        # (and thus the symstates themselves) vary with machine load.
        # rlimit is per-check(), so reuse across push/pop scopes is fine.
        self.solver = z3.Solver()
        self.solver.set("rlimit", solver_rlimit or self.SOLVER_RLIMIT)

        # Populated by _parse():
        self.mainq_params: list[tuple[str, str]] = []   # [(name, type), ...]
        self.vtrace_params: dict[str, list[str]] = {}   # {func_name: [param_names]}
        self.func_bodies: dict[str, c_ast.Compound] = {}
        # struct support: type key ('struct S' or typedef name) -> field Decls,
        # and declared struct variable -> its type key
        self.struct_defs: dict[str, list[c_ast.Decl]] = {}
        self.struct_vars: dict[str, str] = {}
        # declared array sizes (env name -> element count) for bounds checks;
        # unsized array parameters are unbounded and never checked
        self.array_sizes: dict[str, int] = {}
        self.mainq_ret: str = "int"
        # user-defined functions (for call inlining) and global variables
        self.func_params: dict[str, list[c_ast.Decl]] = {}
        self.global_decls: list[c_ast.Decl] = []
        self.global_names: set[str] = set()
        self._inline_depth = 0
        self.MAX_INLINE_DEPTH = 8   # recursion cap; deeper calls -> fresh var
        # during havoc-launched executions (induction step, termination
        # body) vassert must be a NO-OP: its assume-after-assert would
        # otherwise smuggle the very property being proven into the path
        # while its violation is discarded — vacuously "valid"
        self._hypothetical = False

    # ── public ───────────────────────────────────────────────────────

    def run(self) -> list[tuple[str, z3.BoolRef, z3.BoolRef]]:
        """
        Execute symbolically.

        Returns list of (loc, pc, slocal) tuples where pc and slocal are z3
        boolean expressions, consumed directly (in-process) by
        SymStatesMaker.merge() — no text serialization/parsing round-trip.
        """
        self._parse()
        init_state = self._make_init_state()
        self._exec_compound(self.func_bodies["mainQ"], [init_state])
        return self._z3_records()

    def gen_inputs(self) -> list[tuple[str, dict[str, str]]]:
        """
        One concrete mainQ input per collected path record (call after run()):
        solve the record's path condition and read off the X_* input values,
        model-completed for unconstrained inputs. Feeding these to the
        instrumented binary guarantees every explored path — and thus every
        reachable vtrace location — actually produces a trace, instead of
        relying on random inputs to hit it.

        Values are exact z3 numerals as strings (e.g. "5", "-3", "1/2").
        """
        out = []
        for rec in self.records:
            self.solver.push()
            for c in rec.pc_snapshot:
                self.solver.add(c)
            if self.solver.check() == z3.sat:
                m = self.solver.model()
                vals = {}
                for name, typ in self.mainq_params:
                    var = _input_var(name, typ)
                    vals[name] = str(m.eval(var, model_completion=True))
                out.append((rec.loc, vals))
            self.solver.pop()
        return out

    def gen_test_harness(self) -> str:
        """
        C source for a replay driver (call after run()): a main() that calls
        mainQ once per explored path, using gen_inputs(). Compile it together
        with the original program and run under a sanitizer/debugger/tracer
        to replay every symbolic path concretely — with real C semantics.
        Programs with array-valued mainQ parameters are not supported.
        """
        from fractions import Fraction

        if any(t.endswith("[]") for _, t in self.mainq_params):
            return ("/* symex_c: replay harness not supported for "
                    "array-valued mainQ parameters */\n")

        def c_lit(v: str, typ: str) -> str:
            if typ in ("double", "float") or "/" in v:
                return repr(float(Fraction(v)))
            return v

        sig = ", ".join(f"{t} {n}" for n, t in self.mainq_params) or "void"
        lines = [
            f"/* Replay harness generated by symex_c.py for {self.filename.name}",
            " * One mainQ call per explored symbolic path.",
            " * Build (original file has no main):",
            f" *   gcc {self.filename.name} harness.c -o replay",
            " * Build (original file defines main):",
            f" *   gcc -c -Dmain=_orig_main {self.filename.name} -o orig.o",
            " *   gcc orig.o harness.c -o replay",
            " */",
            f"extern {self.mainq_ret} mainQ({sig});",
            "",
            "int main(void){",
        ]
        for k, (loc, vals) in enumerate(self.gen_inputs(), 1):
            args = ", ".join(c_lit(vals[n], t) for n, t in self.mainq_params)
            lines.append(f"    mainQ({args});    /* path {k} -> {loc} */")
        lines += ["    return 0;", "}", ""]
        return "\n".join(lines)

    def unreached_locs(self) -> list[str]:
        """
        vtrace functions defined in the file but not reached on any feasible
        explored path (call after run()). A location here means DIG would
        collect no data for it — either dead code or max_depth is too small.
        """
        reached = {rec.loc for rec in self.records}
        return sorted(loc for loc in self.vtrace_params if loc not in reached)

    def parse_c_expr(self, text: str, as_bool: bool = True) -> z3.ExprRef:
        """
        Parse a C expression string (e.g. "q*y + r == x") into a z3
        expression over program-variable names — the CLI-friendly way to
        build invariants for check_inv/prove_inductive/houdini, or (with
        as_bool=False) arithmetic ranking functions for prove_termination.
        Variables are ints (matching the benchmarks' vtrace params).
        """
        ast = c_parser.CParser().parse(
            f"int __e__(void){{ return ({text}); }}")
        expr = ast.ext[0].body.block_items[0].expr
        # no safety checks while evaluating an invariant, it's not program code
        cs, co = self.check_safety, self.check_overflow
        self.check_safety = self.check_overflow = False
        try:
            val = self._eval_expr(expr, SymState())
            return _as_bool(val) if as_bool else val
        finally:
            self.check_safety, self.check_overflow = cs, co

    def houdini(self, invs: list[z3.ExprRef],
                loop: int = 0) -> list[z3.ExprRef]:
        """
        Largest subset of `invs` whose CONJUNCTION is inductive at the
        loop head: drop candidates that fail the base check, then drop
        step-violated ones to fixpoint (classic houdini). Feed DIG's
        candidate invariants in, get a sound, mutually inductive subset
        out — candidates that aren't inductive alone often survive here
        because the others support them. Unknown solver results drop the
        candidate (conservative).
        """
        if not self.func_bodies:
            self._parse()
        loops = _find_loops(self.func_bodies["mainQ"])
        assert 0 <= loop < len(loops), f"no loop #{loop} (found {len(loops)})"
        node = loops[loop]

        saved = (self.records, self.assert_results, self.safety_results)
        self.records, self.assert_results, self.safety_results = [], [], []
        try:
            entry = self._states_reaching(node)
            if not entry:
                return []
            cands = [c for c in invs if all(
                self._counterexample(st.pc, _subst_env(c, st.env))[0]
                == z3.unsat for st in entry)]

            changed = True
            while changed and cands:
                changed = False
                henv = {n: z3.Const(f"_ind_{n}", v.sort())
                        for n, v in entry[0].env.items()}
                hstate = SymState(env=dict(henv))
                cond_node, body = _loop_cond_body(node)
                graw, hstate = self._eval_expr_effects(cond_node, hstate)
                for c in cands:
                    hstate = hstate.add_constraint(_subst_env(c, henv))
                hstate = hstate.add_constraint(_as_bool(graw))
                if not self._feasible(hstate):
                    break   # loop can't iterate under the candidates
                self._hypothetical = True
                try:
                    post = [s for s in self._exec_compound(body, [hstate])
                            if s.exit not in (Exit.BREAK, Exit.RETURN)]
                finally:
                    self._hypothetical = False
                kept = []
                for c in cands:
                    if all(self._counterexample(
                            s.pc, _subst_env(c, s.env))[0] == z3.unsat
                            for s in post):
                        kept.append(c)
                    else:
                        changed = True
                cands = kept
            return cands
        finally:
            self.records, self.assert_results, self.safety_results = saved

    def prove_inductive(self, inv: z3.ExprRef, loop: int = 0,
                        k: int = 1) -> tuple[str, dict[str, str] | None]:
        """
        Prove `inv` holds at the head of the loop-th loop of mainQ (source
        order) on EVERY iteration — unbounded, unlike vassert/check_inv —
        by k-induction (default k=1):

          base: inv holds at the first k loop heads on every path in
          step: from an arbitrary run of k consecutive iterations that all
                satisfy inv (and the guard), head k+1 satisfies inv too

        Invariants that are not 1-inductive (e.g. alternating state) often
        become provable at k=2 or 3.

        inv is a z3 expression over program variable names (z3.Int("q") ...).
        Returns ("valid", None), ("base-violated", cex) with concrete inputs,
        ("step-violated", cex) with a concrete pre-iteration state over _ind_*
        variables, or ("unknown", None) on solver cutoff.

        Caveats: nested loops inside the body still unroll to max_depth (the
        step is bounded w.r.t. them), and a step counterexample may be
        unreachable — strengthen inv or raise k, as usual with k-induction.
        """
        assert k >= 1, k
        node, entry_states = self._loop_target(loop)

        # don't pollute run() results while re-executing
        saved = (self.records, self.assert_results, self.safety_results)
        self.records, self.assert_results, self.safety_results = [], [], []
        try:
            if not entry_states:
                return ("unknown", None)   # loop head unreachable
            cond_node, body = _loop_cond_body(node)
            unknown = False

            # base: heads 0 .. k-1 on every path in
            states = entry_states
            for head in range(k):
                for st in states:
                    r, cex = self._counterexample(st.pc,
                                                  _subst_env(inv, st.env))
                    if r == z3.sat:
                        return ("base-violated", cex)
                    if r == z3.unknown:
                        unknown = True
                if head < k - 1:
                    states = self._advance_iteration(states, cond_node, body)

            # step: havoc; k heads assumed to satisfy inv, prove head k
            # (vassert in the body is a no-op here — see _hypothetical)
            henv = {name: z3.Const(f"_ind_{name}", val.sort())
                    for name, val in entry_states[0].env.items()}
            states = [SymState(env=dict(henv))]
            self._hypothetical = True
            try:
                for _ in range(k):
                    states = [st.add_constraint(_subst_env(inv, st.env))
                              for st in states]
                    states = self._advance_iteration(states, cond_node, body)
            finally:
                self._hypothetical = False
            for st in states:
                r, cex = self._counterexample(st.pc, _subst_env(inv, st.env))
                if r == z3.sat:
                    return ("step-violated", cex)
                if r == z3.unknown:
                    unknown = True

            return ("unknown", None) if unknown else ("valid", None)
        finally:
            self.records, self.assert_results, self.safety_results = saved

    def prove_termination(self, rank: z3.ExprRef, loop: int = 0,
                          assume: tuple[z3.ExprRef, ...] | list = ()
                          ) -> tuple[str, dict[str, str] | None]:
        """
        Prove the loop-th loop terminates via the candidate ranking
        function `rank` (an integer expression over program variables):

          bound:    whenever the loop can iterate, rank >= 0
          decrease: every iteration strictly decreases rank (by >= 1)

        `assume` is an optional list of supporting loop INVARIANTS added to
        the havoc state — they must actually be invariants (prove them with
        prove_inductive/houdini first; the CLI's --assume does this for you)
        or the result is unsound.

        Returns ("terminates", None), ("bound-violated", cex),
        ("decrease-violated", cex) over _ind_* pre-state variables, or
        ("unknown", None).
        """
        node, entry_states = self._loop_target(loop)
        saved = (self.records, self.assert_results, self.safety_results)
        self.records, self.assert_results, self.safety_results = [], [], []
        try:
            if not entry_states:
                return ("unknown", None)
            cond_node, body = _loop_cond_body(node)
            henv = {name: z3.Const(f"_ind_{name}", val.sort())
                    for name, val in entry_states[0].env.items()}
            h = SymState(env=dict(henv))
            for inv in assume:
                h = h.add_constraint(_subst_env(inv, henv))
            pre_rank = _subst_env(rank, henv)

            graw, h = self._eval_expr_effects(cond_node, h)
            h = h.add_constraint(_as_bool(graw))   # loop iterates
            if not self._feasible(h):
                return ("terminates", None)        # loop can never iterate

            r, cex = self._counterexample(h.pc, op_module.ge(pre_rank, 0))
            if r == z3.sat:
                return ("bound-violated", cex)
            unknown = r == z3.unknown

            self._hypothetical = True
            try:
                post = self._exec_compound(body, [h])
            finally:
                self._hypothetical = False
            for s in post:
                if s.exit in (Exit.BREAK, Exit.RETURN):
                    continue   # that path leaves the loop anyway
                post_rank = _subst_env(rank, s.env)
                r, cex = self._counterexample(
                    s.pc, op_module.le(post_rank,
                                       op_module.sub(pre_rank, 1)))
                if r == z3.sat:
                    return ("decrease-violated", cex)
                unknown |= r == z3.unknown

            return ("unknown", None) if unknown else ("terminates", None)
        finally:
            self.records, self.assert_results, self.safety_results = saved

    def _loop_target(self, loop: int
                     ) -> tuple[c_ast.While | c_ast.For, list[SymState]]:
        if not self.func_bodies:
            self._parse()
        loops = _find_loops(self.func_bodies["mainQ"])
        assert 0 <= loop < len(loops), f"no loop #{loop} (found {len(loops)})"
        node = loops[loop]
        # shield run() results from the capture execution
        saved = (self.records, self.assert_results, self.safety_results)
        self.records, self.assert_results, self.safety_results = [], [], []
        try:
            entry = self._states_reaching(node)
        finally:
            self.records, self.assert_results, self.safety_results = saved
        return node, entry

    def _advance_iteration(self, states: list[SymState],
                           cond_node: c_ast.Node,
                           body: c_ast.Compound) -> list[SymState]:
        """One loop iteration: assume the guard, run the body; paths that
        exit (guard false, break, return) drop out — they have no further
        loop-head obligations."""
        nxt = []
        for st in states:
            graw, st2 = self._eval_expr_effects(cond_node, st)
            st2 = st2.add_constraint(_as_bool(graw))
            if not self._feasible(st2):
                continue
            for s in self._exec_compound(body, [st2]):
                if s.exit == Exit.CONTINUE:
                    nxt.append(s.reset_exit())
                elif s.exit == Exit.NORMAL:
                    nxt.append(s)
        return nxt

    def _states_reaching(self, node: c_ast.Node) -> list[SymState]:
        """Symbolic states at first arrival at `node` (paths stop there)."""
        self._captured = []
        self._capture_node = node
        try:
            self._exec_compound(self.func_bodies["mainQ"],
                                [self._make_init_state()])
        finally:
            self._capture_node = None
        return self._captured

    def _counterexample(self, pc: list[z3.ExprRef],
                        claim: z3.ExprRef):
        """check(pc ∧ ¬claim): (z3.sat, model-dict) | (unsat|unknown, None)."""
        self.solver.push()
        for c in pc:
            self.solver.add(c)
        self.solver.add(z3.Not(claim))
        r = self.solver.check()
        cex = None
        if r == z3.sat:
            m = self.solver.model()
            cex = {d.name(): str(m[d]) for d in m.decls()}
        self.solver.pop()
        return r, cex

    def check_inv(self, loc: str,
                  inv: z3.ExprRef) -> tuple[str, dict[str, str] | None]:
        """
        Check a candidate invariant at a vtrace location (call after run()):
        pc ∧ slocal ⇒ inv must hold on every collected path. inv is a z3
        expression over the vtrace parameter names and/or X_* input symbols.

        Returns ("valid", None), ("violated", cex) with a concrete
        counterexample assignment, or ("unknown", None) on solver cutoff.
        Bounded by max_depth unrolling, like vassert.
        """
        status = "valid"
        for rloc, pc, slocal in self._z3_records():
            if rloc != loc:
                continue
            self.solver.push()
            self.solver.add(pc, slocal, z3.Not(inv))
            r = self.solver.check()
            cex = (self.solver.model() if r == z3.sat else None)
            self.solver.pop()
            if r == z3.sat:
                return ("violated", {d.name(): str(cex[d]) for d in cex.decls()})
            if r == z3.unknown:
                status = "unknown"
        return (status, None)

    # ── parsing ───────────────────────────────────────────────────────

    def _parse(self) -> c_ast.FileAST:
        src = _preprocess(self.filename.read_text())

        parser = c_parser.CParser()
        ast = parser.parse(src, self.filename.name)  # name -> nicer coords
        self._register_structs(ast)

        for node in ast.ext:
            if not isinstance(node, c_ast.FuncDef):
                # global variable declarations (skip prototypes & struct defs)
                if (isinstance(node, c_ast.Decl) and node.name
                        and not isinstance(node.type,
                                           (c_ast.FuncDecl, c_ast.Struct))):
                    self.global_decls.append(node)
                    self.global_names.add(node.name)
                continue
            name = node.decl.name
            self.func_bodies[name] = node.body
            args = node.decl.type.args
            self.func_params[name] = list(args.params) if args else []

            if name == "mainQ":
                self.mainq_ret = _type_name(node.decl) or "int"
                if node.decl.type.args:
                    self.mainq_params = [
                        (p.name, _param_ctype(p))
                        for p in node.decl.type.args.params
                    ]

            if name.startswith("vtrace") and node.decl.type.args:
                self.vtrace_params[name] = [
                    p.name for p in node.decl.type.args.params
                ]

        assert "mainQ" in self.func_bodies, "mainQ not found in C file"
        return ast

    def _make_init_state(self) -> SymState:
        state = SymState()
        # globals first (zero-initialized per C static-storage rules)
        for g in self.global_decls:
            state = self._declare_global(g, state)
        for name, typ in self.mainq_params:
            state.env[name] = _input_var(name, typ)
        if self.check_overflow:
            # inputs are real C ints: constrain them to the int range so
            # overflow findings reflect the program, not unbounded inputs
            for name, typ in self.mainq_params:
                if typ in ("int", "long", "short", "char"):
                    v = state.env[name]
                    state.pc.append(z3.And(op_module.ge(v, INT_MIN),
                                           op_module.le(v, INT_MAX)))
        return state

    def _declare_global(self, node: c_ast.Decl, state: SymState) -> SymState:
        """Globals: explicit initializer, else 0 (C static storage)."""
        sname = self._struct_of(node)
        if sname is not None:
            return self._declare_struct_var(node, sname, state)
        if isinstance(node.type, c_ast.ArrayDecl):
            return self._declare_array_var(node, state)
        is_real = _type_name(node) in ("double", "float")
        if node.init is not None:
            val = self._eval_expr(node.init, state)
            val = _to_real(val) if is_real else _to_int(val)
        else:
            val = z3.RealVal(0) if is_real else z3.IntVal(0)
        return state.set_var(node.name, val)

    # ── statement execution ───────────────────────────────────────────

    def _exec_compound(self,
                       node: c_ast.Compound,
                       states: list[SymState]) -> list[SymState]:
        if not node or not node.block_items:
            return states

        active = states
        done: list[SymState] = []

        for stmt in node.block_items:
            if not active:
                break
            new_states = self._exec_stmt(stmt, active)
            active = []
            for s in new_states:
                if s.exit == Exit.NORMAL:
                    active.append(s)
                else:
                    done.append(s)

        return done + active

    def _exec_stmt(self,
                   node: c_ast.Node,
                   states: list[SymState]) -> list[SymState]:
        if not states:
            return []

        if node is self._capture_node:
            # prove_inductive(): collect loop-entry states, stop these paths
            if isinstance(node, c_ast.For) and node.init:
                states = self._exec_stmt(node.init, states)
            self._captured.extend(states)
            return []

        if getattr(node, "coord", None):
            self._cur_coord = str(node.coord)

        if isinstance(node, c_ast.Compound):
            return self._exec_compound(node, states)

        if isinstance(node, c_ast.Decl):
            return self._exec_decl(node, states)

        if isinstance(node, c_ast.Assignment):
            return self._exec_assign(node, states)

        if isinstance(node, c_ast.If):
            return self._exec_if(node, states)

        if isinstance(node, c_ast.While):
            return self._exec_while(node, states)

        if isinstance(node, c_ast.For):
            return self._exec_for(node, states)

        if isinstance(node, c_ast.FuncCall):
            return self._exec_call(node, states)

        if isinstance(node, c_ast.Break):
            return [s.with_exit(Exit.BREAK) for s in states]

        if isinstance(node, c_ast.Continue):
            return [s.with_exit(Exit.CONTINUE) for s in states]

        if isinstance(node, c_ast.Return):
            result = []
            for s in states:
                val = None
                if node.expr is not None:
                    try:
                        val, s = self._eval_expr_effects(node.expr, s)
                    except NotImplementedError:
                        val = None   # unsupported return expr: value unknown
                result.append(replace(s, exit=Exit.RETURN, ret=val))
            return result

        # Unary expression statement (e.g., i++, i--)
        # pycparser uses "p++"/"p--" for postfix and "++"/"--" for prefix
        if isinstance(node, c_ast.UnaryOp) and node.op in ("p++", "p--", "++", "--"):
            return self._exec_incr_stmt(node, states)

        # Unknown: pass through
        return states

    def _model_call(self, node: c_ast.FuncCall,
                    state: SymState) -> tuple[z3.ExprRef, list[z3.ExprRef]] | None:
        """
        Model a pure helper/library call as a fresh symbolic value plus the
        path constraints that define it. Returns (value, constraints) or None
        if the call isn't modeled. Lets symex handle programs like knuth that
        call e.g. isqrt without inlining the helper's loop.
        """
        if not isinstance(node.name, c_ast.ID):
            return None
        fname = node.name.name
        args = node.args.exprs if node.args else []
        if fname == "isqrt" and len(args) == 1:
            x = self._eval_expr(args[0], state)
            s = z3.Int(self._fresh_name("isqrt"))
            # integer sqrt: s >= 0 and s*s <= x < (s+1)*(s+1)
            cons = [s >= 0, s * s <= x, (s + 1) * (s + 1) > x]
            return s, cons
        return None

    def _fresh_name(self, prefix: str) -> str:
        self._fresh_ctr += 1
        return f"_{prefix}_{self._fresh_ctr}"

    _SPECIAL_FUNCS = ("mainQ", "main", "vassume", "vassert")

    def _inline_call(self, node: c_ast.FuncCall,
                     state: SymState
                     ) -> list[tuple[z3.ExprRef, SymState]] | None:
        """
        Inline a call to a user-defined function: bind arguments, execute
        the body (loops unroll as usual), and yield one (return value,
        state) pair per path through the callee. The caller's locals are
        restored afterwards; only globals keep the callee's writes (there
        are no pointers). Returns None if the call isn't inlinable;
        recursion beyond MAX_INLINE_DEPTH yields a fresh symbolic value.
        """
        if not isinstance(node.name, c_ast.ID):
            return None
        fname = node.name.name
        if (fname not in self.func_bodies or fname in self._SPECIAL_FUNCS
                or fname.startswith("vtrace")):
            return None
        if self._inline_depth >= self.MAX_INLINE_DEPTH:
            return [(z3.Int(self._fresh_name(fname)), state)]

        env = dict(state.env)
        args = node.args.exprs if node.args else []
        for p, a in zip(self.func_params[fname], args):
            val = self._eval_expr(a, state)
            if isinstance(p.type, (c_ast.ArrayDecl, c_ast.PtrDecl)):
                env[p.name] = val   # arrays pass through
            elif _type_name(p) in ("double", "float"):
                env[p.name] = _to_real(val)
            else:
                env[p.name] = _to_int(val)

        self._inline_depth += 1
        try:
            outs = self._exec_compound(self.func_bodies[fname],
                                       [replace(state, env=env, loop_depth=0)])
        finally:
            self._inline_depth -= 1

        results = []
        for s in outs:
            ret = s.ret if (s.exit == Exit.RETURN and s.ret is not None) \
                else z3.Int(self._fresh_name(fname))
            # restore caller locals; keep the callee's global writes and pc
            new_env = dict(state.env)
            for g in self.global_names:
                if g in s.env:
                    new_env[g] = s.env[g]
            results.append((ret, replace(s, env=new_env, exit=state.exit,
                                         ret=None,
                                         loop_depth=state.loop_depth)))
        return results

    # ── structs ───────────────────────────────────────────────────────
    # Structs are lowered field-sensitively: `struct P p` puts one env
    # entry per (nested) field under a mangled name like "p.x". No heap:
    # struct pointers and '->' are not supported.

    def _register_structs(self, ast: c_ast.FileAST) -> None:
        """Record top-level struct definitions and struct typedefs."""
        for node in ast.ext:
            if isinstance(node, c_ast.Typedef):
                inner = getattr(node.type, "type", None)
                if isinstance(inner, c_ast.Struct) and inner.decls:
                    self.struct_defs[node.name] = inner.decls
                    if inner.name:
                        self.struct_defs[f"struct {inner.name}"] = inner.decls
            elif (isinstance(node, c_ast.Decl)
                  and isinstance(node.type, c_ast.Struct)
                  and node.type.decls):
                self.struct_defs[f"struct {node.type.name}"] = node.type.decls

    def _struct_of(self, decl: c_ast.Decl) -> str | None:
        """Struct type key of a Decl, registering inline definitions."""
        t = decl.type
        if not isinstance(t, c_ast.TypeDecl):
            return None
        it = t.type
        if isinstance(it, c_ast.Struct):
            key = f"struct {it.name}"
            if it.decls:  # definition combined with the declaration
                self.struct_defs[key] = it.decls
            return key if key in self.struct_defs else None
        if isinstance(it, c_ast.IdentifierType) and it.names[-1] in self.struct_defs:
            return it.names[-1]
        return None

    def _field_paths(self, sname: str,
                     prefix: str = "") -> list[tuple[str, c_ast.Decl]]:
        """Flattened (path, field_decl) pairs, recursing into nested structs."""
        out = []
        for f in self.struct_defs[sname]:
            path = f"{prefix}{f.name}"
            nested = self._struct_of(f)
            if nested is not None:
                out.extend(self._field_paths(nested, f"{path}."))
            else:
                out.append((path, f))
        return out

    def _declare_struct_var(self, node: c_ast.Decl, sname: str,
                            state: SymState) -> SymState:
        if node.name is None:      # bare `struct S {...};` type definition
            return state
        self.struct_vars[node.name] = sname
        inits = (node.init.exprs
                 if isinstance(node.init, c_ast.InitList) else [])
        for k, (path, f) in enumerate(self._field_paths(sname)):
            mangled = f"{node.name}.{path}"
            is_real = _type_name(f) in ("double", "float")
            if isinstance(f.type, c_ast.ArrayDecl):
                self._note_array_size(mangled, f.type, None)
                val = z3.Array(f"_uninit_{mangled}", z3.IntSort(),
                               _REAL if is_real else z3.IntSort())
            elif k < len(inits):   # positional {…} initializer, flat only
                v = self._eval_expr(inits[k], state)
                val = _to_real(v) if is_real else _to_int(v)
            else:
                val = (z3.Real(f"_uninit_{mangled}") if is_real
                       else z3.Int(f"_uninit_{mangled}"))
            state = state.set_var(mangled, val)
        return state

    # ── arrays / lvalues ──────────────────────────────────────────────

    def _declare_array_var(self, node: c_ast.Decl,
                           state: SymState) -> SymState:
        is_real = _type_name(node) in ("double", "float")
        esort = _REAL if is_real else z3.IntSort()
        self._note_array_size(node.name, node.type,
                              node.init if isinstance(node.init,
                                                      c_ast.InitList) else None)
        if isinstance(node.init, c_ast.InitList):
            # int a[3] = {1,2}: elements not mentioned are 0 in C
            arr = z3.K(z3.IntSort(),
                       z3.RealVal(0) if is_real else z3.IntVal(0))
            for k, e in enumerate(node.init.exprs):
                v = self._eval_expr(e, state)
                arr = z3.Store(arr, k, _to_real(v) if is_real else _to_int(v))
        else:
            arr = z3.Array(f"_uninit_{node.name}", z3.IntSort(), esort)
        return state.set_var(node.name, arr)

    def _note_array_size(self, name: str, adecl: c_ast.ArrayDecl,
                         init: c_ast.InitList | None) -> None:
        """Record a declared array's element count for bounds checking."""
        dim = getattr(adecl, "dim", None)
        if isinstance(dim, c_ast.Constant):
            self.array_sizes[name] = int(dim.value, 0)
        elif init is not None:
            self.array_sizes[name] = len(init.exprs)

    def _lvalue_name(self, node: c_ast.Node) -> str | None:
        """Mangled env name of an lvalue: x, p.x, p.inner.y."""
        if isinstance(node, c_ast.ID):
            return node.name
        if isinstance(node, c_ast.StructRef) and node.type == ".":
            base = self._lvalue_name(node.name)
            return f"{base}.{node.field.name}" if base else None
        return None

    def _assign_lvalue(self, state: SymState, lv: c_ast.Node,
                       val: z3.ExprRef) -> SymState:
        """Assign to a scalar (x, p.x) or an array element (a[i], p.a[i])."""
        if isinstance(lv, c_ast.ArrayRef):
            base = self._lvalue_name(lv.name)
            arr = state.env.get(base) if base else None
            if arr is None or not z3.is_array(arr):
                return state
            idx = _to_int(self._eval_expr(lv.subscript, state))
            self._check_bounds(base, idx, state)
            v = (_to_real(val) if arr.sort().range() == _REAL
                 else _to_int(val))
            self._check_overflow_val(v, state)
            return state.set_var(base, z3.Store(arr, idx, v))
        name = self._lvalue_name(lv)
        if name is None:
            return state
        self._check_overflow_val(val, state)
        return state.set_var(name, val)

    def _exec_decl(self,
                   node: c_ast.Decl,
                   states: list[SymState]) -> list[SymState]:
        result = []
        for state in states:
            if isinstance(node.init, c_ast.FuncCall):
                modeled = self._model_call(node.init, state)
                if modeled is not None:
                    val, cons = modeled
                    ns = state
                    for c in cons:
                        ns = ns.add_constraint(c)
                    result.append(ns.set_var(node.name, val))
                    continue
                inlined = self._inline_call(node.init, state)
                if inlined is not None:
                    declared = _type_name(node)
                    for val, ns in inlined:
                        if declared in ("double", "float"):
                            val = _to_real(val)
                        elif declared in ("int", "long", "short", "char"):
                            val = _to_int(val)
                        self._check_overflow_val(val, ns)
                        result.append(ns.set_var(node.name, val))
                    continue
            sname = self._struct_of(node)
            if sname is not None:
                result.append(self._declare_struct_var(node, sname, state))
                continue
            if isinstance(node.type, c_ast.ArrayDecl):
                result.append(self._declare_array_var(node, state))
                continue
            declared = _type_name(node)
            is_real_decl = declared in ("double", "float")
            if node.init is not None:
                val, state = self._eval_expr_effects(node.init, state)
                # honor the declared type (e.g. `double x = a;` makes x real)
                if is_real_decl:
                    val = _to_real(val)
                elif declared in ("int", "long", "short", "char"):
                    val = _to_int(val)
            else:
                # Uninitialised — use a fresh symbolic var of the declared sort
                val = (z3.Real(f"_uninit_{node.name}") if is_real_decl
                       else z3.Int(f"_uninit_{node.name}"))
            if node.init is not None:
                self._check_overflow_val(val, state)
            result.append(state.set_var(node.name, val))
        return result

    def _exec_assign(self,
                     node: c_ast.Assignment,
                     states: list[SymState]) -> list[SymState]:
        result = []
        for state in states:
            # modeled calls (e.g. s = isqrt(n)) add defining constraints
            if node.op == "=" and isinstance(node.rvalue, c_ast.FuncCall):
                modeled = self._model_call(node.rvalue, state)
                if modeled is not None:
                    val, cons = modeled
                    ns = state
                    for c in cons:
                        ns = ns.add_constraint(c)
                    result.append(self._assign_lvalue(ns, node.lvalue, val))
                    continue
                inlined = self._inline_call(node.rvalue, state)
                if inlined is not None:
                    for val, ns in inlined:
                        result.append(
                            self._assign_lvalue(ns, node.lvalue, val))
                    continue
            # whole-struct copy: q = p duplicates every field
            if (node.op == "=" and isinstance(node.lvalue, c_ast.ID)
                    and isinstance(node.rvalue, c_ast.ID)
                    and node.rvalue.name in self.struct_vars):
                lhs, rhs = node.lvalue.name, node.rvalue.name
                self.struct_vars.setdefault(lhs, self.struct_vars[rhs])
                ns = state
                for path, _f in self._field_paths(self.struct_vars[rhs]):
                    src = ns.env.get(f"{rhs}.{path}")
                    if src is not None:
                        ns = ns.set_var(f"{lhs}.{path}", src)
                result.append(ns)
                continue
            rhs, state = self._eval_expr_effects(node.rvalue, state)
            if node.op == "=":
                val = rhs
            elif node.op in ("+=", "-=", "*=", "/=", "%="):
                lhs = self._eval_expr(node.lvalue, state)
                val = self._apply_binary(node.op[0], lhs, rhs, state)
            else:
                val = rhs
            result.append(self._assign_lvalue(state, node.lvalue, val))
        return result

    def _exec_incr_stmt(self,
                        node: c_ast.UnaryOp,
                        states: list[SymState]) -> list[SymState]:
        delta = 1 if node.op in ("p++", "++") else -1
        result = []
        for state in states:
            cur = self._eval_expr(node.expr, state)
            result.append(self._assign_lvalue(
                state, node.expr, op_module.add(cur, delta)))
        return result

    def _exec_if(self,
                 node: c_ast.If,
                 states: list[SymState]) -> list[SymState]:
        result = []
        for state in states:
            raw, state = self._eval_expr_effects(node.cond, state)
            cond = _as_bool(raw)

            # True branch
            then_states: list[SymState] = []
            true_state = state.add_constraint(cond).with_trace(
                f"{node.coord} if-true ({_short(cond)})")
            if self._feasible(true_state):
                then_states = self._exec_stmt(node.iftrue, [true_state])

            # False branch
            else_states: list[SymState] = []
            false_state = state.add_constraint(z3.Not(cond)).with_trace(
                f"{node.coord} if-false ({_short(cond)})")
            if self._feasible(false_state):
                if node.iffalse:
                    else_states = self._exec_stmt(node.iffalse, [false_state])
                else:
                    else_states = [false_state]

            if self.merge_states:
                merged = self._try_merge(state, cond, then_states, else_states)
                if merged is not None:
                    result.append(merged)
                    continue
            result.extend(then_states)
            result.extend(else_states)

        return result

    def _try_merge(self, parent: SymState, cond: z3.ExprRef,
                   then_states: list[SymState],
                   else_states: list[SymState]) -> SymState | None:
        """
        Merge a simple if/else diamond into one state with If-valued vars:
        applies only when each branch produced exactly one straight-line
        state (no extra constraints beyond the branch condition, no
        break/continue/return, no loop iterations inside). Turns 2^n paths
        over n sequential diamonds into 1, at the cost of ite terms.
        """
        if len(then_states) != 1 or len(else_states) != 1:
            return None
        t, e = then_states[0], else_states[0]
        for s in (t, e):
            if (s.exit != Exit.NORMAL
                    or s.loop_depth != parent.loop_depth
                    or len(s.pc) != len(parent.pc) + 1):
                return None
        env = {}
        for k in t.env.keys() | e.env.keys():
            vt, ve = t.env.get(k), e.env.get(k)
            if vt is None or ve is None:
                env[k] = vt if ve is None else ve
            elif vt.eq(ve):
                env[k] = vt
            else:
                if vt.sort() != ve.sort():
                    if z3.is_arith(vt) and z3.is_arith(ve):
                        vt, ve = _coerce(vt, ve)
                    else:
                        return None
                env[k] = z3.If(cond, vt, ve)
        return replace(parent, env=env,
                       trace=parent.trace + ("(merged if/else)",))

    def _exec_while(self,
                    node: c_ast.While,
                    states: list[SymState],
                    _iter: int = 0) -> list[SymState]:
        """
        Unroll the while loop up to max_depth total iterations.
        Each unique state tracks its own loop_depth so paths share depth budgets.
        """
        if not states:
            return []

        # Hard cap to prevent explosion
        if len(states) > self.MAX_STATES:
            states = states[:self.MAX_STATES]

        result: list[SymState] = []       # states that exited the loop
        continuing: list[SymState] = []   # states that re-enter

        cond_is_true = _is_const_true(node.cond)

        for state in states:
            if state.loop_depth >= self.max_depth:
                # Depth exhausted: treat loop as terminated
                if not cond_is_true:
                    raw, state = self._eval_expr_effects(node.cond, state)
                    exit_s = state.add_constraint(
                        z3.Not(_as_bool(raw))).with_trace(
                        f"{node.coord} loop-exit (depth cap)")
                    if self._feasible(exit_s):
                        result.append(exit_s)
                # else: while(1) at max depth — dead path, discard
                continue

            if cond_is_true:
                # while(1): only break exits
                body_states = self._exec_compound(
                    node.stmt,
                    [state.inc_loop().with_trace(
                        f"{node.coord} loop-iter {state.loop_depth + 1}")])
                for s in body_states:
                    if s.exit == Exit.BREAK:
                        result.append(s.reset_exit())
                    elif s.exit == Exit.CONTINUE:
                        continuing.append(s.reset_exit())
                    elif s.exit == Exit.NORMAL:
                        continuing.append(s)
                    else:  # RETURN
                        result.append(s)
            else:
                # the condition is fully evaluated whether the loop is
                # entered or exited, so its side effects apply to both
                raw, state = self._eval_expr_effects(node.cond, state)
                cond = _as_bool(raw)

                # Exit branch (condition false)
                exit_s = state.add_constraint(z3.Not(cond)).with_trace(
                    f"{node.coord} loop-exit ({_short(cond)})")
                if self._feasible(exit_s):
                    result.append(exit_s)

                # Enter branch (condition true)
                enter_s = state.add_constraint(cond).inc_loop().with_trace(
                    f"{node.coord} loop-iter {state.loop_depth + 1}")
                if self._feasible(enter_s):
                    body_states = self._exec_compound(node.stmt, [enter_s])
                    for s in body_states:
                        if s.exit == Exit.BREAK:
                            result.append(s.reset_exit())
                        elif s.exit == Exit.CONTINUE:
                            continuing.append(s.reset_exit())
                        elif s.exit == Exit.NORMAL:
                            continuing.append(s)
                        else:
                            result.append(s)

        # Recurse for states re-entering the loop
        result.extend(self._exec_while(node, continuing, _iter + 1))
        return result

    def _exec_for(self,
                  node: c_ast.For,
                  states: list[SymState]) -> list[SymState]:
        # Desugar: init; while(cond) { body; next; }
        if node.init:
            states = self._exec_stmt(node.init, states)

        cond = node.cond or c_ast.Constant("int", "1")
        body_items = node.stmt.block_items or [] if isinstance(node.stmt, c_ast.Compound) else [node.stmt]
        if node.next:
            body_items = body_items + [node.next]

        fake_while = c_ast.While(cond=cond, stmt=c_ast.Compound(block_items=body_items))
        return self._exec_while(fake_while, states)

    def _exec_call(self,
                   node: c_ast.FuncCall,
                   states: list[SymState]) -> list[SymState]:
        fname = node.name.name if isinstance(node.name, c_ast.ID) else None
        if fname is None:
            return states

        if fname == "vassume":
            result = []
            for state in states:
                raw, state = self._eval_expr_effects(node.args.exprs[0], state)
                new_state = state.add_constraint(_as_bool(raw)).with_trace(
                    f"{node.coord} assume ({_short(raw)})")
                if self._feasible(new_state):
                    result.append(new_state)
            return result

        if fname == "vassert":
            if self._hypothetical:
                return states
            result = []
            for state in states:
                raw, state = self._eval_expr_effects(node.args.exprs[0], state)
                cond = _as_bool(raw)
                self.assert_results.append(self._check_assert(node, cond, state))
                # assume-after-assert: downstream code sees cond as true;
                # drop the path if cond contradicts it entirely
                new_state = state.add_constraint(cond)
                if self._feasible(new_state):
                    result.append(new_state)
            return result

        if fname.startswith("vtrace") and fname in self.vtrace_params:
            params = self.vtrace_params[fname]
            for state in states:
                vals = {}
                for pname, arg in zip(params,
                                      node.args.exprs if node.args else []):
                    vals[pname] = self._eval_expr(arg, state)
                self.records.append(PathRecord(
                    loc=fname,
                    param_names=params,
                    env_snapshot=vals,
                    pc_snapshot=list(state.pc),
                ))
            return states

        # user-defined helpers: inline (only global writes survive the call)
        if fname in self.func_bodies and fname not in self._SPECIAL_FUNCS:
            result = []
            for state in states:
                inlined = self._inline_call(node, state)
                if inlined is None:
                    result.append(state)
                else:
                    result.extend(ns for _val, ns in inlined)
            return result

        # Ignore: printf, atoi, unknown functions
        return states

    def _check_assert(self, node: c_ast.FuncCall, cond: z3.ExprRef,
                      state: SymState) -> AssertResult:
        """Check pc ⇒ cond; a sat model of pc ∧ ¬cond is a counterexample."""
        self.solver.push()
        for c in state.pc:
            self.solver.add(c)
        self.solver.add(z3.Not(cond))
        r = self.solver.check()
        if r == z3.sat:
            m = self.solver.model()
            status = "violated"
            cex = {d.name(): str(m[d]) for d in m.decls()}
        else:
            status = "valid" if r == z3.unsat else "unknown"
            cex = None
        self.solver.pop()
        return AssertResult(coord=str(node.coord), cond=cond,
                            status=status, cex=cex, trace=state.trace)

    # ── expression evaluation ─────────────────────────────────────────

    def _eval_expr_effects(self, node: c_ast.Node,
                           state: SymState) -> tuple[z3.ExprRef, SymState]:
        """
        Evaluate an expression and apply any side effects it contains
        (i++, --j) to the state, so e.g. `while (i++ < n)` advances i.
        Effects apply after the whole expression is evaluated — there is
        no intra-expression sequencing, and && / || do not short-circuit
        the right operand's effects.
        """
        self._pending_effects = []
        val = self._eval_expr(node, state)
        for name, delta in self._pending_effects:
            cur = state.env.get(name, z3.Int(name))
            state = state.set_var(name, op_module.add(cur, delta))
        self._pending_effects = []
        return val, state

    def _eval_expr(self, node: c_ast.Node, state: SymState) -> z3.ExprRef:
        if isinstance(node, c_ast.Constant):
            if node.type in ("double", "float"):
                # exact rational, e.g. "3.25" -> 13/4
                return z3.RealVal(node.value.rstrip("fF"))
            return z3.IntVal(int(node.value, 0))

        if isinstance(node, c_ast.ID):
            v = state.env.get(node.name)
            if v is None:
                # Treat as a fresh symbolic var (handles forward-declared globals)
                v = z3.Int(node.name)
            return v

        if isinstance(node, c_ast.UnaryOp):
            return self._eval_unary(node, state)

        if isinstance(node, c_ast.BinaryOp):
            return self._eval_binary(node, state)

        if isinstance(node, c_ast.Cast):
            val = self._eval_expr(node.expr, state)
            tn = _type_name(node.to_type)
            if tn in ("double", "float"):
                return _to_real(val)
            if tn in ("int", "long", "short", "char"):
                return _to_int(val)
            return val

        if isinstance(node, c_ast.ArrayRef):
            base = self._lvalue_name(node.name)
            idx = _to_int(self._eval_expr(node.subscript, state))
            self._check_bounds(base, idx, state)
            arr = state.env.get(base) if base else None
            if arr is None or not z3.is_array(arr):
                # forward-declared global array: fresh symbolic int array
                arr = z3.Array(base or self._fresh_name("arr"),
                               z3.IntSort(), z3.IntSort())
            return z3.Select(arr, idx)

        if isinstance(node, c_ast.StructRef):
            if node.type != ".":
                raise NotImplementedError(
                    "struct pointer access '->' not supported (no heap model)")
            name = self._lvalue_name(node)
            v = state.env.get(name) if name else None
            return v if v is not None else z3.Int(name or
                                                  self._fresh_name("field"))

        if isinstance(node, c_ast.TernaryOp):
            cond = _as_bool(self._eval_expr(node.cond, state))
            t = self._eval_expr(node.iftrue, state)
            f = self._eval_expr(node.iffalse, state)
            t, f = _coerce(t, f)
            return z3.If(cond, t, f)

        if isinstance(node, c_ast.FuncCall) and isinstance(node.name, c_ast.ID):
            fname = node.name.name
            # nondeterministic input: fresh symbolic value, no constraints
            if fname in ("unknown", "nondet") or fname.startswith("nondet_"):
                return z3.Int(self._fresh_name(fname))

        if isinstance(node, c_ast.ExprList):
            # Comma expression: evaluate all, return last
            result = z3.IntVal(0)
            for e in node.exprs:
                result = self._eval_expr(e, state)
            return result

        raise NotImplementedError(f"Unsupported expression: {type(node).__name__}: {node}")

    def _eval_unary(self, node: c_ast.UnaryOp, state: SymState) -> z3.ExprRef:
        # p++/++p as expressions: post yields the old value, pre the new one;
        # the increment itself is recorded and applied by _eval_expr_effects
        # (pycparser uses "p++"/"p--" for postfix and "++"/"--" for prefix)
        if node.op in ("p++", "++", "p--", "--"):
            val = self._eval_expr(node.expr, state)
            if isinstance(node.expr, c_ast.ID):
                delta = 1 if node.op in ("p++", "++") else -1
                self._pending_effects.append((node.expr.name, delta))
                if node.op in ("++", "--"):
                    return op_module.add(val, delta)
            return val

        operand = self._eval_expr(node.expr, state)
        ops = {
            "-": lambda x: -x,
            "+": lambda x: x,
            "!": lambda x: z3.Not(_as_bool(x)),
            "~": lambda x: -x - 1,  # bitwise NOT approximation for integers
        }
        fn = ops.get(node.op)
        if fn is None:
            raise NotImplementedError(f"Unary op '{node.op}' not supported")
        return fn(operand)

    def _eval_binary(self, node: c_ast.BinaryOp, state: SymState) -> z3.ExprRef:
        # Short-circuit: defer right-side eval for && and ||
        if node.op == "&&":
            lhs = _as_bool(self._eval_expr(node.left, state))
            rhs = _as_bool(self._eval_expr(node.right, state))
            return z3.And(lhs, rhs)
        if node.op == "||":
            lhs = _as_bool(self._eval_expr(node.left, state))
            rhs = _as_bool(self._eval_expr(node.right, state))
            return z3.Or(lhs, rhs)

        lhs = self._eval_expr(node.left, state)
        rhs = self._eval_expr(node.right, state)
        return self._apply_binary(node.op, lhs, rhs, state)

    def _apply_binary(self, op: str, lhs: z3.ExprRef, rhs: z3.ExprRef,
                      state: SymState) -> z3.ExprRef:
        # mixed int/real: promote to a common sort so z3 doesn't reject the op
        # (and so "/" becomes real division when either operand is real)
        if op != "%":
            lhs, rhs = _coerce(lhs, rhs)

        if op in ("/", "%") and self.check_safety:
            self._record_safety("division-by-zero",
                                op_module.ne(rhs, 0), state)
        if op == "/" and not _is_real(lhs):
            return self._c_int_div(lhs, rhs, state)
        if op == "%":
            return self._c_int_mod(lhs, rhs, state)

        arith = {
            "+": op_module.add,
            "-": op_module.sub,
            "*": op_module.mul,
            "/": op_module.truediv,   # reals only; int "/" handled above
        }
        cmp = {
            "<":  op_module.lt,
            "<=": op_module.le,
            ">":  op_module.gt,
            ">=": op_module.ge,
            "==": op_module.eq,
            "!=": op_module.ne,
        }
        if op in arith:
            return arith[op](lhs, rhs)
        if op in cmp:
            return cmp[op](lhs, rhs)

        raise NotImplementedError(f"Binary op '{op}' not supported")

    # C "/" and "%" on ints truncate toward zero (result/remainder take the
    # dividend's sign); z3's Int "/" and "%" follow SMT-LIB (remainder always
    # non-negative). They agree when dividend >= 0 and divisor > 0 — the
    # common, vassume'd case — so keep the plain form there (it also keeps
    # existing symstates byte-identical). Otherwise emit a corrected term.

    def _c_int_div(self, a: z3.ExprRef, b: z3.ExprRef,
                   state: SymState) -> z3.ExprRef:
        if self._entailed(state, z3.And(a >= 0, b > 0)):
            return a / b
        # trunc(a/b) = euclid(a/b) + (0 if a>=0 or b|a else (1 if b>0 else -1))
        return a / b + z3.If(z3.Or(a % b == 0, a >= 0),
                             z3.IntVal(0),
                             z3.If(b > 0, z3.IntVal(1), z3.IntVal(-1)))

    def _c_int_mod(self, a: z3.ExprRef, b: z3.ExprRef,
                   state: SymState) -> z3.ExprRef:
        if self._entailed(state, z3.And(a >= 0, b > 0)):
            return a % b
        # C remainder = euclid remainder shifted into the dividend's sign
        return z3.If(z3.Or(a % b == 0, a >= 0),
                     a % b,
                     a % b - z3.If(b > 0, b, -b))

    # ── feasibility ───────────────────────────────────────────────────

    def _record_safety(self, kind: str, safe: z3.ExprRef,
                       state: SymState) -> None:
        """
        Auto safety check: if the path does not entail `safe`, record a
        violation with a concrete counterexample input (or "unknown" on
        solver cutoff). Proven-safe sites are not recorded. Callers gate
        on check_safety / check_overflow.
        """
        if self._entailed(state, safe):
            return
        self.solver.push()
        for c in state.pc:
            self.solver.add(c)
        self.solver.add(z3.Not(safe))
        r = self.solver.check()
        if r == z3.sat:
            m = self.solver.model()
            res = AssertResult(coord=self._cur_coord, cond=safe,
                               status="violated", kind=kind,
                               cex={d.name(): str(m[d]) for d in m.decls()},
                               trace=state.trace)
        else:
            res = AssertResult(coord=self._cur_coord, cond=safe,
                               status="unknown", kind=kind,
                               trace=state.trace)
        self.solver.pop()
        self.safety_results.append(res)

    def _check_overflow_val(self, val: z3.ExprRef, state: SymState) -> None:
        if (not self.check_overflow or z3.is_array(val)
                or val.sort() != z3.IntSort()):
            return
        self._record_safety(
            "signed-overflow",
            z3.And(op_module.ge(val, INT_MIN), op_module.le(val, INT_MAX)),
            state)

    def _check_bounds(self, base: str | None, idx: z3.ExprRef,
                      state: SymState) -> None:
        if self.check_safety and base is not None and base in self.array_sizes:
            n = self.array_sizes[base]
            self._record_safety(
                "array-bounds",
                z3.And(op_module.ge(idx, 0), op_module.lt(idx, n)), state)

    def _entailed(self, state: SymState, claim: z3.ExprRef) -> bool:
        """pc ⇒ claim, conservatively (unknown counts as not entailed)."""
        self.solver.push()
        for c in state.pc:
            self.solver.add(c)
        self.solver.add(z3.Not(claim))
        result = self.solver.check()
        self.solver.pop()
        return result == z3.unsat

    def _feasible(self, state: SymState) -> bool:
        if not state.pc:
            return True
        self.solver.push()
        for c in state.pc:
            self.solver.add(c)
        result = self.solver.check()
        self.solver.pop()
        # If unknown (timeout), be optimistic and keep the path
        return result != z3.unsat

    # ── output ─────────────────────────────────────────────────────────

    def _z3_records(self) -> list[tuple[str, z3.BoolRef, z3.BoolRef]]:
        """
        Return list of (loc, pc, slocal) tuples of z3 boolean expressions.

        pc is the conjunction of the path-condition constraints (z3 True if
        unconstrained); slocal is the conjunction of `var == expr` equalities
        over the variables in the vtrace param list.
        """
        out = []
        for rec in self.records:
            eqs = []
            for name in rec.param_names:
                v = rec.env_snapshot.get(name)
                # vtrace params must be numeric scalars (array-valued args
                # have no scalar symstate var to equate)
                if v is None or not isinstance(v, z3.ArithRef):
                    continue
                # the symstate var must match the value's sort (Real for doubles)
                var = z3.Real(name) if _is_real(v) else z3.Int(name)
                eqs.append(var == v)
            if not eqs:
                continue
            # Leave pc/slocal unsimplified: PathCond.expr and PCs.myexpr already
            # z3.simplify at the right granularity, and an eager per-record
            # simplify here produces a form z3 solves much slower downstream
            # (~4x in the eqt check phase on cohendiv).
            slocal = z3.And(eqs)
            pc = z3.And(rec.pc_snapshot)   # z3.And([]) is True
            out.append((rec.loc, pc, slocal))
        return out


# ─────────────────────────────────────────────── utilities ──────────

def _strip_comments(src: str) -> str:
    import re
    pattern = re.compile(
        r'//.*?$|/\*.*?\*/|\'(?:\\.|[^\\\'])*\'|"(?:\\.|[^\\"])*"',
        re.DOTALL | re.MULTILINE,
    )
    return re.sub(pattern, lambda m: " " if m.group(0).startswith("/") else m.group(0), src)


def _strip_includes(src: str) -> str:
    """Remove #include lines so pycparser doesn't need system headers."""
    lines = [l for l in src.splitlines() if not l.strip().startswith("#include")]
    return "\n".join(lines)


def _preprocess(src: str) -> str:
    """Strip #includes, then run cpp for any remaining directives
    (#define, #if, ...) so macro-using files parse. Includes are stripped
    first so system headers never enter; without cpp on PATH the source
    passes through unchanged (directive-free files are unaffected)."""
    src = _strip_includes(src)
    if any(line.lstrip().startswith("#") for line in src.splitlines()):
        import subprocess
        try:
            out = subprocess.run(["cpp", "-E", "-P", "-"], input=src,
                                 capture_output=True, text=True, timeout=10)
            if out.returncode == 0:
                src = out.stdout
        except (OSError, subprocess.TimeoutExpired):
            pass
    return _strip_comments(src)


def _is_const_true(node: c_ast.Node) -> bool:
    return isinstance(node, c_ast.Constant) and node.value == "1"


def _find_loops(body: c_ast.Node) -> list[c_ast.Node]:
    """All While/For nodes under `body`, in source (pre-)order."""
    loops: list[c_ast.Node] = []

    class _V(c_ast.NodeVisitor):
        def visit_While(self, n):
            loops.append(n)
            self.generic_visit(n)

        def visit_For(self, n):
            loops.append(n)
            self.generic_visit(n)

    _V().visit(body)
    return loops


def _loop_cond_body(node: c_ast.While | c_ast.For
                    ) -> tuple[c_ast.Node, c_ast.Compound]:
    """(condition expr, body-as-Compound) of a While or For loop;
    a For's `next` is appended to the body, mirroring _exec_for."""
    if isinstance(node, c_ast.While):
        body = (node.stmt if isinstance(node.stmt, c_ast.Compound)
                else c_ast.Compound(block_items=[node.stmt]))
        return node.cond, body
    cond = node.cond or c_ast.Constant("int", "1")
    items = (list(node.stmt.block_items or [])
             if isinstance(node.stmt, c_ast.Compound) else [node.stmt])
    if node.next:
        items = items + [node.next]
    return cond, c_ast.Compound(block_items=items)


def _subst_env(inv: z3.ExprRef, env: dict[str, z3.ExprRef]) -> z3.ExprRef:
    """inv with each program-variable name replaced by its env expression."""
    pairs = [(z3.Const(name, val.sort()), val) for name, val in env.items()]
    return z3.substitute(inv, pairs)


# ─────────────────────────────────────────────── standalone CLI ─────

def main() -> None:
    """Standalone use: print symstates and vassert verdicts for a C file.

        python -m data.symex_c prog.c [--depth N]

    Exits nonzero if any vassert is violated (counterexamples printed).
    """
    import argparse
    import sys

    ap = argparse.ArgumentParser(description=main.__doc__.splitlines()[0])
    ap.add_argument("file", type=Path)
    ap.add_argument("--depth", type=int, default=4,
                    help="loop unroll depth (default 4)")
    ap.add_argument("--gen-tests", action="store_true",
                    help="print one concrete mainQ input per explored path")
    ap.add_argument("--gen-harness", metavar="FILE",
                    help="write a C replay driver calling mainQ per path")
    ap.add_argument("--no-safety", action="store_true",
                    help="disable auto division-by-zero/array-bounds checks")
    ap.add_argument("--check-overflow", action="store_true",
                    help="check signed 32-bit overflow (constrains inputs "
                         "to the int range)")
    ap.add_argument("--merge", action="store_true",
                    help="merge simple if/else joins (fewer paths, ite terms)")
    ap.add_argument("--prove", action="append", metavar="EXPR", default=[],
                    help='prove EXPR (e.g. "q*y + r == x") holds at the '
                         "loop head on every iteration (unbounded induction)")
    ap.add_argument("--check-inv", action="append", nargs=2, default=[],
                    metavar=("LOC", "EXPR"),
                    help="check EXPR at every record of vtrace LOC (bounded)")
    ap.add_argument("--houdini", action="append", metavar="EXPR", default=[],
                    help="candidate invariant; the set is pruned to its "
                         "largest mutually inductive subset")
    ap.add_argument("--loop", type=int, default=0,
                    help="loop index for --prove/--houdini/--terminates")
    ap.add_argument("--k", type=int, default=1,
                    help="induction depth for --prove (default 1)")
    ap.add_argument("--terminates", metavar="RANK",
                    help="prove the loop terminates via this integer "
                         'ranking expression (e.g. "r")')
    ap.add_argument("--assume", action="append", metavar="EXPR", default=[],
                    help="supporting invariant for --terminates; verified "
                         "inductive first (dropped with a warning if not)")
    args = ap.parse_args()

    engine = CSymEx(args.file, args.depth,
                    check_safety=not args.no_safety,
                    check_overflow=args.check_overflow,
                    merge_states=args.merge)
    results = engine.run()

    for loc, pc, slocal in results:
        print(f"{loc}:\n  pc:     {pc}\n  slocal: {slocal}")

    for loc in engine.unreached_locs():
        print(f"warning: {loc} is unreached "
              f"(dead code, or --depth {args.depth} too small)")

    if args.gen_tests:
        for loc, vals in engine.gen_inputs():
            argstr = ", ".join(f"{k}={v}" for k, v in vals.items())
            print(f"input reaching {loc}: mainQ({argstr})")

    if args.gen_harness:
        Path(args.gen_harness).write_text(engine.gen_test_harness())
        print(f"replay harness written to {args.gen_harness}")

    violated = False
    for a in engine.safety_results + engine.assert_results:
        label = "vassert" if a.kind == "vassert" else a.kind
        line = f"{label} at {a.coord}: {a.status}  [{a.cond}]"
        if a.status == "violated":
            violated = True
            line += f"  counterexample: {a.cex}"
        print(line)
        if a.status == "violated" and a.trace:
            print("  witness trace:")
            for ev in a.trace:
                print(f"    {ev}")

    for text in args.prove:
        status, cex = engine.prove_inductive(engine.parse_c_expr(text),
                                             loop=args.loop, k=args.k)
        line = f"prove {text}: {status}"
        if cex:
            line += f"  counterexample: {cex}"
        print(line)
        violated |= status != "valid"

    if args.terminates:
        assumes = [(t, engine.parse_c_expr(t)) for t in args.assume]
        if assumes:
            kept = {id(e) for e in engine.houdini([e for _, e in assumes],
                                                  loop=args.loop)}
            for t, e in assumes:
                if id(e) not in kept:
                    print(f"warning: --assume {t} is not inductive; dropped")
            assumes = [(t, e) for t, e in assumes if id(e) in kept]
        rank = engine.parse_c_expr(args.terminates, as_bool=False)
        status, cex = engine.prove_termination(
            rank, loop=args.loop, assume=[e for _, e in assumes])
        line = f"terminates (rank {args.terminates}): {status}"
        if cex:
            line += f"  counterexample: {cex}"
        print(line)
        violated |= status != "terminates"

    for loc, text in args.check_inv:
        status, cex = engine.check_inv(loc, engine.parse_c_expr(text))
        line = f"check {text} at {loc}: {status}"
        if cex:
            line += f"  counterexample: {cex}"
        print(line)
        violated |= status != "valid"

    if args.houdini:
        cands = [(t, engine.parse_c_expr(t)) for t in args.houdini]
        kept = {id(e) for e in engine.houdini([e for _, e in cands],
                                              loop=args.loop)}
        for t, e in cands:
            print(f"houdini {t}: "
                  f"{'kept (inductive)' if id(e) in kept else 'dropped'}")

    sys.exit(1 if violated else 0)


if __name__ == "__main__":
    main()
