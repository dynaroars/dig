"""
Neuro-symbolic invariant inference (prototype).

An LLM *proposes* candidate invariants (the forms DIG's algebraic engine can't
do well: disjunctive, conditional, nonlinear inequalities, closed forms); DIG's
existing symbolic-state + z3 machinery *verifies* them soundly and returns
counterexamples that drive a CEGIR refinement loop. Every reported invariant is
z3-checked against the program's symbolic states, so soundness does not depend
on the LLM.

  llm: source + traces + counterexamples  -> propose ->  candidate invariants
                                               |
                          DIG symstates + z3  -> verify ->  proved / cex
                                               |
                              cex -> new traces -> re-propose (CEGIR)

The LLM backend is pluggable (Anthropic by default); the verifier is the load-
bearing, sound half and runs with no LLM at all (see verify()).
"""
from __future__ import annotations

import random
import tempfile
import time
from pathlib import Path

import sympy
import z3

import settings
import data.prog
import data.traces
import infer.inv
import infer.eqt
import infer.oct
import alg
import helpers.vcommon as CM
from helpers.z3utils import Z3

mlog = CM.getLogger(__name__, settings.LOGGER_LEVEL)


# ─────────────────────────────── a generic, checkable invariant ──────

class LLMInv(infer.inv.Inv):
    """
    Wraps an arbitrary z3 boolean predicate so DIG's checker can verify it.
    Unlike Eqt/Oct/... it carries the z3 expr directly, so it supports any
    form the LLM proposes (disjunctions, nonlinear inequalities, ...).
    """

    def __init__(self, zexpr: z3.BoolRef, label: str) -> None:
        self._zexpr = zexpr
        self.inv = label          # used by __hash__/__eq__/__repr__
        self.reset_stat()

    @property
    def mystr(self) -> str:
        return str(self.inv)

    @property
    def cinvs_category(self) -> str:
        return "llm"

    @property
    def expr(self) -> z3.BoolRef:
        return self._zexpr

    def test_single_trace(self, trace: data.traces.Trace) -> bool:
        sub = [(z3.Int(str(k)), z3.IntVal(int(v)))
               for k, v in trace.mydict.items()]
        return z3.is_true(z3.simplify(z3.substitute(self._zexpr, *sub)))


# ─────────────────── render proved preds in DIG's native form ─────────

def _z3_to_sympy(t: z3.ExprRef):
    """Convert a z3 *arithmetic term* (Int sort) to a sympy expression."""
    k = t.decl().kind()
    if k == z3.Z3_OP_ANUM:                       # integer literal
        return sympy.Integer(t.as_long())
    if k == z3.Z3_OP_UNINTERPRETED and t.num_args() == 0:   # variable
        return sympy.Symbol(t.decl().name())
    args = [_z3_to_sympy(t.arg(i)) for i in range(t.num_args())]
    if k == z3.Z3_OP_ADD:
        return sum(args, sympy.Integer(0))
    if k == z3.Z3_OP_SUB:
        return args[0] - sum(args[1:], sympy.Integer(0)) if len(args) > 1 \
            else -args[0]
    if k == z3.Z3_OP_MUL:
        return sympy.prod(args)
    if k == z3.Z3_OP_UMINUS:
        return -args[0]
    if k == z3.Z3_OP_POWER:
        return args[0] ** args[1]
    raise ValueError(f"unsupported z3 op in term: {t}")


def _split_const(expr):
    """expr  ->  (variable_part, constant)  so that expr == var_part + const."""
    expr = sympy.expand(expr)
    const = expr.as_coefficients_dict().get(sympy.Integer(1), 0)
    return expr - const, const


def _max_deg(expr) -> int:
    expr = sympy.expand(expr)
    syms = list(expr.free_symbols)
    if not syms:
        return 0
    try:
        return sympy.Poly(expr, *syms).total_degree()
    except sympy.PolynomialError:
        return 1


def to_native(inv: LLMInv) -> infer.inv.Inv:
    """
    Re-express a proved LLMInv as DIG's native invariant so it prints/classifies
    like a standard run: equalities -> Eqt (`lhs - rhs == 0`), linear
    inequalities -> Oct (`term <= const`, sign-normalized as DIG does). Forms
    DIG's algebraic engine can't produce (nonlinear inequalities, congruences,
    disjunctions) stay as the original LLMInv, grouped under `LLM:`.
    """
    e = inv.expr
    k = e.decl().kind()
    try:
        if k == z3.Z3_OP_EQ:
            lhs = _z3_to_sympy(e.arg(0)) - _z3_to_sympy(e.arg(1))
            return infer.eqt.Eqt(sympy.Eq(sympy.expand(lhs), 0),
                                 stat=infer.inv.Inv.PROVED)
        if k in (z3.Z3_OP_LE, z3.Z3_OP_GE, z3.Z3_OP_LT, z3.Z3_OP_GT):
            a, b = _z3_to_sympy(e.arg(0)), _z3_to_sympy(e.arg(1))
            # bring to `expr <= 0`, matching DIG's orientation
            if k == z3.Z3_OP_LE:    expr = a - b
            elif k == z3.Z3_OP_GE:  expr = b - a
            elif k == z3.Z3_OP_LT:  expr = a - b + 1
            else:                   expr = b - a + 1
            if _max_deg(expr) <= 1:                     # linear octagon
                var_part, const = _split_const(expr)
                return infer.oct.Oct(sympy.Le(var_part, -const),
                                     stat=infer.inv.Inv.PROVED)
    except (ValueError, TypeError):
        pass
    return inv                                          # keep as LLM


# ─────────────────────────────── symbolic states for a program ───────

def get_dig(cfile: Path, seed: int = 42) -> alg.DigSymStatesC:
    """Set up DIG far enough to have symbolic states for `cfile`."""
    dig = alg.DigSymStatesC(cfile)
    dig.seed = seed
    random.seed(seed)
    dig.tmpdir = Path(tempfile.mkdtemp(dir=settings.TMPDIR, prefix="llm_"))
    dig.tmpdir_del = dig.tmpdir / "delete_me"
    dig.tmpdir_del.mkdir()
    dig.mysrc = dig.mysrc_cls(cfile, dig.tmpdir_del)
    dig.inp_decls = dig.mysrc.inp_decls
    dig.inv_decls = dig.mysrc.inv_decls
    dig.prog = data.prog.Prog(dig.exe_cmd, dig.inp_decls, dig.inv_decls)
    dig.symstates = dig.get_symbolic_states()
    dig.locs = dig.prog.locs
    return dig


# ─────────────────────────────── the sound verifier (LLM-free) ───────

def verify(dig: alg.DigSymStatesC,
           candidates: dict[str, list[tuple[z3.BoolRef, str]]]
           ) -> tuple[dict[str, list[LLMInv]], dict]:
    """
    candidates: {loc -> [(z3_pred, label), ...]}
    Returns (proved, cexs) where proved is {loc -> [proved LLMInv, ...]} and
    cexs is DIG's counterexample dict {loc -> {inv_label -> [cex_dicts]}}.
    Pure DIG symstates + z3; no LLM.
    """
    dinvs = infer.inv.DInvs()
    for loc, preds in candidates.items():
        for zexpr, label in preds:
            dinvs.setdefault(loc, infer.inv.Invs()).add(LLMInv(zexpr, label))

    cexs, checked = dig.symstates.check(dinvs, inps=None)
    proved = {loc: [inv for inv in checked[loc] if inv.is_proved]
              for loc in checked}
    return proved, cexs


def verify_houdini(cfile: Path,
                   candidates: dict[str, list[tuple[z3.BoolRef, str]]],
                   depth: int = 5) -> dict[str, list[LLMInv]]:
    """
    Extra sound verification stage for LLM candidates: run houdini
    (k-induction) over the *union* of candidates at each loop head and keep the
    largest jointly-inductive subset. This is stronger than verify()'s
    per-candidate bounded symbolic-state check in two ways: the proof is
    unbounded (k-induction, not bounded-depth reachable states), and it proves
    *mutually* inductive sets -- candidates that fail on their own but hold
    given the others (the classic reason 1-induction rejects interdependent
    invariants). Survivors are returned as PROVED LLMInv objects per loc.

    candidates: {loc -> [(z3_pred, label), ...]} (as produced by _parse). Only
    the candidates at a loop-head vtrace location are used; non-loop locations
    are left to verify().
    """
    from data.symex_c import CSymEx, _find_loops
    from infer.recurrence import _loop_head_vtrace

    engine = CSymEx(Path(cfile), depth)
    engine._parse()
    loops = _find_loops(engine.func_bodies["mainQ"])

    proved: dict[str, list[LLMInv]] = {}
    for i, node in enumerate(loops):
        loc = _loop_head_vtrace(node)
        if loc is None or loc not in candidates:
            continue

        exprs, id2label, seen = [], {}, set()
        for zexpr, label in candidates[loc]:
            try:
                key = str(z3.simplify(zexpr))
            except z3.Z3Exception:
                continue
            if key in seen:
                continue
            seen.add(key)
            exprs.append(zexpr)
            id2label[id(zexpr)] = label
        if not exprs:
            continue

        try:
            kept = engine.houdini(exprs, loop=i)
        except Exception as ex:
            mlog.debug(f"llm houdini declined loop {i} ({loc}): {ex}")
            continue

        for e in kept:
            inv = LLMInv(e, id2label.get(id(e), str(e)))
            inv.set_stat(infer.inv.Inv.PROVED)
            proved.setdefault(loc, []).append(inv)
    return proved


def _format_cexs(cexs: dict) -> str:
    """
    Render DIG's counterexample dict as one 'candidate  # false when <state>'
    line per disproved candidate, so the next LLM round sees *why* each guess
    failed (the concrete state that breaks it) rather than an opaque dict dump.
    """
    lines = []
    for loc, per_inv in cexs.items():
        for label, states in per_inv.items():
            st = states[0] if states else {}
            state_str = ", ".join(f"{k}={v}" for k, v in st.items())
            lines.append(f"{label}   # false when {state_str}"
                         if state_str else f"{label}   # false")
    return "\n".join(lines)


# ─────────────────────────────── LLM backend (pluggable) ─────────────

def propose(c_source: str, trace_sample: str = "", cexs: str = "") -> str:
    """
    Ask the LLM for candidate invariants. Returns raw text; caller parses it.
    Requires ANTHROPIC_API_KEY + the anthropic SDK. The verifier above runs
    without this. `trace_sample` is optional: when empty, the model proposes
    from the source alone (no .exe run needed).
    """
    import anthropic  # lazy: only needed for the LLM half

    prompt = f"""You are given a C function{' and sample execution traces recorded at its loop head(s)' if trace_sample else ''}.
Propose loop invariants: numerical relations over ONLY the traced variables
(the arguments of the vtrace* calls) that hold on every iteration. Prefer forms
a polynomial-equation solver would miss: disjunctions, conditionals, nonlinear
inequalities, closed forms.

Output rules (important):
- one invariant per line, nothing else (no prose, no markdown, no numbering)
- each line is a single Python boolean expression over the traced variable names
- use: + - * / % **, ==, !=, <=, <, >=, >, and, or, not, parentheses
- example lines:   a*y == b        and(r >= 0, q*y + r == x)        a == 0 or b == a*y

C source:
{c_source}
"""
    if trace_sample:
        prompt += f"\nSample traces (one per line):\n{trace_sample}\n"
    if cexs:
        prompt += f"\nThese candidates were FALSE (counterexamples); avoid them:\n{cexs}\n"

    client = anthropic.Anthropic()
    msg = client.messages.create(
        model="claude-opus-4-8",
        max_tokens=1024,
        messages=[{"role": "user", "content": prompt}],
    )
    return msg.content[0].text


def run(cfile: Path, seed: float, max_rounds: int = 3,
        no_traces: bool = False) -> tuple[infer.inv.DInvs, dict]:
    """
    Full CEGIR loop: propose -> verify -> feed counterexamples back. Needs an
    LLM backend (propose(), which reads ANTHROPIC_API_KEY); the verifier half is
    reusable on its own. Returns (dinvs, time_d) where dinvs holds the proved
    invariants in DIG's native form. With no_traces=True the prompt uses the
    source only (the .exe is never run).
    """
    random.seed(seed)
    time_d = {}
    st = time.time()
    dig = get_dig(cfile)
    time_d["symbolic_states"] = time.time() - st

    c_source = Path(cfile).read_text()
    proved_by_loc: dict[str, dict[str, infer.inv.Inv]] = {}
    cex_text = ""
    t_llm = t_verify = 0.0
    for rnd in range(max_rounds):
        trace_sample = "" if no_traces else _trace_sample(dig)
        t = time.time()
        text = propose(c_source, trace_sample, cex_text)
        t_llm += time.time() - t

        candidates = _parse(text, dig)
        if not candidates:
            mlog.info(f"round {rnd}: LLM proposed 0 parseable candidates")
            break
        # _parse replicates the same predicate list at every loc, so count one
        n_cands = len(next(iter(candidates.values())))
        mlog.info(f"round {rnd}: LLM proposed {n_cands} candidates")
        t = time.time()
        proved, cexs = verify(dig, candidates)
        # extra sound pass: k-induction over the union of candidates per loop,
        # catching mutually-inductive sets the per-candidate check misses. Its
        # bounded entry states can over-approve on nested loops, so intersect
        # with verify(): never resurrect a candidate the symbolic-state check
        # already disproved (a genuine, reachable counterexample).
        if settings.DO_LLM_HOUDINI:
            disproved = {loc: set(labels) for loc, labels in cexs.items()}
            for loc, invs in verify_houdini(cfile, candidates).items():
                proved.setdefault(loc, [])
                have = {inv.mystr for inv in proved[loc]}
                bad = disproved.get(loc, set())
                proved[loc].extend(
                    inv for inv in invs
                    if inv.mystr not in have and inv.mystr not in bad)
        t_verify += time.time() - t
        for loc, invs in proved.items():
            for inv in invs:
                proved_by_loc.setdefault(loc, {})[inv.mystr] = to_native(inv)
        n_new = sum(len(v) for v in proved.values())
        n_cex = sum(len(labels) for labels in cexs.values())
        mlog.info(f"round {rnd}: {n_new} proved, {n_cex} disproved")
        if not cexs:
            break
        cex_text = _format_cexs(cexs)

    time_d["llm_propose"] = t_llm
    time_d["verify"] = t_verify

    dinvs = infer.inv.DInvs()
    for loc, d in proved_by_loc.items():
        for inv in d.values():
            dinvs.add(loc, inv)

    # remove redundant/weaker invariants, exactly as a standard run does
    if dinvs.siz:
        t = time.time()
        dinvs = dinvs.simplify()
        time_d["simplify"] = time.time() - t

    time_d["total"] = time.time() - st
    return dinvs, time_d


def report(progname: str, dinvs: infer.inv.DInvs, time_d: dict,
           seed: float) -> None:
    """Print results in the same shape as a standard (non-LLM) dig.py run."""
    nlocs = len(dinvs)
    total = dinvs.siz
    typ_ctr = dinvs.typ_ctr
    typss = ", ".join(f"{k}: {typ_ctr[k]}" for k in sorted(typ_ctr))

    # V: #distinct vars, T: max #terms, D: max deg, NL: #nonlinear invs
    vss, degs, terms = set(), [0], [0]
    for inv in dinvs.invs:
        p = getattr(inv, "inv", None)
        if isinstance(p, (sympy.Equality, sympy.Le)):
            vss |= {str(s) for s in p.lhs.free_symbols}
            degs.append(_max_deg(p.lhs))
            terms.append(len(sympy.Add.make_args(sympy.expand(p.lhs))))
    V, T, D = len(vss), max(terms), max(degs)
    NL = sum(1 for d in degs if d >= 2)

    print(f"* prog {progname} locs {nlocs}; invs {total} ({typss}) "
          f"V {V} T {T} D {D}; NL {NL} ({D}) ;")
    time_s = ", ".join(f"{t} {time_d[t]:.1f}s" for t in time_d)
    print(f"-> time {time_s}")
    print(f"rand seed {seed}, test {random.randint(0, 100)}")
    print(dinvs)


# ─────────────────────────────── helpers (parse / sample) ────────────

def _trace_sample(dig, n: int = 12) -> str:
    """Run a few random inputs and format concrete trace rows per location."""
    rinps = dig.prog.gen_rand_inps(n_needed=8)
    inps = data.traces.Inps().merge(rinps, dig.inp_decls.names)
    dtraces = dig.prog.get_traces(inps)
    lines = []
    for loc in dtraces:
        for t in list(dtraces[loc])[:n]:
            row = ", ".join(f"{k}={v}" for k, v in t.mydict.items())
            lines.append(f"{loc}: {row}")
    return "\n".join(lines)


def _parse(text: str, dig) -> dict[str, list[tuple[z3.BoolRef, str]]]:
    """Parse one-invariant-per-line LLM output into z3 predicates per loc."""
    out: dict[str, list] = {}
    locs = list(dig.inv_decls)
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            zexpr = Z3.parse(line)
        except Exception:
            continue
        if not z3.is_bool(zexpr):
            continue
        for loc in locs:  # prototype: try the candidate at every loc
            out.setdefault(loc, []).append((zexpr, line))
    return out
