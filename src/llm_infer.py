"""
Neuro-symbolic invariant inference (prototype).

An LLM *proposes* candidate invariants (the forms DIG's algebraic engine can't
do well: disjunctive, conditional, nonlinear inequalities, closed forms); DIG's
existing symbolic-state + z3 machinery *verifies* them soundly and returns
counterexamples that drive a CEGIR refinement loop. Every reported invariant is
z3-checked against the program's symbolic states, so soundness does not depend
on the LLM.

  llm: source + traces + counterexamples  ──propose──▶  candidate invariants
                                               │
                          DIG symstates + z3  ─┴─verify─▶  proved / cex
                                               │
                              cex ──▶ new traces ──▶ re-propose (CEGIR)

The LLM backend is pluggable (Anthropic by default); the verifier is the load-
bearing, sound half and runs with no LLM at all (see verify()).
"""
from __future__ import annotations

import os
import random
import tempfile
from pathlib import Path

import z3

import settings
import data.prog
import data.traces
import infer.inv
import alg
from helpers.z3utils import Z3


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
           ) -> tuple[list[LLMInv], dict]:
    """
    candidates: {loc -> [(z3_pred, label), ...]}
    Returns (proved invariants, cexs) where cexs is DIG's counterexample dict
    {loc -> {inv_label -> [cex_dicts]}}. Pure DIG symstates + z3; no LLM.
    """
    dinvs = infer.inv.DInvs()
    for loc, preds in candidates.items():
        for zexpr, label in preds:
            dinvs.setdefault(loc, infer.inv.Invs()).add(LLMInv(zexpr, label))

    cexs, checked = dig.symstates.check(dinvs, inps=None)
    proved = [inv for loc in checked for inv in checked[loc] if inv.is_proved]
    return proved, cexs


# ─────────────────────────────── LLM backend (pluggable) ─────────────

def propose(c_source: str, trace_sample: str, cexs: str = "") -> str:
    """
    Ask the LLM for candidate invariants. Returns raw text; caller parses it.
    Requires ANTHROPIC_API_KEY + the anthropic SDK. The verifier above runs
    without this.
    """
    import anthropic  # lazy: only needed for the LLM half

    prompt = f"""You are given a C function and sample execution traces recorded
at its loop head(s). Propose loop invariants: numerical relations over ONLY the
traced variables that hold on every iteration. Prefer forms a polynomial-equation
solver would miss: disjunctions, conditionals, nonlinear inequalities, closed
forms.

Output rules (important):
- one invariant per line, nothing else (no prose, no markdown, no numbering)
- each line is a single Python boolean expression over the traced variable names
- use: + - * / % **, ==, !=, <=, <, >=, >, and, or, not, parentheses
- example lines:   a*y == b        and(r >= 0, q*y + r == x)        a == 0 or b == a*y

C source:
{c_source}

Sample traces (one per line):
{trace_sample}
"""
    if cexs:
        prompt += f"\nThese candidates were FALSE (counterexamples); avoid them:\n{cexs}\n"

    client = anthropic.Anthropic()
    msg = client.messages.create(
        model="claude-opus-4-8",
        max_tokens=1024,
        messages=[{"role": "user", "content": prompt}],
    )
    return msg.content[0].text


def run(cfile: Path, max_rounds: int = 3) -> list[LLMInv]:
    """
    Full CEGIR loop: propose -> verify -> feed counterexamples back. Needs an
    LLM backend (propose()); the verifier half is reusable on its own.
    """
    dig = get_dig(cfile)
    c_source = Path(cfile).read_text()
    proved_all: list[LLMInv] = []
    cex_text = ""
    for _ in range(max_rounds):
        text = propose(c_source, _trace_sample(dig), cex_text)
        candidates = _parse(text, dig)
        if not candidates:
            break
        proved, cexs = verify(dig, candidates)
        proved_all.extend(proved)
        if not cexs:
            break
        cex_text = str(cexs)
    return proved_all


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
