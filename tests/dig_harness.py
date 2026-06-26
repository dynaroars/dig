"""
Helpers for the benchmark regression tests: run DIG on a C file and parse its
output into a stable, nondeterminism-tolerant signature.

The signature is:
  - status: "ok" | "timeout" | "fail"
  - n_invs: total invariant count
  - eqts:   the equality invariants, sign-normalized (so `p==0` and `-p==0`
            compare equal) and de-duplicated

Equalities are the most deterministic + most meaningful invariants, so they
drive correctness checks. Counts of the wobblier types (congruences, octs) are
only guarded loosely via a min-count floor.
"""
from __future__ import annotations

import os
import re
import signal
import subprocess
import sys
from pathlib import Path

import sympy

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "src"
BENCH = REPO / "benchmark"
BENCH_DIRS = ["c/nla", "c/complexity", "c/hola"]


def programs() -> list[Path]:
    progs: list[Path] = []
    for d in BENCH_DIRS:
        progs.extend(sorted((BENCH / d).glob("*.c")))
    return progs


def prog_id(path: Path) -> str:
    """e.g. 'nla/cohendiv' — stable id used as the golden key and test id."""
    return f"{path.parent.name}/{path.stem}"


def canon_eqt(s: str) -> str:
    """
    Canonicalize an 'lhs == rhs' equality string so sign flips and term
    reorderings compare equal. Falls back to the raw string if unparseable.
    """
    try:
        lhs, rhs = s.split("==")
        # force every identifier to a plain Symbol so names that collide with
        # sympy builtins (N, S, E, I, Q, ...) don't get reinterpreted
        loc = {n: sympy.Symbol(n) for n in set(re.findall(r"[A-Za-z_]\w*", s))}
        e = sympy.expand(sympy.sympify(lhs, locals=loc)
                         - sympy.sympify(rhs, locals=loc))
        terms = e.as_ordered_terms()
        if terms and terms[0].as_coeff_Mul()[0] < 0:
            e = -e
        return str(e)
    except Exception:
        return s.strip()


def run_dig(cfile: Path, seed: int = 42, timeout: int = 180) -> dict:
    cmd = [sys.executable, "-O", "dig.py", str(cfile.resolve()), "-seed", str(seed)]
    # start_new_session so DIG's forked multiprocessing workers share a process
    # group we can kill wholesale on timeout — otherwise a timed-out run orphans
    # ~ncpu busy-looping workers that poison every subsequent run.
    p = subprocess.Popen(cmd, cwd=SRC, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True,
                         start_new_session=True)
    try:
        out, _ = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
        p.communicate()
        return {"status": "timeout", "n_invs": 0, "eqts": []}
    m = re.search(r"^\* prog \S+ .*?invs (\d+) ", out, re.M)
    if not m:
        return {"status": "fail", "n_invs": 0, "eqts": []}

    eqts = set()
    for line in out.splitlines():
        line = line.strip()
        if line.startswith("Eqt:"):
            for e in line[len("Eqt:"):].split(";"):
                if e.strip():
                    eqts.add(canon_eqt(e))
    return {"status": "ok", "n_invs": int(m.group(1)), "eqts": sorted(eqts)}
