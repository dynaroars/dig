#!/usr/bin/env python3
"""
Benchmark harness for src/data/symex_c.py (CSymEx) — symex only, no DIG.

Runs CSymEx over the C benchmark programs at one or more unroll depths and
reports, per (program, depth):

  - wall time (best of --repeat runs)
  - number of (loc, pc, slocal) records produced
  - a signature hash over the ordered record strings, used both to detect
    nondeterminism across repeats and to diff against a saved baseline

Each run happens in a fresh subprocess so z3 state can't leak between
programs and a hung program only costs its own --timeout.

Usage:
  python tests/bench_symex.py                          # nla suite, depths 2,3,4
  python tests/bench_symex.py --suites nla hola
  python tests/bench_symex.py --programs cohendiv sqrt1 --depths 2 3 4 5
  python tests/bench_symex.py --repeat 3               # timing + determinism
  python tests/bench_symex.py --save                   # write tests/symex_baseline.json
  python tests/bench_symex.py --check                  # compare against baseline

Exit status: nonzero if any run crashed, any repeat disagreed (nondeterminism),
or --check found a regression (signature/record-count change, or slowdown
beyond --time-factor).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SRC = REPO / "src"
BENCH = REPO / "benchmark" / "c"
BASELINE_PATH = Path(__file__).parent / "symex_baseline.json"

SUITES = ["nla", "complexity", "hola"]


# ───────────────────────────────────────────────────────── worker ──

def worker(path: str, depth: int) -> None:
    """Run one (program, depth) and print a JSON result on stdout."""
    sys.path.insert(0, str(SRC))
    from data.symex_c import CSymEx

    t0 = time.perf_counter()
    engine = CSymEx(Path(path), depth)
    results = engine.run()
    wall = time.perf_counter() - t0

    sig = hashlib.sha256(
        "\n".join(f"{loc}|{pc}|{slocal}" for loc, pc, slocal in results)
        .encode()).hexdigest()

    print(json.dumps({"wall": wall, "n_records": len(results), "sig": sig}))


# ───────────────────────────────────────────────────────── driver ──

def collect_programs(suites: list[str], names: list[str] | None) -> list[Path]:
    progs: list[Path] = []
    for suite in suites:
        progs.extend(sorted((BENCH / suite).glob("*.c")))
    if names:
        wanted = set(names)
        progs = [p for p in progs if p.stem in wanted]
        missing = wanted - {p.stem for p in progs}
        if missing:
            sys.exit(f"error: program(s) not found in {suites}: {sorted(missing)}")
    return progs


def prog_id(path: Path) -> str:
    return f"{path.parent.name}/{path.stem}"


def run_one(path: Path, depth: int, timeout: float) -> dict:
    """Returns {wall, n_records, sig} or {error: ...}."""
    cmd = [sys.executable, __file__, "--worker", str(path), str(depth)]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True,
                             timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"error": f"timeout({timeout:g}s)"}
    if out.returncode != 0:
        last = (out.stderr or "").strip().splitlines()
        return {"error": last[-1][:100] if last else f"exit {out.returncode}"}
    return json.loads(out.stdout.strip().splitlines()[-1])


def bench(progs: list[Path], depths: list[int], repeat: int,
          timeout: float) -> dict[str, dict]:
    """
    Returns {key: {wall, n_records, sig}} or {key: {error}} where
    key = 'suite/prog@depth'. wall is the best (min) of `repeat` runs;
    a 'nondet' field is set if repeats disagree on the signature.
    """
    results: dict[str, dict] = {}
    for path in progs:
        for depth in depths:
            key = f"{prog_id(path)}@{depth}"
            runs = []
            for _ in range(repeat):
                r = run_one(path, depth, timeout)
                runs.append(r)
                if "error" in r:
                    break
            first = runs[0]
            if any("error" in r for r in runs):
                err = next(r for r in runs if "error" in r)
                results[key] = {"error": err["error"]}
                print(f"  {key:<40} ERROR: {err['error']}")
                continue
            entry = {
                "wall": round(min(r["wall"] for r in runs), 4),
                "n_records": first["n_records"],
                "sig": first["sig"],
            }
            if len({r["sig"] for r in runs}) > 1:
                entry["nondet"] = True
            results[key] = entry
            flag = "  NONDETERMINISTIC" if entry.get("nondet") else ""
            print(f"  {key:<40} {entry['wall']:>8.3f}s  "
                  f"{entry['n_records']:>5} records  "
                  f"{entry['sig'][:12]}{flag}")
    return results


# ─────────────────────────────────────────────── baseline compare ──

def check_against_baseline(results: dict[str, dict], baseline: dict[str, dict],
                           time_factor: float, time_slack: float) -> list[str]:
    problems = []
    for key, base in sorted(baseline.items()):
        cur = results.get(key)
        if cur is None:
            continue  # not part of this run's selection
        if "error" in base:
            if "error" not in cur:
                print(f"  {key}: previously {base['error']}, now succeeds "
                      f"({cur['n_records']} records) — rerun --save to record")
            continue
        if "error" in cur:
            problems.append(f"{key}: was ok, now {cur['error']}")
            continue
        if cur["sig"] != base["sig"]:
            detail = (f" (records {base['n_records']} -> {cur['n_records']})"
                      if cur["n_records"] != base["n_records"] else "")
            problems.append(f"{key}: symstates changed{detail}")
        limit = base["wall"] * time_factor + time_slack
        if cur["wall"] > limit:
            problems.append(
                f"{key}: slower — {cur['wall']:.3f}s vs baseline "
                f"{base['wall']:.3f}s (limit {limit:.3f}s)")
    return problems


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    ap.add_argument("--worker", nargs=2, metavar=("FILE", "DEPTH"),
                    help=argparse.SUPPRESS)
    ap.add_argument("--suites", nargs="+", default=["nla"], choices=SUITES)
    ap.add_argument("--programs", nargs="+",
                    help="restrict to these program stems (e.g. cohendiv sqrt1)")
    ap.add_argument("--depths", nargs="+", type=int, default=[2, 3, 4])
    ap.add_argument("--repeat", type=int, default=1,
                    help="runs per (program, depth); best time kept, "
                         "signatures compared for determinism")
    ap.add_argument("--timeout", type=float, default=60,
                    help="per-run timeout in seconds (default 60)")
    ap.add_argument("--save", action="store_true",
                    help=f"write results to {BASELINE_PATH.name}")
    ap.add_argument("--check", action="store_true",
                    help=f"compare against {BASELINE_PATH.name}")
    ap.add_argument("--time-factor", type=float, default=1.5,
                    help="--check fails if wall > baseline * factor + slack")
    ap.add_argument("--time-slack", type=float, default=0.25,
                    help="absolute slack seconds added to the time limit")
    args = ap.parse_args()

    if args.worker:
        worker(args.worker[0], int(args.worker[1]))
        return

    progs = collect_programs(args.suites, args.programs)
    if not progs:
        sys.exit("error: no programs selected")

    print(f"benchmarking CSymEx: {len(progs)} program(s), "
          f"depths {args.depths}, repeat={args.repeat}")
    t0 = time.perf_counter()
    results = bench(progs, args.depths, args.repeat, args.timeout)
    print(f"total: {time.perf_counter() - t0:.1f}s")

    failed = [k for k, v in results.items() if "error" in v
              and not v["error"].startswith("timeout")]
    nondet = [k for k, v in results.items() if v.get("nondet")]
    if nondet:
        print(f"\nNONDETERMINISTIC results: {nondet}")

    ok = not failed and not nondet

    if args.save:
        BASELINE_PATH.write_text(json.dumps(results, indent=1, sort_keys=True)
                                 + "\n")
        print(f"baseline saved to {BASELINE_PATH}")

    if args.check:
        if not BASELINE_PATH.exists():
            sys.exit(f"error: no baseline at {BASELINE_PATH}; run --save first")
        baseline = json.loads(BASELINE_PATH.read_text())
        problems = check_against_baseline(results, baseline,
                                          args.time_factor, args.time_slack)
        if problems:
            print("\nbaseline check FAILED:")
            for p in problems:
                print(f"  {p}")
            ok = False
        else:
            print("\nbaseline check passed")

    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
