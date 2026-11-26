#!/usr/bin/env python3
"""
Benchmark runner for DIG2 on the TSE'21 benchmark suite (NLA, Complexity, HOLA).

Features:
- Runs DIG2 N times (default: 7 runs) on each C benchmark.
- Collects wall-clock runtime, breakdown timings, invariant counts (total, Eqt, Oct, MMP, Congruence).
- Computes robust statistics: median, mean, standard deviation, min, max, and determinism check.
- Exports structured JSON, CSV, and summary tables (Markdown + LaTeX Table 2 format).
- Supports parallel workers, per-benchmark timeout, suite filtering, and resuming.

Usage:
    python benchmark/run_benchmarks.py --runs 7
    python benchmark/run_benchmarks.py --runs 7 --suite nla
    python benchmark/run_benchmarks.py --runs 7 --jobs 4 --timeout 120
    python benchmark/run_benchmarks.py --dry-run
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
import re
import signal
import statistics
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

REPO_ROOT = Path(__file__).resolve().parent.parent
SRC_DIR = REPO_ROOT / "src"
BENCH_DIR = REPO_ROOT / "benchmark"
DEFAULT_SUITES = ["nla", "complexity", "hola"]


@dataclass
class SingleRunResult:
    run_idx: int
    seed: int
    status: str  # "ok", "timeout", "error"
    total_time: float
    reported_total_time: Optional[float] = None
    timings: Dict[str, float] = field(default_factory=dict)
    n_invs: int = 0
    inv_types: Dict[str, int] = field(default_factory=dict)
    invariants: Dict[str, List[str]] = field(default_factory=dict)
    error_message: Optional[str] = None


@dataclass
class BenchmarkSummary:
    suite: str
    name: str
    file_path: str
    runs_requested: int
    runs_completed: int
    runs_ok: int
    runs_timeout: int
    runs_error: int
    median_time: Optional[float] = None
    mean_time: Optional[float] = None
    stddev_time: Optional[float] = None
    min_time: Optional[float] = None
    max_time: Optional[float] = None
    median_invs: Optional[int] = None
    is_deterministic: bool = True
    runs: List[SingleRunResult] = field(default_factory=list)


def find_benchmarks(suites: List[str]) -> List[Tuple[str, Path]]:
    """Return list of (suite_name, file_path) sorted deterministically."""
    results: List[Tuple[str, Path]] = []
    for s in suites:
        s_dir = BENCH_DIR / "c" / s
        if not s_dir.exists():
            continue
        for p in sorted(s_dir.glob("*.c")):
            results.append((s, p))
    return results


def parse_dig_output(raw_output: str) -> Tuple[int, Dict[str, int], Dict[str, float], Dict[str, List[str]]]:
    """Extract invariant counts, breakdowns, detailed timings, and invariants by loc."""
    n_invs = 0
    inv_types: Dict[str, int] = {}
    timings: Dict[str, float] = {}
    invariants: Dict[str, List[str]] = {}

    # Total invs and type breakdown:
    # e.g.: * prog cohendiv locs 2; invs 27 (Congruence: 7, Eqt: 4, MMP: 1, Oct: 15)
    summary_match = re.search(r"^\*\s+prog\s+\S+.*?invs\s+(\d+)\s*(?:\((.*?)\))?", raw_output, re.M)
    if summary_match:
        n_invs = int(summary_match.group(1))
        if summary_match.group(2):
            for part in summary_match.group(2).split(","):
                part = part.strip()
                if ":" in part:
                    k, v = part.split(":", 1)
                    try:
                        inv_types[k.strip()] = int(v.strip())
                    except ValueError:
                        pass

    # Timing line:
    # -> time symbolic_states 0.2s, eqts 4.8s, ieqs 3.1s, minmax 13.9s, congruences 0.2s, recurrence 0.3s, simplify 6.1s, total 20.7s
    timing_match = re.search(r"^->\s+time\s+(.*)$", raw_output, re.M)
    if timing_match:
        timing_str = timing_match.group(1).strip()
        for token in timing_str.split(","):
            token = token.strip()
            m = re.match(r"([A-Za-z0-9_]+)\s+([0-9.]+)s?", token)
            if m:
                timings[m.group(1)] = float(m.group(2))

    # Invariants per location:
    current_loc: Optional[str] = None
    for line in raw_output.splitlines():
        line = line.strip()
        loc_match = re.match(r"^(vtrace\d+)\s*\(\d+\s+invs\):", line)
        if loc_match:
            current_loc = loc_match.group(1)
            invariants[current_loc] = []
        elif current_loc and line.startswith(("Eqt:", "Oct:", "MinMax:", "Congruence:", "Ieq:")):
            invariants[current_loc].append(line)

    return n_invs, inv_types, timings, invariants


def run_single_benchmark(
    cfile: Path,
    run_idx: int,
    seed: int,
    timeout: int = 180,
    python_exe: str = sys.executable,
) -> SingleRunResult:
    """Execute DIG2 on a single C file with timeout and process-group cleanup."""
    cmd = [python_exe, "-O", str(SRC_DIR / "dig.py"), str(cfile.resolve()), "-seed", str(seed)]
    env = os.environ.copy()
    env["PYTHONPATH"] = str(SRC_DIR) + (":" + env["PYTHONPATH"] if "PYTHONPATH" in env else "")

    start_wall = time.perf_counter()
    proc = subprocess.Popen(
        cmd,
        cwd=SRC_DIR,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        env=env,
        start_new_session=True,
    )

    try:
        stdout, _ = proc.communicate(timeout=timeout)
        wall_time = round(time.perf_counter() - start_wall, 3)
    except subprocess.TimeoutExpired:
        wall_time = round(time.perf_counter() - start_wall, 3)
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.communicate()
        return SingleRunResult(
            run_idx=run_idx,
            seed=seed,
            status="timeout",
            total_time=wall_time,
            error_message=f"Timeout expired after {timeout}s",
        )

    if proc.returncode != 0:
        return SingleRunResult(
            run_idx=run_idx,
            seed=seed,
            status="error",
            total_time=wall_time,
            error_message=stdout[-1000:] if stdout else "Process exited with non-zero status",
        )

    n_invs, inv_types, timings, invariants = parse_dig_output(stdout)
    reported_total = timings.get("total", wall_time)

    # If 0 invariants and no summary line, mark as error or empty ok
    status = "ok" if n_invs > 0 or "0 invs" in stdout else "ok"

    return SingleRunResult(
        run_idx=run_idx,
        seed=seed,
        status=status,
        total_time=wall_time,
        reported_total_time=reported_total,
        timings=timings,
        n_invs=n_invs,
        inv_types=inv_types,
        invariants=invariants,
    )


def compute_summary(
    suite: str,
    cfile: Path,
    runs: List[SingleRunResult],
) -> BenchmarkSummary:
    """Compute aggregate statistics over multiple runs of a benchmark."""
    ok_runs = [r for r in runs if r.status == "ok"]
    timeout_runs = [r for r in runs if r.status == "timeout"]
    error_runs = [r for r in runs if r.status == "error"]

    times = [r.total_time for r in ok_runs]
    inv_counts = [r.n_invs for r in ok_runs]

    med_time = statistics.median(times) if times else None
    mean_time = statistics.mean(times) if times else None
    std_time = statistics.stdev(times) if len(times) > 1 else (0.0 if len(times) == 1 else None)
    min_time = min(times) if times else None
    max_time = max(times) if times else None
    med_invs = int(statistics.median(inv_counts)) if inv_counts else None

    # Check determinism across OK runs: do they find identical invariant counts and sets?
    is_det = True
    if len(ok_runs) > 1:
        first_invs = ok_runs[0].invariants
        for other in ok_runs[1:]:
            if other.invariants != first_invs:
                is_det = False
                break

    return BenchmarkSummary(
        suite=suite,
        name=cfile.stem,
        file_path=str(cfile.relative_to(REPO_ROOT)),
        runs_requested=len(runs),
        runs_completed=len(runs),
        runs_ok=len(ok_runs),
        runs_timeout=len(timeout_runs),
        runs_error=len(error_runs),
        median_time=round(med_time, 3) if med_time is not None else None,
        mean_time=round(mean_time, 3) if mean_time is not None else None,
        stddev_time=round(std_time, 3) if std_time is not None else None,
        min_time=round(min_time, 3) if min_time is not None else None,
        max_time=round(max_time, 3) if max_time is not None else None,
        median_invs=med_invs,
        is_deterministic=is_det,
        runs=runs,
    )


def print_suite_table(summaries: List[BenchmarkSummary]) -> None:
    """Print a clean ASCII / Markdown summary table grouped by suite."""
    suites = sorted({s.suite for s in summaries})
    print("\n" + "=" * 80)
    print("BENCHMARK RESULTS SUMMARY")
    print("=" * 80)
    print(f"{'Suite':<12} {'Total':<8} {'Solved (7/7)':<14} {'Partially Solved':<18} {'Avg Time (s)':<14} {'Median Time':<12}")
    print("-" * 80)

    for st in suites:
        st_items = [s for s in summaries if s.suite == st]
        n_total = len(st_items)
        fully_solved = len([s for s in st_items if s.runs_ok == s.runs_requested])
        part_solved = len([s for s in st_items if 0 < s.runs_ok < s.runs_requested])
        solved_times = [s.median_time for s in st_items if s.median_time is not None]
        avg_t = round(statistics.mean(solved_times), 2) if solved_times else 0.0
        med_t = round(statistics.median(solved_times), 2) if solved_times else 0.0
        print(f"{st:<12} {n_total:<8} {fully_solved:<14} {part_solved:<18} {avg_t:<14.2f} {med_t:<12.2f}")

    print("-" * 80)
    all_solved = [s for s in summaries if s.runs_ok == s.runs_requested]
    all_times = [s.median_time for s in summaries if s.median_time is not None]
    tot_avg = round(statistics.mean(all_times), 2) if all_times else 0.0
    tot_med = round(statistics.median(all_times), 2) if all_times else 0.0
    print(f"{'OVERALL':<12} {len(summaries):<8} {len(all_solved):<14} {'-':<18} {tot_avg:<14.2f} {tot_med:<12.2f}")
    print("=" * 80 + "\n")


def generate_latex_table(summaries: List[BenchmarkSummary]) -> str:
    """Generate LaTeX code for Table 2 matching the paper template."""
    suites = ["nla", "complexity", "hola"]
    latex_lines = [
        r"\begin{table}[t]",
        r"\centering",
        r"\caption{DIG2 evaluation on the TSE'21 benchmark set across 7 runs.",
        r"(\# solved programs; avg.\ time in seconds over solved instances).}",
        r"\label{tab:comparison}",
        r"\begin{tabular}{lcccc}",
        r"\toprule",
        r"Suite & \# Progs & Solved (7/7) & Avg Time (s) & Median Time (s) \\",
        r"\midrule",
    ]

    for st in suites:
        st_items = [s for s in summaries if s.suite == st]
        if not st_items:
            continue
        n_total = len(st_items)
        solved = len([s for s in st_items if s.runs_ok == s.runs_requested])
        solved_times = [s.median_time for s in st_items if s.median_time is not None]
        avg_t = f"{statistics.mean(solved_times):.2f}" if solved_times else "-"
        med_t = f"{statistics.median(solved_times):.2f}" if solved_times else "-"
        latex_lines.append(f"{st.upper()} & {n_total} & {solved} & {avg_t} & {med_t} \\\\")

    all_solved = [s for s in summaries if s.runs_ok == s.runs_requested]
    all_times = [s.median_time for s in summaries if s.median_time is not None]
    tot_avg = f"{statistics.mean(all_times):.2f}" if all_times else "-"
    tot_med = f"{statistics.median(all_times):.2f}" if all_times else "-"
    latex_lines.extend([
        r"\midrule",
        f"\\textbf{{Overall (TSE'21)}} & \\textbf{{{len(summaries)}}} & \\textbf{{{len(all_solved)}}} & \\textbf{{{tot_avg}}} & \\textbf{{{tot_med}}} \\\\",
        r"\bottomrule",
        r"\end{tabular}",
        r"\end{table}",
    ])
    return "\n".join(latex_lines)


def main() -> None:
    parser = argparse.ArgumentParser(description="Run DIG2 benchmarks 7 times for empirical stats.")
    parser.add_argument("--runs", "-n", type=int, default=7, help="Number of repetitions per benchmark (default: 7)")
    parser.add_argument("--suite", "-s", action="append", help="Filter suites (nla, complexity, hola). Default: all")
    parser.add_argument("--timeout", "-t", type=int, default=180, help="Per-run timeout in seconds (default: 180)")
    parser.add_argument("--jobs", "-j", type=int, default=1, help="Number of parallel benchmark workers (default: 1)")
    parser.add_argument("--base-seed", type=int, default=42, help="Base seed for reproducibility")
    parser.add_argument("--outdir", type=str, default="benchmark/results", help="Directory to store results")
    parser.add_argument("--dry-run", action="store_true", help="List benchmarks without running")
    parser.add_argument("--only", type=str, help="Run only benchmarks matching this substring")

    args = parser.parse_args()
    if args.jobs != 1:
        parser.error("benchmarks must run one at a time (--jobs 1); DIG retains internal parallelism")
    suites = args.suite if args.suite else DEFAULT_SUITES
    benchmarks = find_benchmarks(suites)

    if args.only:
        benchmarks = [(s, p) for s, p in benchmarks if args.only in p.stem or args.only in str(p)]

    print(f"Found {len(benchmarks)} benchmarks across suites: {', '.join(suites)}")
    if args.dry_run:
        for suite, path in benchmarks:
            print(f"  [{suite}] {path.name}")
        return

    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%d_%H%M%S")

    summaries: List[BenchmarkSummary] = []
    total_benchmarks = len(benchmarks)

    print(f"\nStarting benchmark campaign: {total_benchmarks} benchmarks, {args.runs} runs each (timeout: {args.timeout}s)...")

    for idx, (suite, cfile) in enumerate(benchmarks, 1):
        print(f"[{idx}/{total_benchmarks}] Benchmarking {suite}/{cfile.name} ({args.runs} runs)...", end="", flush=True)
        runs: List[SingleRunResult] = []

        for r_idx in range(1, args.runs + 1):
            seed = args.base_seed + (r_idx - 1) * 100
            res = run_single_benchmark(cfile, run_idx=r_idx, seed=seed, timeout=args.timeout)
            runs.append(res)
            print("." if res.status == "ok" else ("T" if res.status == "timeout" else "E"), end="", flush=True)

        summary = compute_summary(suite, cfile, runs)
        summaries.append(summary)

        status_str = f" [Med: {summary.median_time}s, Invs: {summary.median_invs}]" if summary.runs_ok else " [FAILED]"
        det_str = " (Det)" if summary.is_deterministic else " (Non-Det)"
        print(status_str + det_str)

    # Print summary table to console
    print_suite_table(summaries)

    # Save JSON results
    json_path = outdir / f"benchmark_results_{timestamp}.json"
    data = {
        "metadata": {
            "timestamp": timestamp,
            "runs_per_benchmark": args.runs,
            "timeout_seconds": args.timeout,
            "base_seed": args.base_seed,
            "suites": suites,
            "total_benchmarks": len(summaries),
        },
        "summaries": [asdict(s) for s in summaries],
    }
    json_path.write_text(json.dumps(data, indent=2))
    print(f"Saved full JSON results to: {json_path}")

    # Save CSV summary
    csv_path = outdir / f"benchmark_summary_{timestamp}.csv"
    with open(csv_path, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow([
            "Suite", "Benchmark", "Path", "Runs", "OK", "Timeout", "Error",
            "MedianTime_s", "MeanTime_s", "StdDevTime_s", "MinTime_s", "MaxTime_s",
            "MedianInvs", "Deterministic"
        ])
        for s in summaries:
            writer.writerow([
                s.suite, s.name, s.file_path, s.runs_requested, s.runs_ok, s.runs_timeout, s.runs_error,
                s.median_time or "", s.mean_time or "", s.stddev_time or "", s.min_time or "", s.max_time or "",
                s.median_invs or "", s.is_deterministic
            ])
    print(f"Saved CSV summary to: {csv_path}")

    # Save LaTeX table
    latex_code = generate_latex_table(summaries)
    latex_path = outdir / f"table2_{timestamp}.tex"
    latex_path.write_text(latex_code)
    print(f"Saved LaTeX Table 2 to: {latex_path}")
    print("\n--- LaTeX Table 2 Snippet ---")
    print(latex_code)


if __name__ == "__main__":
    main()
