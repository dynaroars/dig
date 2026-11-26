#!/usr/bin/env python3
"""
Clean, isolated, reproducible evaluation campaign runner for all 113 benchmarks.
Runs all 113 programs from scratch across 7 seeds (0..6) = 791 runs.
Outputs to a dedicated directory: benchmark/results/campaign_full_791/
Logs per-run stdout/stderr, execution time, exit codes, and structured manifest.json.
"""
from __future__ import annotations

import concurrent.futures
import datetime
import json
import os
import platform
import signal
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SRC_DIR = REPO_ROOT / "src"
DIG_PY = SRC_DIR / "dig.py"
OUT_DIR = REPO_ROOT / "benchmark/results/campaign_full_791"
LOGS_DIR = OUT_DIR / "logs"

# 4 Suites: 113 programs
NLA_FILES = sorted((REPO_ROOT / "benchmark/c/nla").glob("*.c"))
MOSAIC_FILES = sorted((REPO_ROOT / "benchmark/c/NLA-mosaic").glob("*.c"))
COMP_FILES = sorted((REPO_ROOT / "benchmark/c/complexity").glob("*.c"))
HOLA_FILES = sorted((REPO_ROOT / "benchmark/c/hola").glob("*.c"))

ALL_BENCHMARKS = (
    [("nla", p) for p in NLA_FILES] +
    [("NLA-mosaic", p) for p in MOSAIC_FILES] +
    [("complexity", p) for p in COMP_FILES] +
    [("hola", p) for p in HOLA_FILES]
)

def get_git_commit() -> str:
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, text=True).strip()
    except Exception:
        return "unknown"

def get_z3_version() -> str:
    try:
        import z3
        return z3.get_version_string()
    except Exception as ex:
        return f"unknown ({ex})"

def run_single_seed(task):
    suite, filepath, seed, timeout_sec = task
    prog_stem = filepath.stem
    bmdir = OUT_DIR / prog_stem
    bmdir.mkdir(parents=True, exist_ok=True)
    
    prog_log_dir = LOGS_DIR / suite / prog_stem
    prog_log_dir.mkdir(parents=True, exist_ok=True)
    log_file = prog_log_dir / f"seed_{seed}.log"

    cmd = [
        sys.executable, "-u", "-O", str(DIG_PY),
        str(filepath.resolve()),
        "-seed", str(seed),
        "-tmpdir", str(bmdir)
    ]
    env = os.environ.copy()
    env["PYTHONPATH"] = str(SRC_DIR) + (":" + env["PYTHONPATH"] if "PYTHONPATH" in env else "")

    st = time.time()
    outcome = "unknown"
    returncode = None
    output_text = ""
    timed_out = False

    try:
        p = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            env=env,
            start_new_session=True,
        )
        try:
            output_text, _ = p.communicate(timeout=timeout_sec)
            returncode = p.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass
            output_text, _ = p.communicate()
            returncode = -9
    except Exception as ex:
        output_text = f"Exception during execution: {ex}"
        returncode = -1

    elapsed = round(time.time() - st, 3)

    # Determine structured outcome
    # Check if a result file was generated for this seed
    has_result = False
    result_path = None
    for d in bmdir.iterdir():
        if d.is_dir() and d.name.startswith(f"Dig_{seed}_") and (d / "result").is_file():
            has_result = True
            result_path = str((d / "result").relative_to(REPO_ROOT))
            break

    if timed_out:
        outcome = "timeout"
    elif returncode == 0 and has_result:
        outcome = "success"
    elif "cannot obtain symstates" in output_text or "unreachable locs" in output_text:
        outcome = "depth_limit"
    elif returncode != 0:
        outcome = f"error_exit_{returncode}"
    elif not has_result:
        outcome = "no_invariants_found"

    # Write per-run execution log
    with open(log_file, "w", encoding="utf-8") as lf:
        lf.write(f"=== DIG-KN Run Log ===\n")
        lf.write(f"Suite: {suite}\n")
        lf.write(f"Program: {filepath.name}\n")
        lf.write(f"Seed: {seed}\n")
        lf.write(f"Timestamp: {datetime.datetime.now(datetime.timezone.utc).isoformat()}\n")
        lf.write(f"Command: {' '.join(cmd)}\n")
        lf.write(f"Elapsed: {elapsed}s\n")
        lf.write(f"Returncode: {returncode}\n")
        lf.write(f"Outcome: {outcome}\n")
        lf.write(f"Result File: {result_path}\n")
        lf.write(f"=== Output ===\n")
        lf.write(output_text)

    record = {
        "suite": suite,
        "program": filepath.name,
        "stem": prog_stem,
        "seed": seed,
        "elapsed_sec": elapsed,
        "returncode": returncode,
        "outcome": outcome,
        "has_result": has_result,
        "result_path": result_path,
        "log_path": str(log_file.relative_to(REPO_ROOT))
    }

    return record

def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    LOGS_DIR.mkdir(parents=True, exist_ok=True)
    num_seeds = 7
    timeout_per_seed = 45.0
    max_workers = 1

    metadata = {
        "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "git_commit": get_git_commit(),
        "python_version": sys.version,
        "platform": platform.platform(),
        "processor": platform.processor(),
        "z3_version": get_z3_version(),
        "total_benchmarks": len(ALL_BENCHMARKS),
        "total_requested_runs": len(ALL_BENCHMARKS) * num_seeds,
        "timeout_per_seed_sec": timeout_per_seed,
        "parallel_workers": max_workers,
        "suites_breakdown": {
            "nla": len(NLA_FILES),
            "NLA-mosaic": len(MOSAIC_FILES),
            "complexity": len(COMP_FILES),
            "hola": len(HOLA_FILES)
        }
    }

    tasks = []
    for suite, filepath in ALL_BENCHMARKS:
        for s in range(num_seeds):
            tasks.append((suite, filepath, s, timeout_per_seed))

    print(f"=== Starting Isolated DIG-KN Evaluation Campaign (791 Runs) ===", flush=True)
    print(f"Output Directory: {OUT_DIR}", flush=True)
    print(f"Total benchmarks: {len(ALL_BENCHMARKS)} across 4 suites", flush=True)
    print(f"Total tasks: {len(tasks)} ({max_workers} worker, {timeout_per_seed}s per-seed timeout)\n", flush=True)

    start_time = time.time()
    results = []
    completed_count = 0

    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(run_single_seed, t): t for t in tasks}
        for future in concurrent.futures.as_completed(futures):
            rec = future.result()
            results.append(rec)
            completed_count += 1
            cur_elapsed = time.time() - start_time
            print(f"[{completed_count}/{len(tasks)} in {cur_elapsed:.1f}s] [{rec['suite']}/{rec['program']}] seed {rec['seed']}: {rec['outcome']} ({rec['elapsed_sec']}s)", flush=True)

    total_wall_time = round(time.time() - start_time, 2)
    metadata["total_campaign_wall_sec"] = total_wall_time

    # Sort results for deterministic manifest
    results.sort(key=lambda r: (r["suite"], r["program"], r["seed"]))

    manifest = {
        "metadata": metadata,
        "runs": results
    }

    manifest_file = OUT_DIR / "manifest.json"
    with open(manifest_file, "w", encoding="utf-8") as mf:
        json.dump(manifest, mf, indent=2)

    print(f"\n=== Campaign Finished in {total_wall_time}s ===", flush=True)
    print(f"Manifest written to {manifest_file}", flush=True)

if __name__ == "__main__":
    main()
