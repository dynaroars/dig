#!/usr/bin/env python3
"""
Extended evaluation campaign runner for all 111 executable benchmark programs across all 4 suites:
NLA (33), NLA-mosaic (14), Complexity (19), HOLA (45).
Evaluates 111 programs across 7 seeds (0..6) = 777 runs with increased depth limits (--se_maxdepth 16)
and extended timeout (120.0s).
Outputs to dedicated directory: benchmark/results/campaign_extended_111/
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
OUT_DIR = REPO_ROOT / "benchmark/results/campaign_extended_111"
LOGS_DIR = OUT_DIR / "logs"

# 4 Target Suites: 111 executable programs (excluding bad-programs)
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
        "--se_maxdepth", "16",
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

    # Classification
    result_file = None
    if timed_out or returncode == -9 or elapsed >= timeout_sec:
        outcome = "timeout"
    elif returncode != 0:
        if "cannot obtain symstates" in output_text or "unreachable locs" in output_text:
            outcome = "depth_limit"
        else:
            outcome = f"error_exit_{returncode}"
    else:
        # Check if a result file was created for this seed
        matching_results = list(bmdir.glob(f"Dig_{seed}_*/result"))
        if matching_results:
            # pick newest
            matching_results.sort(key=lambda p: p.stat().st_mtime, reverse=True)
            result_file = str(matching_results[0].relative_to(REPO_ROOT))
            outcome = "success"
        elif "cannot obtain symstates" in output_text:
            outcome = "depth_limit"
        else:
            outcome = "no_result_file"

    # Write per-run log
    with open(log_file, "w") as f:
        f.write(f"=== BENCHMARK: {suite}/{prog_stem} (seed {seed}) ===\n")
        f.write(f"=== CMD: {' '.join(cmd)} ===\n")
        f.write(f"=== OUTCOME: {outcome} (returncode: {returncode}, elapsed: {elapsed}s) ===\n")
        if result_file:
            f.write(f"=== RESULT_FILE: {result_file} ===\n")
        f.write("\n" + output_text)

    print(f"[{suite}] {prog_stem} (seed {seed}): {outcome} ({elapsed}s)")

    return {
        "suite": suite,
        "program": prog_stem,
        "seed": seed,
        "source_file": str(filepath.relative_to(REPO_ROOT)),
        "outcome": outcome,
        "returncode": returncode,
        "elapsed_sec": elapsed,
        "result_file": result_file,
        "log_file": str(log_file.relative_to(REPO_ROOT)),
    }

def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    LOGS_DIR.mkdir(parents=True, exist_ok=True)

    seeds = list(range(7))
    timeout_sec = 120.0
    num_workers = 1

    tasks = []
    for suite, filepath in ALL_BENCHMARKS:
        for s in seeds:
            tasks.append((suite, filepath, s, timeout_sec))

    print(f"=== Launching Extended Evaluation Campaign (111 Programs) ===")
    print(f"Suites: NLA ({len(NLA_FILES)}), NLA-mosaic ({len(MOSAIC_FILES)}), Complexity ({len(COMP_FILES)}), HOLA ({len(HOLA_FILES)})")
    print(f"Total Programs: {len(ALL_BENCHMARKS)} | Total Runs: {len(tasks)} ({len(seeds)} seeds each)")
    print(f"Timeout: {timeout_sec}s | Depth Limit: --se_maxdepth 16 | Parallel Workers: {num_workers}")
    print(f"Output Directory: {OUT_DIR}\n")

    manifest = {
        "timestamp": datetime.datetime.now().isoformat(),
        "git_commit": get_git_commit(),
        "python_version": platform.python_version(),
        "platform": platform.platform(),
        "z3_version": get_z3_version(),
        "se_maxdepth": 16,
        "timeout_sec": timeout_sec,
        "num_workers": num_workers,
        "total_programs": len(ALL_BENCHMARKS),
        "total_runs": len(tasks),
        "runs": []
    }

    start_time = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=num_workers) as executor:
        futures = [executor.submit(run_single_seed, task) for task in tasks]
        for future in concurrent.futures.as_completed(futures):
            try:
                res = future.result()
                manifest["runs"].append(res)
            except Exception as ex:
                print(f"Task exception: {ex}")

    total_wall_time = round(time.time() - start_time, 2)
    manifest["total_wall_time_sec"] = total_wall_time

    manifest_file = OUT_DIR / "manifest.json"
    with open(manifest_file, "w") as f:
        json.dump(manifest, f, indent=2)

    print(f"\n=== Campaign Complete in {total_wall_time}s ===")
    print(f"Manifest written to: {manifest_file}")

if __name__ == "__main__":
    main()
