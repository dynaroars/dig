#!/usr/bin/env python3
"""
Parallel benchmark runner for all 113 benchmarks across 4 suites:
- nla: 33 programs
- NLA-mosaic: 14 programs
- complexity: 20 programs
- hola: 46 programs
Total: 113 programs x 7 seeds = 791 runs.
Runs with a per-seed timeout using a process pool with 6 worker threads.
"""
import concurrent.futures
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SRC_DIR = REPO_ROOT / "src"
DIG_PY = SRC_DIR / "dig.py"
OUT_DIR = REPO_ROOT / "benchmark/results/sample_run"

# Suites
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

def get_completed_seeds(bmdir: Path) -> set[int]:
    if not bmdir.is_dir():
        return set()
    seeds = set()
    for rd in bmdir.iterdir():
        if rd.is_dir() and (rd / "result").is_file():
            try:
                s = int(rd.name.split("_")[1])
                seeds.add(s)
            except (IndexError, ValueError):
                pass
    return seeds

def run_single_benchmark_seed(task):
    suite, filepath, seed, timeout_sec = task
    bmdir = OUT_DIR / filepath.stem
    bmdir.mkdir(parents=True, exist_ok=True)
    
    cmd = [
        sys.executable, "-u", "-O", str(DIG_PY),
        str(filepath.resolve()),
        "-seed", str(seed),
        "-tmpdir", str(bmdir)
    ]
    env = os.environ.copy()
    env["PYTHONPATH"] = str(SRC_DIR) + (":" + env["PYTHONPATH"] if "PYTHONPATH" in env else "")

    st = time.time()
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
            out, _ = p.communicate(timeout=timeout_sec)
            elapsed = time.time() - st
            return f"[{suite}/{filepath.name}] seed {seed}: OK in {elapsed:.2f}s (code {p.returncode})"
        except subprocess.TimeoutExpired:
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            except ProcessLookupError:
                pass
            p.communicate()
            return f"[{suite}/{filepath.name}] seed {seed}: TIMED OUT ({timeout_sec}s)"
    except Exception as ex:
        return f"[{suite}/{filepath.name}] seed {seed}: ERROR {ex}"

def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    num_runs = 7
    timeout_per_seed = 45  # seconds
    max_workers = 1        # One DIG invocation at a time.

    tasks = []
    for suite, filepath in ALL_BENCHMARKS:
        bmdir = OUT_DIR / filepath.stem
        completed = get_completed_seeds(bmdir)
        needed = [s for s in range(num_runs) if s not in completed]
        for s in needed:
            tasks.append((suite, filepath, s, timeout_per_seed))

    print(f"=== Starting Full 113-Program Benchmark Campaign (7 runs each) ===", flush=True)
    print(f"Total benchmarks: {len(ALL_BENCHMARKS)} (nla: {len(NLA_FILES)}, mosaic: {len(MOSAIC_FILES)}, comp: {len(COMP_FILES)}, hola: {len(HOLA_FILES)})", flush=True)
    print(f"Total tasks remaining to execute: {len(tasks)} (across {max_workers} parallel workers, {timeout_per_seed}s timeout)\n", flush=True)

    completed_count = 0
    start_time = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(run_single_benchmark_seed, t): t for t in tasks}
        for future in concurrent.futures.as_completed(futures):
            res = future.result()
            completed_count += 1
            elapsed_total = time.time() - start_time
            print(f"[{completed_count}/{len(tasks)} in {elapsed_total:.1f}s] {res}", flush=True)

    print(f"\nAll tasks finished in {time.time() - start_time:.2f}s.")

if __name__ == "__main__":
    main()
