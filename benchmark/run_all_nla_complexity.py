#!/usr/bin/env python3
"""
Parallel benchmark runner for all NLA (33) and Complexity (20) benchmarks.
Runs 7 independent seeds per benchmark with a per-seed timeout using a process pool.
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

# 33 NLA benchmarks
NLA_FILES = sorted((REPO_ROOT / "benchmark/c/nla").glob("*.c"))
# 14 NLA-mosaic benchmarks
MOSAIC_FILES = sorted((REPO_ROOT / "benchmark/c/NLA-mosaic").glob("*.c"))
# 20 Complexity benchmarks
COMP_FILES = sorted((REPO_ROOT / "benchmark/c/complexity").glob("*.c"))

ALL_BENCHMARKS = [("nla", p) for p in NLA_FILES] + [("NLA-mosaic", p) for p in MOSAIC_FILES] + [("complexity", p) for p in COMP_FILES]

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
    timeout_per_seed = 45 # seconds
    max_workers = 1 # One DIG invocation at a time; keep internal parallelism.

    tasks = []
    for suite, filepath in ALL_BENCHMARKS:
        bmdir = OUT_DIR / filepath.stem
        completed = get_completed_seeds(bmdir)
        needed = [s for s in range(num_runs) if s not in completed]
        for s in needed:
            tasks.append((suite, filepath, s, timeout_per_seed))

    print(f"=== Starting NLA + Complexity Benchmark Run ===", flush=True)
    print(f"Total tasks to execute: {len(tasks)} (across {max_workers} worker, {timeout_per_seed}s timeout)\n", flush=True)

    completed_count = 0
    with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(run_single_benchmark_seed, t): t for t in tasks}
        for future in concurrent.futures.as_completed(futures):
            res = future.result()
            completed_count += 1
            print(f"({completed_count}/{len(tasks)}) {res}", flush=True)

    print("\n=== Benchmark execution finished. Generating comprehensive report... ===", flush=True)
    subprocess.run([sys.executable, str(REPO_ROOT / "benchmark/generate_report.py"), str(OUT_DIR)], check=True)

if __name__ == "__main__":
    main()
