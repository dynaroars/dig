#!/usr/bin/env python3
"""
Batch benchmark runner for DIG-KN.
Runs 7 independent seeds per benchmark with a per-seed timeout.
Saves results directly into the specified benchmark directory.
"""
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SRC_DIR = REPO_ROOT / "src"
DIG_PY = SRC_DIR / "dig.py"

BENCHMARKS = [
    # NLA
    ("nla", "benchmark/c/nla/ps2.c"),
    ("nla", "benchmark/c/nla/cohendiv.c"),
    ("nla", "benchmark/c/nla/egcd.c"),
    ("nla", "benchmark/c/nla/divbin.c"),
    ("nla", "benchmark/c/nla/mannadiv.c"),
    ("nla", "benchmark/c/nla/hard.c"),
    ("nla", "benchmark/c/nla/geo1.c"),
    # Complexity
    ("complexity", "benchmark/c/complexity/cav09_fig1a.c"),
    ("complexity", "benchmark/c/complexity/cav09_fig1d.c"),
    ("complexity", "benchmark/c/complexity/cav09_fig2d.c"),
    ("complexity", "benchmark/c/complexity/pldi09_fig4_1.c"),
    ("complexity", "benchmark/c/complexity/popl09_fig2_1.c"),
    ("complexity", "benchmark/c/complexity/popl09_fig2_2.c"),
    ("complexity", "benchmark/c/complexity/popl09_fig3_4.c"),
    # HOLA
    ("hola", "benchmark/c/hola/01.dig.c"),
    ("hola", "benchmark/c/hola/02.dig.c"),
    ("hola", "benchmark/c/hola/03.dig.c"),
    ("hola", "benchmark/c/hola/07.dig.c"),
    ("hola", "benchmark/c/hola/08.dig.c"),
    ("hola", "benchmark/c/hola/11.dig.c"),
    ("hola", "benchmark/c/hola/15.dig.c"),
    ("hola", "benchmark/c/hola/20.dig.c"),
]

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

def main():
    outdir = REPO_ROOT / "benchmark/results/sample_run"
    outdir.mkdir(parents=True, exist_ok=True)
    
    num_runs = 7
    timeout_per_seed = 45 # seconds
    
    env = os.environ.copy()
    env["PYTHONPATH"] = str(SRC_DIR) + (":" + env["PYTHONPATH"] if "PYTHONPATH" in env else "")

    print(f"=== Running Batch Benchmarks ({len(BENCHMARKS)} programs, {num_runs} seeds, timeout {timeout_per_seed}s) ===", flush=True)

    for idx, (suite, rel_path) in enumerate(BENCHMARKS, 1):
        target_file = REPO_ROOT / rel_path
        if not target_file.is_file():
            print(f"[{idx}/{len(BENCHMARKS)}] Skipping missing file: {rel_path}", flush=True)
            continue
            
        bmdir = outdir / target_file.stem
        bmdir.mkdir(parents=True, exist_ok=True)
        completed = get_completed_seeds(bmdir)
        needed = [s for s in range(num_runs) if s not in completed]
        
        if not needed:
            print(f"[{idx}/{len(BENCHMARKS)}] {suite}/{target_file.name}: all {num_runs} runs already completed.", flush=True)
            continue

        print(f"[{idx}/{len(BENCHMARKS)}] {suite}/{target_file.name}: running {len(needed)} seeds {needed}...", flush=True)

        for seed in needed:
            cmd = [
                sys.executable, "-u", "-O", str(DIG_PY),
                str(target_file.resolve()),
                "-seed", str(seed),
                "-tmpdir", str(bmdir)
            ]
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
                    out, _ = p.communicate(timeout=timeout_per_seed)
                    elapsed = time.time() - st
                    print(f"   -> Seed {seed}: completed in {elapsed:.2f}s (code {p.returncode})", flush=True)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(os.getpgid(p.pid), signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    p.communicate()
                    print(f"   -> Seed {seed}: TIMED OUT after {timeout_per_seed}s", flush=True)
            except Exception as ex:
                print(f"   -> Seed {seed}: error {ex}", flush=True)

    print("\n=== All benchmark runs finished. Generating updated report... ===", flush=True)
    subprocess.run([sys.executable, str(REPO_ROOT / "benchmark/generate_report.py"), str(outdir)], check=True)

if __name__ == "__main__":
    main()
