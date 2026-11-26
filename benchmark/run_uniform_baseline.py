#!/usr/bin/env python3
"""Run the uniform seven-seed baseline serially and keep paper progress current."""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import signal
import statistics
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "src"
OUT = ROOT / "benchmark/results/uniform_baseline_no_recurrence_20261009"
LOCK = ROOT / "benchmark/results/.tse_recovery.lock"
SEEDS = tuple(range(7))
DEPTH = 16
TIMEOUT_SECONDS = 600
TYPES = "eqt,ieq,minmax,congruence"
SUITES = (
    ("nla", 33, sorted((ROOT / "benchmark/c/nla").glob("*.c"))),
    ("complexity", 19, sorted((ROOT / "benchmark/c/complexity").glob("*.c"))),
    ("hola", 45, sorted((ROOT / "benchmark/c/hola").glob("*.c"))),
    # ("NLA-mosaic", 14, sorted((ROOT / "benchmark/c/NLA-mosaic").glob("*.c"))),  # Excluded at the user's request.
)
HISTORICAL = {"nla": "73.1", "complexity": "14.8", "hola": "29.4"}
LABELS = {"nla": "NLA", "complexity": "Complexity", "hola": "HOLA"}
PROGRAM_TOTAL = sum(expected for _, expected, _ in SUITES)
RUN_TOTAL = PROGRAM_TOTAL * len(SEEDS)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def atomic_json(path: Path, obj: object) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)


def load_state() -> dict:
    path = OUT / "status.json"
    return json.loads(path.read_text()) if path.exists() else {"runs": {}}


def suite_stats(state: dict, suite: str, expected_programs: int) -> dict:
    runs = state["runs"]
    selected = [v for v in runs.values() if v["suite"] == suite]
    attempted = len(selected)
    success = [r for r in selected if r["status"] == "completed"]
    timeouts = sum(r["status"] == "timeout" for r in selected)
    errors = sum(r["status"] in {"error", "exception"} for r in selected)
    programs_done = 0
    for suite_name, _, files in SUITES:
        if suite_name == suite:
            for source in files:
                program_runs = [runs.get(f"{suite}/{source.stem}/{seed}") for seed in SEEDS]
                if all(r is not None for r in program_runs):
                    programs_done += 1
            break
    return {
        "programs_done": programs_done,
        "programs_expected": expected_programs,
        "attempted": attempted,
        "attempted_expected": expected_programs * len(SEEDS),
        "success": len(success),
        "timeouts": timeouts,
        "errors": errors,
        "median": statistics.median([r["dig_seconds"] for r in success]) if success else None,
    }


def fmt(value: float | None) -> str:
    return "--" if value is None else f"{value:.2f}"


def refresh_reports(state: dict) -> None:
    rows = []
    markdown = [
        "# Uniform baseline campaign (2026-10-09)", "",
        f"Suites in order: {', '.join(f'{LABELS[s]} ({n})' for s, n, _ in SUITES)}; NLA-mosaic is excluded.",
        f"Configuration: seeds 0--6; timeout {TIMEOUT_SECONDS}s; depth {DEPTH}; types `{TYPES}`; no explicit degree cap; arrays and static recurrence inference excluded.",
        "Trace-based equality fitting remains enabled. DIG invocations run one at a time. A completed attempt is a DIG exit with a saved result; timeouts and errors are reported separately.", "",
        "| Suite | Programs with all 7 attempts | Attempts | Successful results | Timeouts | Errors | Median DIG time (s) |",
        "|---|---:|---:|---:|---:|---:|---:|",
    ]
    total = {k: 0 for k in ("programs_done", "programs_expected", "attempted", "attempted_expected", "success", "timeouts", "errors")}
    all_times = []
    for suite, expected, files in SUITES:
        if len(files) != expected:
            raise RuntimeError(f"Expected {expected} {suite} files, found {len(files)}")
        stats = suite_stats(state, suite, expected)
        rows.append(f"{LABELS[suite]} & {stats['programs_done']}/{expected} & {stats['attempted']}/{expected * 7} & {HISTORICAL[suite]} & {fmt(stats['median'])} \\\\")
        markdown.append(f"| {LABELS[suite]} | {stats['programs_done']}/{expected} | {stats['attempted']}/{expected * 7} | {stats['success']} | {stats['timeouts']} | {stats['errors']} | {fmt(stats['median'])} |")
        for key in total:
            total[key] += stats[key]
        all_times.extend(r["dig_seconds"] for r in state["runs"].values()
                         if r["suite"] == suite and r["status"] == "completed")
    rows.append(f"\\textbf{{Overall}} & \\textbf{{{total['programs_done']}/{PROGRAM_TOTAL}}} & \\textbf{{{total['attempted']}/{RUN_TOTAL}}} & \\textbf{{38.2}} & \\textbf{{{fmt(statistics.median(all_times) if all_times else None)}}} \\\\")
    markdown.append(f"| **Overall** | **{total['programs_done']}/{PROGRAM_TOTAL}** | **{total['attempted']}/{RUN_TOTAL}** | **{total['success']}** | **{total['timeouts']}** | **{total['errors']}** | **{fmt(statistics.median(all_times) if all_times else None)}** |")
    markdown += ["", f"Last updated: {time.strftime('%Y-%m-%d %H:%M:%S %Z')}", ""]
    (OUT / "RUN_STATUS.md").write_text("\n".join(markdown))

    tex_rows = ["% Generated campaign progress; incorporate into paper only after editing is complete."]
    tex_rows.extend(rows)
    (OUT / "table_progress.tex").write_text("\n".join(tex_rows) + "\n")


def run_one(state: dict, suite: str, source: Path, seed: int, env: dict[str, str]) -> None:
    key = f"{suite}/{source.stem}/{seed}"
    if key in state["runs"]:
        return
    run_root = OUT / "runs" / suite / source.stem / f"seed_{seed}"
    artifacts = run_root / "artifacts"
    artifacts.mkdir(parents=True, exist_ok=True)
    log = run_root / "run.log"
    cmd = [sys.executable, "-u", "-O", str(ROOT / "src/dig.py"), str(source),
           "--se_maxdepth", str(DEPTH), "-types", TYPES, "-seed", str(seed), "-tmpdir", str(artifacts)]
    started = time.time()
    status = "error"
    returncode = None
    result = None
    try:
        with log.open("w") as out:
            out.write("COMMAND: " + " ".join(cmd) + "\n")
            out.write(f"TIMEOUT_SECONDS: {TIMEOUT_SECONDS}\n")
            out.flush()
            proc = subprocess.Popen(cmd, cwd=ROOT, env=env, stdout=out,
                                    stderr=subprocess.STDOUT, start_new_session=True)
            try:
                returncode = proc.wait(timeout=TIMEOUT_SECONDS)
                result_files = list(artifacts.glob(f"Dig_{seed}_*/result"))
                result = str(result_files[0].relative_to(OUT)) if len(result_files) == 1 else None
                status = "completed" if returncode == 0 and result else "error"
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
                returncode = proc.returncode
                status = "timeout"
    except Exception as exc:
        with log.open("a") as out:
            out.write(f"\nRUNNER_EXCEPTION: {exc!r}\n")
        status = "exception"
    elapsed = time.time() - started
    dig_seconds = None
    if result:
        sys.path.insert(0, str(SRC))
        try:
            from helpers.vcommon import vload
            raw = vload(OUT / result)
            dig_seconds = float(raw.time_d["total"])
        except Exception:
            dig_seconds = None
    state["runs"][key] = {
        "suite": suite, "program": source.stem, "source": str(source.relative_to(ROOT)),
        "source_sha256": sha256(source), "seed": seed, "status": status,
        "returncode": returncode, "elapsed_seconds": round(elapsed, 3),
        "dig_seconds": round(dig_seconds, 3) if dig_seconds is not None else round(elapsed, 3) if status == "completed" else None,
        "result": result, "log": str(log.relative_to(OUT)),
    }
    atomic_json(OUT / "status.json", state)
    refresh_reports(state)
    print(f"{key}: {status} ({elapsed:.1f}s)", flush=True)


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    for suite, expected, files in SUITES:
        if len(files) != expected:
            raise RuntimeError(f"Expected {expected} {suite} files, found {len(files)}")
    lockfile = LOCK.open("a")
    try:
        fcntl.flock(lockfile, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print(f"A recovery or parameter campaign holds {LOCK}; refusing to overlap.", file=sys.stderr)
        return 2

    state = load_state()
    state.setdefault("configuration", {
        "seeds": list(SEEDS), "timeout_seconds": TIMEOUT_SECONDS, "depth": DEPTH,
        "types": TYPES, "array_inference": False, "outer_concurrency": 1,
        "python": sys.version, "source_sha256": {str(p.relative_to(ROOT)): sha256(p) for p in (ROOT / "src").rglob("*.py")},
    })
    state["configuration"]["types"] = TYPES
    state["configuration"]["suite_order"] = [suite for suite, _, _ in SUITES]
    state["configuration"]["excluded_suites"] = ["NLA-mosaic"]
    state["configuration"]["program_count"] = PROGRAM_TOTAL
    atomic_json(OUT / "status.json", state)
    env = os.environ.copy()
    env["PYTHONPATH"] = str(SRC) + (os.pathsep + env["PYTHONPATH"] if env.get("PYTHONPATH") else "")
    refresh_reports(state)

    programs = sum(len(files) for _, _, files in SUITES)
    print(f"Starting uniform baseline: {programs} programs, {len(SEEDS)} seeds, "
          f"{TIMEOUT_SECONDS}s timeout, depth {DEPTH}, types {TYPES}; strictly serial.", flush=True)
    for suite, _, files in SUITES:
        for source in files:
            for seed in SEEDS:
                run_one(state, suite, source, seed, env)
    state["finished_at"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
    atomic_json(OUT / "status.json", state)
    refresh_reports(state)
    print("Uniform baseline campaign finished.", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
