#!/usr/bin/env python3
"""Serial Lean-certification sweep over DIG C benchmarks.

Runs `dig.py <prog> -seed S --certify-lean` ONE PROGRAM AT A TIME (AGENTS.md:
never run DIG benchmark invocations concurrently; each run may use DIG's
internal parallelism), keeps each run's certificate and reports under
`--out/<prog>/`, and writes `summary.json` / `summary.md`.

    .venv/bin/python benchmark/run_lean_cert.py benchmark/c/nla/*.c \
        --out benchmark/results/lean_cert --seed 42

Golden baselines are never touched. `knuth.c` is skipped by default
(deferred per AGENTS.md); pass --include-knuth to run it.
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PY = ROOT / ".venv" / "bin" / "python"


def run_one(cfile: Path, out: Path, seed: int, timeout: int) -> dict:
    pdir = out / cfile.stem
    if pdir.exists():
        shutil.rmtree(pdir)
    pdir.mkdir(parents=True)
    with tempfile.TemporaryDirectory(prefix="leancert_") as tmp:
        cmd = [str(PY), "-O", "dig.py", str(cfile.resolve()), "-seed", str(seed),
               "-tmpdir", tmp, "--certify-lean",
               "--lean-out", str(pdir / "certificate.lean")]
        t0 = time.monotonic()
        try:
            p = subprocess.run(cmd, cwd=ROOT / "src", capture_output=True,
                               text=True, timeout=timeout)
            rc, log = p.returncode, p.stdout + p.stderr
        except subprocess.TimeoutExpired as e:
            rc, log = "timeout", f"timeout after {timeout}s\n{e.stdout or ''}"
        wall = time.monotonic() - t0
        (pdir / "dig_output.txt").write_text(log if isinstance(log, str) else str(log))
        runs = [d for d in Path(tmp).iterdir() if d.is_dir()]
        rep, timing = None, {}
        if runs:
            r = runs[0]
            for name in ("lean_certification.json", "evidence.json", "settings.json"):
                if (r / name).is_file():
                    shutil.copy(r / name, pdir / name)
            if (r / "lean_certification.json").is_file():
                rep = json.loads((r / "lean_certification.json").read_text())
    row = {"program": cfile.stem, "seed": seed, "returncode": rc,
           "wall_sec": round(wall, 1),
           "flags": f"-seed {seed} --certify-lean"}
    if rep is None:
        row.update(status="no-report")
        return row
    kinds: dict[str, list[int]] = {}
    for c in rep["certified"]:
        kinds.setdefault(c["kind"], [0, 0])[0] += 1
    for c in rep["certified"] + rep["dropped"] + rep["unsupported"]:
        kinds.setdefault(c["kind"], [0, 0])[1] += 1
    row.update(
        status=rep["status"], reason=rep.get("reason"),
        certified=len(rep["certified"]), dropped=len(rep["dropped"]),
        unsupported=len(rep["unsupported"]),
        by_kind={k: f"{v[0]}/{v[1]}" for k, v in sorted(kinds.items())},
        rounds=rep["rounds"], lean_sec=round(rep["lean_elapsed_sec"], 1),
        loops=len(rep.get("loops", [])),
        certificate_sha256=rep.get("certificate_sha256"),
        certified_eqts=[f'{c["loc"]}: {c["text"]}' for c in rep["certified"]
                        if c["kind"] == "Eqt"],
        dropped_eqts=[f'{c["loc"]}: {c["text"]}' for c in rep["dropped"]
                      if c["kind"] == "Eqt"],
    )
    return row


def write_summary(rows: list[dict], out: Path) -> None:
    (out / "summary.json").write_text(json.dumps(rows, indent=1) + "\n")
    lines = ["# Lean 4 certification sweep", "",
             "Each row: one serial `dig.py --certify-lean` run. `certified` "
             "counts DIG invariants proved by Lean to hold on every execution "
             "(mathematical integers); `by kind` is certified/total.", "",
             "| program | status | certified | dropped | unsup. | by kind | rounds | Lean s | wall s |",
             "|---|---|---|---|---|---|---|---|---|"]
    for r in rows:
        bk = ", ".join(f"{k} {v}" for k, v in (r.get("by_kind") or {}).items())
        lines.append(
            f"| {r['program']} | {r['status']} | {r.get('certified', '')} | "
            f"{r.get('dropped', '')} | {r.get('unsupported', '')} | {bk} | "
            f"{r.get('rounds', '')} | {r.get('lean_sec', '')} | {r['wall_sec']} |")
    lines += ["", "## Certified equalities", ""]
    for r in rows:
        for e in r.get("certified_eqts", []):
            lines.append(f"- `{r['program']}` {e}")
    lines += ["", "## Dropped equalities (not proved inductive by Lean)", ""]
    for r in rows:
        for e in r.get("dropped_eqts", []):
            lines.append(f"- `{r['program']}` {e}")
    (out / "summary.md").write_text("\n".join(lines) + "\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("programs", nargs="+", type=Path)
    ap.add_argument("--out", type=Path, default=ROOT / "benchmark/results/lean_cert")
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--timeout", type=int, default=3600, help="per program")
    ap.add_argument("--include-knuth", action="store_true")
    a = ap.parse_args()
    a.out = a.out.resolve()            # dig.py runs with cwd=src/
    a.out.mkdir(parents=True, exist_ok=True)
    rows = []
    for cfile in sorted(a.programs):
        if cfile.stem == "knuth" and not a.include_knuth:
            rows.append({"program": "knuth", "seed": a.seed, "status": "skipped",
                         "reason": "deferred (AGENTS.md)", "wall_sec": 0})
            continue
        row = run_one(cfile, a.out, a.seed, a.timeout)       # strictly serial
        rows.append(row)
        print(f"{row['program']}: {row['status']} certified={row.get('certified')} "
              f"wall={row['wall_sec']}s", flush=True)
        write_summary(rows, a.out)
    write_summary(rows, a.out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
