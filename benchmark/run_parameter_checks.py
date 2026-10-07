#!/usr/bin/env python3
"""Small serialized parameter experiments; preserve every run and its settings."""
import argparse
from collections import Counter
import fcntl
import hashlib
import json
import os
from pathlib import Path
import random
import signal
import subprocess
import sys
import time
import sympy

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "src"))
from analysis import Result
from parameter_oracle import check_targets

HARD = ["nla/cohencu", "nla/egcd2", "nla/egcd3", "nla/prod4br",
        "nla/prodbin", "nla/geo3", "nla/ps6", "nla/freire2", "nla/sqrt1",
        "hola/24.dig", "hola/34.dig"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=ROOT)
    parser.add_argument("--programs", nargs="+")
    parser.add_argument("--seeds", type=int, nargs="+", default=[0])
    parser.add_argument("--timeout", type=float, default=240)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--extra", nargs=argparse.REMAINDER, default=[])
    parser.add_argument("--omit-setting", nargs="*", default=[])
    args = parser.parse_args()
    fixture = json.loads((ROOT / "benchmark/parameter_targets.json").read_text())
    specs = fixture["targets"]
    rng = random.Random(20261007)
    spots = []
    for suite in ("nla", "complexity", "hola"):
        eligible = sorted(k for k in fixture["selection_pool"] if k.startswith(suite + "/")
                          and k not in HARD and k != "nla/knuth")
        spots.extend(rng.sample(eligible, 2))
    programs = args.programs or HARD + spots
    for name in programs:
        if name not in specs:
            parser.error(f"program outside this limited fixture: {name}")
    if "nla/knuth" in programs:
        parser.error("Knuth is deferred")
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    lockpath = ROOT / "benchmark/results/.tse_recovery.lock"
    lockpath.parent.mkdir(parents=True, exist_ok=True)
    with lockpath.open("w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        sources = {str(p.relative_to(args.source_root)): hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in (args.source_root / "src").rglob("*.py")}
        manifest = {"outer_concurrency": 1, "source_root": str(args.source_root),
                    "source_sha256": sources, "spot_selection_seed": 20261007,
                    "hard": HARD, "random_spots": spots, "runs": []}
        for seed in args.seeds:
            for name in programs:
                spec = specs[name]
                dest = out / name / f"seed_{seed}"
                dest.mkdir(parents=True, exist_ok=True)
                cmd = [sys.executable, "-u", "-O", str(args.source_root / "src/dig.py"),
                       str(ROOT / spec["source"]), "-se_maxdepth", str(spec["depth"]),
                       "-seed", str(seed), "-types", "eqt,ieq,minmax,array,recurrence",
                       "-tmpdir", str(dest), "-log_level", "2"]
                for key in ("maxdeg", "inpMaxV", "ideg", "iterms", "icoefs"):
                    if key in spec and key not in args.omit_setting:
                        cmd.extend(["-" + key, str(spec[key])])
                cmd.extend(args.extra)
                before = set(dest.glob("Dig_*/result"))
                started = time.monotonic()
                with (dest / "run.log").open("w") as log:
                    proc = subprocess.Popen(cmd, cwd=ROOT, stdout=log,
                                            stderr=subprocess.STDOUT, start_new_session=True)
                    try:
                        returncode = proc.wait(timeout=args.timeout)
                    except subprocess.TimeoutExpired:
                        os.killpg(proc.pid, signal.SIGKILL)
                        returncode = proc.wait()
                    finally:
                        # Include workers in cleanup, also on interruption.
                        try:
                            os.killpg(proc.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        proc.wait()
                row = {"program": name, "seed": seed, "command": cmd,
                       "elapsed": round(time.monotonic() - started, 3),
                       "returncode": returncode, "log": str(dest / "run.log"),
                       "benchmark_sha256": hashlib.sha256((ROOT / spec["source"]).read_bytes()).hexdigest()}
                created = set(dest.glob("Dig_*/result")) - before
                if returncode == 0 and len(created) == 1:
                    resultfile = created.pop()
                    result = Result.load(resultfile.parent)
                    row.update(result=str(resultfile), targets=check_targets(result, spec["targets"]),
                               invariants=result.dinvs.siz,
                               status_counts=dict(Counter(str(inv.stat) for invs in result.dinvs.values()
                                                          for inv in invs)))
                    row["equalities"] = [
                        {"location": loc, "expression": str(inv), "status": str(inv.stat),
                         "degree": int(sympy.Poly(inv.inv.lhs).total_degree()),
                         "terms": len(inv.inv.lhs.as_ordered_terms())}
                        for loc, invs in result.dinvs.items() for inv in invs
                        if isinstance(inv.inv, sympy.Equality)]
                row["target_success"] = bool(row.get("targets")) and all(
                    t["outcome"] == "recovered" for t in row.get("targets", []))
                manifest["runs"].append(row)
                (out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
                print(f"{name} seed={seed}: targets={row['target_success']}, {row['elapsed']}s", flush=True)
        return int(any(not r["target_success"] for r in manifest["runs"]))


if __name__ == "__main__":
    raise SystemExit(main())
