#!/usr/bin/env python3
"""Summarize target checks from the current implementation, across all seeds."""
from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parent.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def collect(specs, result_root):
    sources = {str(p.relative_to(ROOT)): digest(p)
               for p in (ROOT / "src").rglob("*.py")}
    rows = {}
    ignored = defaultdict(int)
    for manifest in result_root.rglob("manifest.json"):
        data = json.loads(manifest.read_text())
        for row in data.get("runs", []):
            name = row.get("program")
            if name not in specs:
                ignored["outside fixture"] += 1
                continue
            if row.get("source_sha256") != sources:
                ignored["different implementation"] += 1
                continue
            spec = specs[name]
            if row.get("benchmark_sha256") != digest(ROOT / spec["source"]):
                ignored["different benchmark"] += 1
                continue
            # Profiling is diagnostic evidence, not a validation timing run.
            if any(str(arg).endswith("dig_profile.py") for arg in row.get("command", [])):
                ignored["profiling"] += 1
                continue
            if row.get("target_success"):
                expected = {(t["location"], t["expression"]) for t in spec["targets"]}
                recovered = {(t["location"], t["expression"])
                             for t in row.get("targets", [])
                             if t["outcome"] == "recovered"}
                result = Path(row.get("result", ""))
                if expected != recovered or not result.is_file():
                    ignored["missing target evidence"] += 1
                    continue
            log = Path(row.get("log", ""))
            if not log.is_file():
                ignored["missing log"] += 1
                continue
            # Use each run's own log time, not the manifest time: appending a
            # later run must not make all earlier rows appear newly executed.
            key = (name, row["seed"])
            stamp = log.stat().st_mtime_ns
            if key not in rows or stamp > rows[key][0]:
                rows[key] = (stamp, row)
    return {key: value[1] for key, value in rows.items()}, dict(ignored)


def render(specs, rows, ignored):
    deferred = {"nla/knuth"}
    required = set(specs) - deferred
    complete = sum(all(rows.get((name, seed), {}).get("target_success", False)
                       for seed in range(7)) for name in required)
    successful = sum(row.get("target_success", False)
                     for (name, seed), row in rows.items()
                     if name in required and seed in range(7))
    lines = ["# TSE recovery validation", "",
             f"Current-source evidence: **{complete}/{len(required)} programs** pass all seven seeds; "
             f"**{successful}/{7*len(required)} required runs** pass their target checks.", "",
             "The fixture covers 91 TSE successes in the current C suites plus a Freire integer control. "
             "Knuth is deferred at the user's request and remains unresolved.", "",
             "A pass means consistent inferred output implies every listed target. "
             "It does not establish unbounded inductiveness of every emitted invariant. "
             "Process completion alone is insufficient. Results from other implementation or benchmark "
             "versions are excluded; the latest matching run for each program/seed is shown.", "",
             "| Program | Passing seeds | Status | Median successful time (s) | Evidence |",
             "| :--- | :--- | :--- | ---: | :--- |"]
    for name in sorted(specs):
        found = {seed: rows[(name, seed)] for seed in range(7) if (name, seed) in rows}
        passed = [seed for seed, row in found.items() if row.get("target_success")]
        failed = [seed for seed, row in found.items() if not row.get("target_success")]
        status = ("deferred" if name in deferred else "7/7 recovered" if len(passed) == 7
                  else "failed seeds: " + ", ".join(map(str, failed)) if failed
                  else "pending" if not found else "validation incomplete")
        timing = f"{median(found[seed]['elapsed'] for seed in passed):.3f}" if passed else "—"
        links = []
        for seed in sorted(found):
            log = Path(found[seed]["log"])
            try:
                target = log.relative_to(ROOT / "benchmark").as_posix()
            except ValueError:
                target = str(log)
            links.append(f"[{seed}]({target})")
        lines.append(f"| `{name}` | {', '.join(map(str, passed)) or '—'} | {status} | {timing} | "
                     + ", ".join(links) + " |")
    lines += ["", "Excluded historical/diagnostic rows: "
              + ", ".join(f"{reason}: {count}" for reason, count in sorted(ignored.items())) + ".", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, default=ROOT / "benchmark/results/tse_recovery")
    parser.add_argument("--out", type=Path, default=ROOT / "benchmark/TSE_RECOVERY_STATUS.md")
    args = parser.parse_args()
    specs = json.loads((ROOT / "benchmark/tse_recovery_targets.json").read_text())
    rows, ignored = collect(specs, args.results)
    args.out.write_text(render(specs, rows, ignored))
    print(args.out)


if __name__ == "__main__":
    main()
