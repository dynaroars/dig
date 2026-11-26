#!/usr/bin/env python3
"""Catalog actual polynomial equalities from saved TSE runs; never launch DIG."""
from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import sys

from generate_tse_recovery_report import ROOT, collect

sys.path.insert(0, str(ROOT / "src"))
import sympy
from analysis import Result


def catalog(specs, rows):
    programs = {}
    for name, spec in sorted(specs.items()):
        runs = []
        for (program, seed), row in sorted(rows.items()):
            if program != name:
                continue
            equations = []
            resultfile = Path(row.get("result") or "")
            if resultfile.is_file():
                result = Result.load(resultfile.parent)
                for location, invs in sorted(result.dinvs.items()):
                    for inv in sorted(invs, key=str):
                        if not isinstance(inv.inv, sympy.Equality):
                            continue
                        expression = sympy.expand(inv.inv.lhs - inv.inv.rhs)
                        symbols = sorted(expression.free_symbols, key=str)
                        poly = sympy.Poly(expression, *symbols) if symbols else None
                        equations.append({
                            "location": location,
                            "equation": f"{expression} = 0",
                            "degree": int(poly.total_degree()) if poly else 0,
                            "monomials": len(poly.terms()) if poly else 1,
                            "variables": list(map(str, symbols)),
                            "dig_status": str(inv.stat),
                        })
            runs.append({key: row.get(key) for key in (
                "seed", "elapsed", "command", "log", "result", "targets",
                "target_success", "source_sha256", "benchmark_sha256")}
                | {"equalities": equations})
        programs[name] = {"source": spec["source"], "targets": spec["targets"],
                          "runs": runs}
    return {"description": "Observed polynomial equalities, not an exact-string golden baseline. "
            "DIG status is the saved checker status, not an unbounded inductiveness certificate.",
            "programs": programs}


def render(data):
    lines = ["# TSE inferred equality catalog", "",
             "Actual equations from saved current-source runs, grouped by program and trace location. "
             "Different bases are retained; no exact match to a historical formula is required. "
             "Degree and monomial count help identify interesting candidates. "
             "Target success is checked separately by semantic implication.", "",
             "This is an observational record, not an automatically accepted golden baseline. "
             "The companion JSON preserves every run's equations, DIG status, command, targets, "
             "source hashes, timing, and evidence paths. Regenerate with "
             "`/usr/bin/python3 benchmark/catalog_tse_invariants.py`; this reads saved results only.", ""]
    for name, program in data["programs"].items():
        lines.extend([f"## {name}", ""])
        runs = program["runs"]
        if not runs:
            lines.extend(["No current-source results recorded (Knuth is deferred).", ""])
            continue
        passed = [str(run["seed"]) for run in runs if run["target_success"]]
        lines.extend([f"Recorded seeds: {', '.join(str(r['seed']) for r in runs)}. "
                      f"Target-confirmed seeds: {', '.join(passed) or 'none'}.", ""])
        grouped = defaultdict(list)
        for run in runs:
            for eq in run["equalities"]:
                grouped[(eq["location"], eq["equation"], eq["degree"], eq["monomials"])].append(run["seed"])
        if grouped:
            lines.extend(["| Location | Degree | Monomials | Equation | Seeds |",
                          "| :--- | ---: | ---: | :--- | :--- |"])
            for (loc, eq, degree, terms), seeds in sorted(grouped.items()):
                lines.append(f"| {loc} | {degree} | {terms} | `{eq}` | "
                             f"{', '.join(map(str, seeds))} |")
        else:
            lines.append("No polynomial equalities emitted; see saved output for other invariant types.")
        lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, default=ROOT / "benchmark/results/tse_recovery")
    parser.add_argument("--out", type=Path, default=ROOT / "benchmark/TSE_RECOVERY_INVARIANTS")
    args = parser.parse_args()
    specs = json.loads((ROOT / "benchmark/tse_recovery_targets.json").read_text())
    rows, _ = collect(specs, args.results)
    data = catalog(specs, rows)
    args.out.with_suffix(".json").write_text(json.dumps(data, indent=2) + "\n")
    args.out.with_suffix(".md").write_text(render(data))
    print(args.out.with_suffix(".md"))


if __name__ == "__main__":
    main()
