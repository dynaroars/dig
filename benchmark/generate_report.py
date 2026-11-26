#!/usr/bin/env python3
"""
Generate a comprehensive TSE'21-style benchmark table and summary from DIG result artifacts.

Usage:
    python3 benchmark/generate_report.py [results_dir]
"""

from __future__ import annotations

import os
import sys
import statistics
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional

REPO_ROOT = Path(__file__).resolve().parent.parent
SRC_DIR = REPO_ROOT / "src"
sys.path.insert(0, str(SRC_DIR))

import helpers.vcommon as CM
from analysis import AResult, Result, Results


def determine_suite(prog_name: str) -> str:
    """Find which suite a benchmark belongs to."""
    for s in ["nla", "NLA-mosaic", "complexity", "hola"]:
        p = REPO_ROOT / "benchmark" / "c" / s / f"{prog_name}.c"
        if p.exists() or (REPO_ROOT / "benchmark" / "c" / s / f"{prog_name}.dig.c").exists():
            return s
    return "other"


def generate_report(results_dir: Path) -> str:
    assert results_dir.is_dir(), f"{results_dir} is not a directory"

    bench_dirs = sorted([d for d in results_dir.iterdir() if d.is_dir() and not d.name.startswith((".", "logs"))])

    prog_data = []

    for bmdir in bench_dirs:
        run_dirs = sorted([
            d for d in bmdir.iterdir()
            if d.is_dir() and (d / Result.resultfile).is_file()
        ])
        if not run_dirs:
            continue

        raw_results = [CM.vload(d / Result.resultfile) for d in run_dirs]
        a_results = [AResult(r) for r in raw_results if r.dinvs.siz or hasattr(r, "dinvs")]
        if not a_results:
            continue

        prog_name = bmdir.name
        suite = determine_suite(prog_name)

        # Compute stats using DIG's analysis engine
        for r in a_results:
            r.analyze()

        nruns = len(a_results)
        f = statistics.median_low

        locs = f([len(r.dinvs) for r in a_results])
        V = f([r.V for r in a_results])
        T = f([r.T for r in a_results])
        D = f([r.D for r in a_results])
        NL = f([r.NL for r in a_results])

        times = [r.time_d.get("total", 0.0) for r in a_results]
        med_time = round(statistics.median(times), 2)
        min_time = round(min(times), 2)
        max_time = round(max(times), 2)
        avg_time = round(statistics.mean(times), 2)

        # Invariant type breakdowns
        inv_counts_list = [r.dinvs.typ_ctr for r in a_results]
        all_types = sorted({k for ctr in inv_counts_list for k in ctr})
        typ_medians = {t: f([ctr.get(t, 0) for ctr in inv_counts_list]) for t in all_types}
        total_invs = sum(typ_medians.values())

        # Check determinism: did all runs find the exact same number of invariants?
        is_det = len(set(r.dinvs.siz for r in a_results)) == 1

        prog_data.append({
            "suite": suite,
            "name": prog_name,
            "runs": nruns,
            "locs": locs,
            "V": V,
            "D": D,
            "NL": NL,
            "total_invs": total_invs,
            "eqts": typ_medians.get("Eqt", 0),
            "octs": typ_medians.get("Oct", 0),
            "mmp": typ_medians.get("MMP", 0),
            "cong": typ_medians.get("Congruence", 0),
            "med_time": med_time,
            "min_time": min_time,
            "max_time": max_time,
            "avg_time": avg_time,
            "is_det": is_det,
        })

    # Build Markdown document
    lines = [
        "# DIG2 Benchmark Evaluation Report (TSE'21 Comparison Format)",
        "",
        f"**Results Directory:** `{results_dir.resolve()}`  ",
        f"**Total Evaluated Programs:** {len(prog_data)}",
        "",
        "> **Note:** All reported times are median wall-clock seconds across the 7 runs.",
        "",
        "---",
        "",
        "## 1. Executive Summary Table",
        "",
        "| Suite | # Programs | Completed Runs | Median Total Invs | Avg Equalities ($E$) | Avg Inequalities ($I$) | Time (s) |",
        "| :--- | :---: | :---: | :---: | :---: | :---: | :---: |",
    ]

    suites = sorted({p["suite"] for p in prog_data})
    for st in suites:
        st_items = [p for p in prog_data if p["suite"] == st]
        n_progs = len(st_items)
        tot_runs = sum(p["runs"] for p in st_items)
        med_invs = statistics.median([p["total_invs"] for p in st_items]) if st_items else 0
        avg_e = round(statistics.mean([p["eqts"] for p in st_items]), 1) if st_items else 0
        avg_i = round(statistics.mean([p["octs"] for p in st_items]), 1) if st_items else 0
        med_t = round(statistics.median([p["med_time"] for p in st_items]), 2) if st_items else 0
        lines.append(f"| **{st.upper()}** | {n_progs} | {tot_runs} | {med_invs} | {avg_e} | {avg_i} | **{med_t}s** |")

    all_times = [p["med_time"] for p in prog_data]
    overall_med_t = round(statistics.median(all_times), 2) if all_times else 0
    lines.extend([
        "| :--- | :---: | :---: | :---: | :---: | :---: | :---: |",
        f"| **OVERALL** | **{len(prog_data)}** | **{sum(p['runs'] for p in prog_data)}** | **-** | **-** | **-** | **{overall_med_t}s** |",
        "",
        "---",
        "",
        "## 2. Detailed Program-by-Program Benchmark Table",
        "",
        "| Suite | Program | $L$ (locs) | $V$ (vars) | $T$ (invs) | Equalities ($E$) | Inequalities ($I$) | Min/Max ($M$) | Congruences ($C$) | $NL(d)$ | Time (s) | Min/Max (s) | Det? |",
        "| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |",
    ])

    for p in prog_data:
        det_str = "✓" if p["is_det"] else "x"
        nl_str = f"{p['NL']} (deg {p['D']})" if p['NL'] > 0 else "-"
        lines.append(
            f"| {p['suite'].upper()} | `{p['name']}` | {p['locs']} | {p['V']} | **{p['total_invs']}** | "
            f"{p['eqts']} | {p['octs']} | {p['mmp']} | {p['cong']} | {nl_str} | **{p['med_time']}s** | "
            f"{p['min_time']}s / {p['max_time']}s | {det_str} |"
        )

    lines.append("")
    report_text = "\n".join(lines)

    report_file = results_dir / "REPORT.md"
    report_file.write_text(report_text)
    return report_text


if __name__ == "__main__":
    target_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("benchmark/results/sample_run")
    print(generate_report(target_dir))
