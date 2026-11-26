#!/usr/bin/env python3
"""
Generate comprehensive campaign report and LaTeX table data from isolated campaign run.
Usage:
    python3 benchmark/generate_campaign_report.py [campaign_dir]
"""
from __future__ import annotations

import json
import os
import statistics
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List

REPO_ROOT = Path(__file__).resolve().parent.parent
SRC_DIR = REPO_ROOT / "src"
sys.path.insert(0, str(SRC_DIR))

import helpers.vcommon as CM
from analysis import AResult, Result

def generate_report(campaign_dir: Path):
    manifest_path = campaign_dir / "manifest.json"
    assert manifest_path.is_file(), f"Missing {manifest_path}"

    with open(manifest_path, "r", encoding="utf-8") as mf:
        manifest = json.load(mf)

    metadata = manifest["metadata"]
    runs = manifest["runs"]

    # Group runs by suite and program
    by_prog = defaultdict(list)
    for r in runs:
        key = (r["suite"], r["program"], r["stem"])
        by_prog[key].append(r)

    suite_stats = defaultdict(lambda: {
        "total_progs": 0,
        "completed_progs": 0,
        "total_runs": 0,
        "success_runs": 0,
        "timeout_runs": 0,
        "depth_runs": 0,
        "error_runs": 0,
        "runtimes": [],
        "med_runtimes_per_prog": [],
        "total_invs": [],
        "eqts": [],
        "octs": [],
        "mmp": [],
        "congs": [],
    })

    prog_summaries = []

    for (suite, prog, stem), pruns in sorted(by_prog.items()):
        suite_stats[suite]["total_progs"] += 1
        suite_stats[suite]["total_runs"] += len(pruns)

        succ_runs = [r for r in pruns if r["outcome"] == "success"]
        timeout_runs = [r for r in pruns if r["outcome"] == "timeout"]
        depth_runs = [r for r in pruns if r["outcome"] == "depth_limit"]
        err_runs = [r for r in pruns if r["outcome"] not in ("success", "timeout", "depth_limit")]

        suite_stats[suite]["success_runs"] += len(succ_runs)
        suite_stats[suite]["timeout_runs"] += len(timeout_runs)
        suite_stats[suite]["depth_runs"] += len(depth_runs)
        suite_stats[suite]["error_runs"] += len(err_runs)

        if succ_runs:
            suite_stats[suite]["completed_progs"] += 1
            raw_results = []
            for r in succ_runs:
                rf = REPO_ROOT / r["result_path"]
                if rf.is_file():
                    raw_results.append(CM.vload(rf))

            a_results = [AResult(res) for res in raw_results if res.dinvs.siz or hasattr(res, "dinvs")]
            for a in a_results:
                a.analyze()

            f = statistics.median_low
            locs = f([len(a.dinvs) for a in a_results]) if a_results else 1
            V = f([a.V for a in a_results]) if a_results else 0
            
            times = [r["elapsed_sec"] for r in succ_runs]
            med_time = round(statistics.median(times), 2)
            suite_stats[suite]["runtimes"].extend(times)
            suite_stats[suite]["med_runtimes_per_prog"].append(med_time)

            inv_counts = [a.dinvs.typ_ctr for a in a_results]
            all_types = sorted({k for ctr in inv_counts for k in ctr})
            typ_medians = {t: f([ctr.get(t, 0) for ctr in inv_counts]) for t in all_types}
            tot_invs = sum(typ_medians.values())

            eqts = typ_medians.get("Eqt", 0)
            octs = typ_medians.get("Oct", 0)
            mmp = typ_medians.get("MMP", 0)
            congs = typ_medians.get("Congruence", 0)

            suite_stats[suite]["total_invs"].append(tot_invs)
            suite_stats[suite]["eqts"].append(eqts)
            suite_stats[suite]["octs"].append(octs)
            suite_stats[suite]["mmp"].append(mmp)
            suite_stats[suite]["congs"].append(congs)

            is_det = len(set(a.dinvs.siz for a in a_results)) == 1 if a_results else False

            prog_summaries.append({
                "suite": suite,
                "program": prog,
                "stem": stem,
                "total_runs": len(pruns),
                "succ_runs": len(succ_runs),
                "timeout_runs": len(timeout_runs),
                "depth_runs": len(depth_runs),
                "locs": locs,
                "vars": V,
                "total_invs": tot_invs,
                "eqts": eqts,
                "octs": octs,
                "mmp": mmp,
                "congs": congs,
                "med_time": med_time,
                "min_time": round(min(times), 2),
                "max_time": round(max(times), 2),
                "det": is_det
            })
        else:
            prog_summaries.append({
                "suite": suite,
                "program": prog,
                "stem": stem,
                "total_runs": len(pruns),
                "succ_runs": 0,
                "timeout_runs": len(timeout_runs),
                "depth_runs": len(depth_runs),
                "locs": "-",
                "vars": "-",
                "total_invs": 0,
                "eqts": 0,
                "octs": 0,
                "mmp": 0,
                "congs": 0,
                "med_time": ">45s" if timeout_runs else "-",
                "min_time": "-",
                "max_time": "-",
                "det": "-"
            })

    # Generate Markdown Summary
    report_lines = []
    report_lines.append(f"# Full Isolated DIG-KN Evaluation Campaign Report (791 Runs)\n")
    report_lines.append(f"**Campaign Output:** `{campaign_dir.relative_to(REPO_ROOT)}`  ")
    report_lines.append(f"**Git Commit:** `{metadata.get('git_commit', 'unknown')}`  ")
    report_lines.append(f"**Z3 Version:** `{metadata.get('z3_version', 'unknown')}`  ")
    report_lines.append(f"**Python Version:** `{metadata.get('python_version', '').split()[0]}`  ")
    report_lines.append(f"**Per-Seed Timeout:** {metadata.get('timeout_per_seed_sec')}s | **Parallel Workers:** {metadata.get('parallel_workers')}  \n")

    report_lines.append(f"## 1. Executive Suite Summary\n")
    report_lines.append(f"| Suite | Progs (Evaluated/Total) | Runs (Completed/Requested) | Timeouts | Depth Limits | Errors | Median Program Time (s) | Mean Total Invs |")
    report_lines.append(f"| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |")

    all_med_times = []
    tot_eval_progs = 0
    tot_all_progs = 0
    tot_succ_runs = 0
    tot_all_runs = 0
    tot_to_runs = 0
    tot_dp_runs = 0
    tot_err_runs = 0

    for s, st in sorted(suite_stats.items()):
        med_t = round(statistics.median(st["med_runtimes_per_prog"]), 2) if st["med_runtimes_per_prog"] else "-"
        avg_inv = round(statistics.mean(st["total_invs"]), 1) if st["total_invs"] else "-"
        report_lines.append(f"| **{s.upper()}** | {st['completed_progs']}/{st['total_progs']} | {st['success_runs']}/{st['total_runs']} | {st['timeout_runs']} | {st['depth_runs']} | {st['error_runs']} | **{med_t}s** | {avg_inv} |")
        if st["med_runtimes_per_prog"]:
            all_med_times.extend(st["med_runtimes_per_prog"])
        tot_eval_progs += st["completed_progs"]
        tot_all_progs += st["total_progs"]
        tot_succ_runs += st["success_runs"]
        tot_all_runs += st["total_runs"]
        tot_to_runs += st["timeout_runs"]
        tot_dp_runs += st["depth_runs"]
        tot_err_runs += st["error_runs"]

    tot_med_t = round(statistics.median(all_med_times), 2) if all_med_times else "-"
    report_lines.append(f"| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |")
    report_lines.append(f"| **OVERALL** | **{tot_eval_progs}/{tot_all_progs}** | **{tot_succ_runs}/{tot_all_runs}** | **{tot_to_runs}** | **{tot_dp_runs}** | **{tot_err_runs}** | **{tot_med_t}s** | **-** |\n")

    report_lines.append(f"## 2. Program-by-Program Breakdown\n")
    report_lines.append(f"| Suite | Program | Runs (Succ/Total) | $L$ | $V$ | $T$ | $E$ | $I$ | $M$ | $C$ | Med Time (s) | Min/Max (s) | Det? |")
    report_lines.append(f"| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |")

    for p in prog_summaries:
        runs_str = f"{p['succ_runs']}/{p['total_runs']}"
        det_str = "✓" if p['det'] is True else ("x" if p['det'] is False else "-")
        report_lines.append(f"| {p['suite'].upper()} | `{p['stem']}` | {runs_str} | {p['locs']} | {p['vars']} | **{p['total_invs']}** | {p['eqts']} | {p['octs']} | {p['mmp']} | {p['congs']} | **{p['med_time']}** | {p['min_time']} / {p['max_time']} | {det_str} |")

    report_content = "\n".join(report_lines)
    report_path = campaign_dir / "CAMPAIGN_REPORT.md"
    with open(report_path, "w", encoding="utf-8") as rf:
        rf.write(report_content)

    print(f"Report generated at {report_path}")
    return report_content

if __name__ == "__main__":
    cdir = Path(sys.argv[1]) if len(sys.argv) > 1 else (REPO_ROOT / "benchmark/results/campaign_full_791")
    generate_report(cdir)
