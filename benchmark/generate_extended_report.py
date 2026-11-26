#!/usr/bin/env python3
"""
Generate markdown report from campaign_extended_111/manifest.json.
"""
from __future__ import annotations

import json
import statistics
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "src"))

import helpers.vcommon as CM
from analysis import Result, AResult

CAMPAIGN_DIR = REPO_ROOT / "benchmark/results/campaign_extended_111"
MANIFEST_FILE = CAMPAIGN_DIR / "manifest.json"
REPORT_FILE = CAMPAIGN_DIR / "CAMPAIGN_REPORT.md"

def main():
    if not MANIFEST_FILE.exists():
        print(f"Error: {MANIFEST_FILE} does not exist.")
        sys.exit(1)

    with open(MANIFEST_FILE) as f:
        manifest = json.load(f)

    runs = manifest["runs"]
    print(f"Loaded {len(runs)} run records from manifest.")

    suites = {}
    for r in runs:
        s = r["suite"].upper()
        p = r["program"]
        if s not in suites:
            suites[s] = {}
        if p not in suites[s]:
            suites[s][p] = []
        suites[s][p].append(r)

    suite_summary = []
    prog_rows = []

    overall_all_medians = []
    overall_all_totals = 0
    overall_all_succ = 0
    overall_all_timeouts = 0
    overall_all_depth = 0
    overall_all_errors = 0

    for sname, progs in suites.items():
        total_progs = len(progs)
        eval_progs = 0
        total_runs = 0
        succ_runs = 0
        timeout_runs = 0
        depth_runs = 0
        error_runs = 0
        prog_medians = []
        inv_counts_total = []

        for pname, pruns in sorted(progs.items()):
            total_runs += len(pruns)
            succs = [r for r in pruns if r["outcome"] == "success"]
            timeouts = [r for r in pruns if r["outcome"] == "timeout"]
            depths = [r for r in pruns if r["outcome"] == "depth_limit"]
            errors = [r for r in pruns if r["outcome"].startswith("error")]

            succ_runs += len(succs)
            timeout_runs += len(timeouts)
            depth_runs += len(depths)
            error_runs += len(errors)

            if succs:
                eval_progs += 1
                times = [r["elapsed_sec"] for r in succs]
                med_time = round(statistics.median(times), 2)
                prog_medians.append(med_time)

                raw_results = []
                for r in succs:
                    if r.get("result_file"):
                        rf = REPO_ROOT / r["result_file"]
                        if rf.is_file():
                            try:
                                raw_results.append(CM.vload(rf))
                            except Exception:
                                pass

                a_results = [AResult(res) for res in raw_results if hasattr(res, "dinvs")]
                for a in a_results:
                    a.analyze()

                f = statistics.median_low
                locs = f([len(a.dinvs) for a in a_results]) if a_results else 1
                V = f([a.V for a in a_results]) if a_results else 0

                inv_counts = [a.dinvs.typ_ctr for a in a_results]
                all_types = sorted({k for ctr in inv_counts for k in ctr})
                typ_medians = {t: f([ctr.get(t, 0) for ctr in inv_counts]) for t in all_types}
                tot_invs = sum(typ_medians.values())
                inv_counts_total.append(tot_invs)

                eqts = typ_medians.get("Eqt", 0)
                octs = typ_medians.get("Oct", 0)
                mmp = typ_medians.get("MMP", 0)
                congs = typ_medians.get("Congruence", 0)

                is_det = len(set(a.dinvs.siz for a in a_results)) == 1 if a_results else False
                det_mark = "✓" if is_det else "x"
                prog_rows.append({
                    "suite": sname,
                    "program": pname,
                    "runs_succ": f"{len(succs)}/{len(pruns)}",
                    "L": locs,
                    "V": V,
                    "T": tot_invs,
                    "E": eqts,
                    "I": octs,
                    "M": mmp,
                    "C": congs,
                    "med_time": f"**{med_time}**",
                    "min_max": f"{min(times)} / {max(times)}",
                    "det": det_mark
                })
            else:
                prog_rows.append({
                    "suite": sname,
                    "program": pname,
                    "runs_succ": f"0/{len(pruns)}",
                    "L": "-",
                    "V": "-",
                    "T": "**0**",
                    "E": 0,
                    "I": 0,
                    "M": 0,
                    "C": 0,
                    "med_time": "**>120s**" if timeouts else "**-**",
                    "min_max": "- / -",
                    "det": "-"
                })

        suite_med = round(statistics.median(prog_medians), 2) if prog_medians else 0.0
        overall_all_medians.extend(prog_medians)
        overall_all_totals += total_runs
        overall_all_succ += succ_runs
        overall_all_timeouts += timeout_runs
        overall_all_depth += depth_runs
        overall_all_errors += error_runs

        mean_invs = round(statistics.mean(inv_counts_total), 1) if inv_counts_total else 0.0
        suite_summary.append({
            "suite": sname,
            "eval_progs": f"{eval_progs}/{total_progs}",
            "runs": f"{succ_runs}/{total_runs}",
            "timeouts": timeout_runs,
            "depth_limits": depth_runs,
            "errors": error_runs,
            "med_time": f"**{suite_med}s**",
            "mean_invs": mean_invs
        })

    overall_med = round(statistics.median(overall_all_medians), 2) if overall_all_medians else 0.0

    lines = [
        "# Extended DIG-KN Evaluation Campaign Report (111 Programs)",
        "",
        f"**Campaign Output:** `{CAMPAIGN_DIR.relative_to(REPO_ROOT)}`  ",
        f"**Git Commit:** `{manifest.get('git_commit', 'unknown')}`  ",
        f"**Z3 Version:** `{manifest.get('z3_version', 'unknown')}`  ",
        f"**Python Version:** `{manifest.get('python_version', 'unknown')}`  ",
        f"**Per-Seed Timeout:** {manifest.get('timeout_sec', 120.0)}s | **Depth Limit:** --se_maxdepth 16 | **Parallel Workers:** {manifest.get('num_workers', 6)}  ",
        "",
        "## 1. Executive Suite Summary",
        "",
        "| Suite | Progs (Evaluated/Total) | Runs (Completed/Requested) | Timeouts | Depth Limits | Errors | Median Program Time (s) | Mean Total Invs |",
        "| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |",
    ]

    for row in suite_summary:
        lines.append(f"| **{row['suite']}** | {row['eval_progs']} | {row['runs']} | {row['timeouts']} | {row['depth_limits']} | {row['errors']} | {row['med_time']} | {row['mean_invs']} |")

    lines.append(f"| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |")
    total_eval = sum(int(r["eval_progs"].split('/')[0]) for r in suite_summary)
    total_all_progs = sum(int(r["eval_progs"].split('/')[1]) for r in suite_summary)
    lines.append(f"| **OVERALL** | **{total_eval}/{total_all_progs}** | **{overall_all_succ}/{overall_all_totals}** | **{overall_all_timeouts}** | **{overall_all_depth}** | **{overall_all_errors}** | **{overall_med}s** | **-** |")
    lines.append("")
    lines.append("## 2. Program-by-Program Breakdown")
    lines.append("")
    lines.append("| Suite | Program | Runs (Succ/Total) | $L$ | $V$ | $T$ | $E$ | $I$ | $M$ | $C$ | Med Time (s) | Min/Max (s) | Det? |")
    lines.append("| :--- | :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |")

    for row in prog_rows:
        lines.append(f"| {row['suite']} | `{row['program']}` | {row['runs_succ']} | {row['L']} | {row['V']} | **{row['T']}** | {row['E']} | {row['I']} | {row['M']} | {row['C']} | {row['med_time']} | {row['min_max']} | {row['det']} |")

    with open(REPORT_FILE, "w") as f:
        f.write("\n".join(lines) + "\n")

    print(f"Report generated at: {REPORT_FILE}")

if __name__ == "__main__":
    main()
