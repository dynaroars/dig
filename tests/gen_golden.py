"""
Generate tests/golden.json by running DIG on every benchmark a few times.

For each program:
  - status: "ok" if any run produced invariants, else "timeout"/"fail";
  - eqts:   equalities found in *every* ok run (intersection), so flaky ones
            that only show up sometimes are not baked into the golden;
  - min_invs: the smallest invariant count across ok runs (the regression
              floor for the wobblier invariant types).

Usage:
    python tests/gen_golden.py [runs] [--only nla|complexity|hola] [--timeout N]
"""
import json
import sys
from pathlib import Path

from dig_harness import programs, prog_id, run_dig


def main(argv: list[str]) -> None:
    runs = 2
    only = None
    timeout = 180
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--only":
            only = argv[i + 1]; i += 2
        elif a == "--timeout":
            timeout = int(argv[i + 1]); i += 2
        else:
            runs = int(a); i += 1

    golden_path = Path(__file__).parent / "golden.json"
    golden = json.loads(golden_path.read_text()) if golden_path.exists() else {}

    for cfile in programs():
        pid = prog_id(cfile)
        if only and not pid.startswith(f"{only}/"):
            continue
        results = [run_dig(cfile, timeout=timeout) for _ in range(runs)]
        ok = [r for r in results if r["status"] == "ok"]
        if ok:
            status = "ok"
            eqts = sorted(set.intersection(*[set(r["eqts"]) for r in ok]))
            min_invs = min(r["n_invs"] for r in ok)
        else:
            status = "timeout" if any(
                r["status"] == "timeout" for r in results) else "fail"
            eqts, min_invs = [], 0
        golden[pid] = {"status": status, "eqts": eqts, "min_invs": min_invs}
        print(f"{pid}: {status} eqts={len(eqts)} min_invs={min_invs}", flush=True)
        golden_path.write_text(json.dumps(golden, indent=2, sort_keys=True))

    print(f"wrote {golden_path}")


if __name__ == "__main__":
    main(sys.argv[1:])
