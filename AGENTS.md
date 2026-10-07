# Repository agent instructions

## Benchmark execution

- Run DIG benchmarks strictly one at a time. Never run multiple `dig.py`
  benchmark invocations concurrently, including different programs or seeds.
- Each individual run may use all available threads and internal multiprocessing.
  Keep DIG's internal parallelism enabled; serialization applies to separate
  benchmark invocations.
- Wait for a run and its worker processes to finish, or terminate and reap them,
  before starting the next run. Coordinate with any other agents or sessions
  using this workspace so their benchmark runs do not overlap.
- Before using a campaign runner, ensure its outer benchmark concurrency is one
  (`--jobs 1`, `max_workers = 1`, or the equivalent). Several existing runners
  launch multiple DIG processes by default; do not use those defaults.

This is an explicit user requirement recorded on 2026-10-06. It applies to all
benchmark experiments, reruns, diagnostics, and campaigns in this repository.

## TSE recovery priorities

- The user asked to recover the benchmarks solved in the TSE paper.
- Defer further Knuth optimization for now: the user explicitly asked not to
  spend excessive effort on it. Preserve its unresolved result and profiling
  evidence; prioritize the remaining programs and validation across seeds.

## Recording invariant results

- Do not require recovered equations to look exactly like the TSE equations.
  Different polynomial bases or equivalent/stronger equalities are acceptable.
- Preserve interesting nonlinear and high-degree equalities per program, with
  their trace locations, degrees, seeds, settings, and validation evidence.
  The user considers complicated high-degree equalities useful candidates even
  when they differ from the historical formulas; retain them for review rather
  than discarding them solely because a reference target was not recovered.
- Keep candidate discovery separate from confirmed target recovery. Degree and
  complexity are useful signals, while semantic target checks provide stronger
  evidence. Do not automatically overwrite the golden baseline with new output.
