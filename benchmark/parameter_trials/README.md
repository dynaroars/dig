# Limited parameter experiment evidence

`results.json` preserves the 22 manifests (170 runs), settings, source and benchmark
hashes, semantic target outcomes and recovered equalities. Equalities are retained
with their locations, degree, term count and validation status; no golden baseline
is overwritten. Absolute log/result paths refer to local raw artifacts.

Named `.patch` files record each trial relative to the frozen pre-experiment source
snapshot (`b84f002`, a local-only baseline commit). They are archival experiment
changes, not patches to apply blindly to the final published source. The baseline
contains numerical recovery work that predates these trials. Rejected sampling,
bound and sample-size policies are not active in the final source.

`final.patch` records accepted numerical parameter changes relative to that
snapshot; it excludes unrelated API-axiom files and the CLI file. The CLI's small
positive-argument validation addition is captured by `correctness.patch` and the
published commit. `published_source_sha256` identifies the final published Python
source; manifests identify the exact source used for each historical run.

See [the trial report](../../docs/benchmarks/PARAMETER_TRIALS.md) for decisions,
comparison limitations and the limited serial runner.
