# Paper audit — 2026-10-06

Audited `paper.tex` using `handsoff.md` → `handoff.md`, the saved benchmark artifacts, current implementation, and the locally supplied TSE'21 PDF. The handoff is a checklist, not independent evidence of experimental correctness. **The paper currently has submission-blocking evaluation and soundness discrepancies.** No paper or implementation source was edited.

## 1. Critical: Table 2 reports full coverage using partial-campaign timings

Locations: `paper.tex:354–410`, especially the setup at 374–389 and the 100% solved claims at 405–415.

Independently loaded every `benchmark/results/sample_run/*/*/result` and recomputed timing medians; also ran `benchmark/generate_report.py`.

| Suite | Programs claimed | Programs with saved results | Saved runs | Programs with 7 runs | Median of available per-program medians |
|---|---:|---:|---:|---:|---:|
| NLA | 33 | 21 | 143 | 19 | 10.90 s |
| NLA-mosaic | 14 | 10 | 47 | 3 | 12.97 s |
| Complexity | 20 | 14 | 97 | 13 | 11.95 s |
| HOLA | 46 | 7 | 49 | 7 | 3.69 s |
| Overall | 113 | **52** | **336** | **42** | **9.45 s** |

These are exactly Table 2's new-tool timings, but they describe the available subsets, not the claimed 113-program completed evaluation. A full 113 × 7 campaign requires 791 runs. Presence of a serialized result does not establish target recovery or an inductive proof.

Incomplete repetitions: `dijkstra` 4, `freire1` 6; `binomial` 3, `chebyshev` 5, `chebyshev_pair` 6, `continued_fraction_sign` 6, `nagata` 1, `pell` 1, `welford` 4; `popl09_fig4_1` 6. Thus even some Appendix A rows are single-run measurements despite the seven-run caption.

Missing results:

- NLA: `cohencu`, `egcd2`, `egcd3`, `fermat1`, `fermat2`, `geo3`, `knuth`, `lcm1`, `lcm2`, `prod4br`, `prodbin`, `wensley`.
- NLA-mosaic: `berggren`, `continued_fraction`, `fibonacci_trace`, `symplectic_euler`.
- Complexity: `cav09_fig1a`, `cav09_fig1d`, `pldi09_fig1`, `pldi09_fig2`, `pldi09_fig4_4`, `popl09_fig4_2`.
- HOLA: only `01`, `02`, `03`, `07`, `08`, `15`, `20` have results; the other 39 do not.

The separate `benchmark_results_20261006_141538.json` contains two `cav09_fig1a` runs (median 2.847 s), but reports zero invariants and is not the dataset behind Table 2. It does not substantiate that case study's 1.25 s result.

Required correction: report available coverage and missing outcomes explicitly, or finish a recorded campaign. Define “solved” in terms of ground-truth recovery/proof; do not infer it from a successful process or nonempty output. Include timeout/error cases in the evaluation denominator.

## 2. Critical: full ground-truth recovery is contradicted by the saved outputs

Locations: `paper.tex:395–420`, Appendix A at 609–617.

The paper claims all ground-truth invariants are synthesized and proved. However:

- `pell` has only two octagons, no equality `x² − 2y² = 1`.
- `markov` has only five octagons, no Markov cubic equality.
- `chebyshev` has two octagons and three min/max relations, no conserved polynomial equality.
- `chebyshev_pair`, `nagata`, and `welford` also have no equalities in this campaign.

Appendix A itself lists E=0 for Pell, Chebyshev, and Welford. It therefore conflicts with the main text's recovery claim.

Separate mosaic experiments are not substitutes for the default campaign: `benchmark/c/NLA-mosaic/results/baseline/RESULTS.md` uses explicit degree caps and selected domains; `tuned/RESULTS.md` additionally enables Kapur. Both explicitly distinguish equality recovery from unbounded proof, and contain missing targets/timeouts.

Required correction: produce a program/target/recovered/proved matrix and distinguish these settings. Revise the blanket 100% claim to match that matrix.

## 3. Critical: ordinary inference does not inductively verify the whole output

Locations: `paper.tex:100`, `230`, `388`, `439–446`.

The default pipeline in `src/alg.py:168–206` merges dynamic, trace-based, recurrence, and optional Kapur results, then sanitizes and saves. It has no final Houdini pass over the union of numerical domains.

`src/data/symstates.py:150–213` labels an invariant `PROVED` after successful **bounded symbolic-state checking**. `mcheck_depth` checks collected unroll depths; this is not unbounded induction. Recurrence/Kapur have separate inductive checks, but their existence does not make all dynamic equalities, octagons, min/max relations, or congruences inductively proved.

Across all saved runs, 1,777 invariant occurrences have status `p` and 490 have status `None`. The `p` status does not identify which proof mechanism was used. For example, `cohendiv` includes congruences with status `None`. `InvStat` has `p/d/u`, not distinct “bounded checked” and “inductively proved” states. The CLI sample also omits the claimed proof/candidate classifications.

Required correction: either document the actual bounded/trace/inductive distinctions or implement and record a sound final proof stage. The current result records do not support counting every reported invariant as inductively proved.

## 4. Critical: reproduced false induction result with a nested loop

Locations: `paper.tex:100`, `227–261`; implementation `src/data/symex_c.py:462–535`, `1698–1739`.

The induction API documents that nested bodies are explored only to `max_depth`. I independently reproduced a false `valid` result:

```python
from pathlib import Path
from data.symex_c import CSymEx

p = Path('/tmp/dig-audit-nested.c')
p.write_text('int mainQ(){int x=0; while(x<2){int y=0;'
             'while(y<20){y++;} x++;}return 0;}')
e = CSymEx(p, max_depth=3)
print(e.prove_inductive(e.parse_c_expr('x == 0'), loop=0))
# Actual output: ('valid', None)
```

Run with `PYTHONPATH=src` from the repository root. In the real execution, the inner loop finishes, `x` becomes 1, and the next outer head violates `x == 0`. The bounded inner exploration loses the continuation; checking the empty post-state set succeeds vacuously. The same pattern must be accounted for in Houdini and other proof APIs that execute nested bodies. `_exec_while` also caps the state list, so proof completeness of path exploration needs explicit handling.

The same reproduction keeps the false invariant in Houdini at depth 3. As a control, depth 25 returns `step-violated` and Houdini drops it, confirming that the result depends on the inner-loop cutoff.

Required correction: propagate incomplete exploration as `unknown`, or use sound loop summaries/overapproximations. Restrict soundness statements until this is addressed. This reproduction is an implementation failure, not merely a wording issue.

## 5. High: runtime prose disagrees with Table 2

Locations: `paper.tex:417–420`.

| Suite | Table 2 / available artifacts | Prose |
|---|---:|---:|
| NLA | 10.90 | 20.91 |
| NLA-mosaic | 12.97 | 6.84 |
| Complexity | 11.95 | 1.78 |
| HOLA | 3.69 | 4.69 |

20.91, 1.78, and 4.69 are individual-program medians (`cohendiv`, `pldi09_fig4_1`, `01.dig`), not suite medians. Claimed speedups are calculated from the conflicting prose values. Fix coverage and baseline comparability before computing replacement speedups.

## 6. High: TSE'21 comparison is not supported as presented

Locations: `paper.tex:399–420`; source `paper/nguyen2021using.pdf`, evaluation Tables 1, 2, 4 and setup.

The supplied prior paper reports five runs on a 64-core AMD 4 GHz machine with 64 GB RAM, not the new paper's seven-run Intel setup. Its NLA and Complexity suites contain 28 and 19 programs, respectively. Aggregating its displayed per-program total runtimes gives:

| Prior suite | Rows | Median | Mean | New paper's attributed TSE'21 value |
|---|---:|---:|---:|---:|
| NLA | 28 | 66.70 | 88.125 | 73.1 |
| Complexity | 19 | 18.10 | 30.8421 | 14.8 |
| HOLA | 46 | 6.70 | 23.20 | 29.4 |

The attributed suite values do not match these aggregates; their provenance is absent. The overall 38.2 s value also needs a defined dataset and aggregation. Historical measurements on different hardware and unequal benchmark subsets cannot establish the claimed controlled speedups. Supply rerun evidence or label a sourced historical comparison and its limits.

## 7. High: complexity examples describe different algorithms/results

Locations: `paper.tex:489–511`.

- `popl09_fig2_2` has one loop with increments of `x` or `z`, three inputs `(a,b,n)`, and no `m`. It is not nested dynamic resets establishing a product bound. The saved cubic factors as `t*(a-n+t)*(a+b-2*n+t)`, yielding roots 0, `n-a`, and `2*n-a-b`. Its median is **17.05 s**, versus **1.82 s** in Table 4.
- `pldi09_fig4_1` has inputs `(id,n)` and cyclic index traversal. Its saved equality is `tCtr=n+1`. The text instead describes two bound inputs `(n,m)` and `t ≤ max(n,m)`.
- `popl09_fig2_1` has no resets: it increments `y` to `m`, then `x` to `n`. Its cubic factors as `t*(a-n+t)*(a+b-m-n+t)`. One root is `n+m-a-b`, but the equality alone is a disjunction of three roots; the paper should state the branch preconditions before presenting an exact formula.
- No supporting sample-run record establishes Table 4's `cav09_fig1a` 1.25 s value.

## 8. High: worked Houdini example gives the wrong reason for non-inductiveness

Locations: `paper.tex:172`, `245`, `445`.

The illustrated inner doubling loop changes only `a,b`, so `q*y+r-x=0` is preserved without any remainder sign condition. For the outer update `q'=q+a`, `r'=r-b`, the equality changes by `a*y-b`; that companion equality is sufficient for preservation regardless of signs. I checked both algebraic preservation obligations with Z3 (`unsat` counterexample queries). Negative `r` is not the stated explanation. Also, `a*y-b=0` is an equality, not an octagonal bound.

Required correction: explain dependence on `a*y=b` for the outer transition or choose an invariant that actually needs the stated bounds. Give a recorded proof experiment for the <0.05 s claim.

## 9. High: degree-estimation claims differ from implementation

Locations: `paper.tex:191–200`, `429–437`; implementation `src/alg.py:408–455`, `src/infer/eqt.py:79–104`.

- The actual schedule starts with degree 2 and the monomial-budget ceiling, adding an estimated intermediate degree. It does not allocate a degree-1, three-term template as claimed for linear examples.
- It stops searching a location once **any** equalities are found. This does not guarantee recovery of every higher-degree relation.
- Finite samples cannot certify the exact global growth order, and growth degree in the iteration count is not a completeness guarantee for multivariate invariant degree.
- For V=3, 120 monomials corresponds to d=7, while the current MAX_TERM=200 permits d=8 (165 monomials). The hypothetical baseline degree needs to be stated consistently.
- `cohencu` has no sample-run results supporting its specific synthesis claim; its cited `z-3*y²-3*y-1` equality is quadratic even if another relation/growth sequence requires a cubic search.

Required correction: describe the estimator as a heuristic search hint and report the actual search schedule, baseline, and measured cost separately.

## 10. High: Appendix B describes a different static algorithm

Locations: `paper.tex:660–681`; implementation `src/infer/kapur.py:91–175`.

The paper derives a coefficient system from the identity `p(T(x))-p(x) ≡ 0`. The implementation instead evaluates monomials along a finite **symbolic orbit from initialization**, forms parameter-coefficient rows, solves their null space, and filters candidates with Houdini. Rewrite the algorithm to match this implementation.

The transition identity is also stronger than inductive preservation of the zero set. For example, `x'=2*x`, initialized at zero, preserves `x=0`, but `p=x` does not satisfy `p(T)-p ≡ 0`. Therefore the text's “all invariant polynomials” characterization is false for its stated system. Its `I_0` notation also mixes a state variety and an ideal of polynomials.

## 11. High: experimental claims lack supporting datasets

Locations: `paper.tex:451–469`, `517–522`, `679–681`, `720–725`.

I found no identified nine-program ablation dataset/configuration/results substantiating Table 3's five means, nor neural experiment records substantiating <0.25 s/candidate and 100% proof precision. “Solved” is undefined, especially when nonlinear equalities are removed yet all cases remain solved. The LLM model/version, prompts, benchmark selection, number of proposals, accepted/rejected/unknown counts, and proof statuses are not reported.

Individual termination/static/Symba timing claims also need linked measurements. Appendix C's “Automatic Routing” is not implemented in the default path: DO_SYMBA=False, and selection is opt-in. Recurrence inference and its multipath extension are enabled by default (`src/settings.py:20–25`, `src/alg.py:315–350`) but omitted from the evaluation's default-engine description.

## 12. Medium: reproducibility and semantic scope need correction

Locations: `paper.tex:155`, `332`, `374–389`.

- The campaign scripts `run_all_nla_complexity.py:90` and `run_nla_mosaic.py:76` use 45 s timeouts, not the stated 300 s. Identify the actual commands/configuration behind the saved dataset. Their output calls a completed subprocess “OK” even for nonzero exit codes.
- The report generator unconditionally says “seven runs” despite loading variable repetition counts and computes medians only over saved results. It should expose missing/error runs and report actual sample sizes. It computes independent median category counts, which need not describe one actual run.
- Several counts vary across distinct seeds (e.g., `cohendiv`: 24 versus 26). This does not disprove same-seed reproducibility, but neither does equal invariant count prove identical outputs. A fixed-seed repeated-run comparison is needed for the 100% claim. A 5 s wall-clock Gröbner timeout remains enabled, qualifying claims that timing never affects output.
- Arithmetic uses mathematical Z3 integers/reals; `double` is modeled as Real, and overflow checking is opt-in. State this scope. Welford's benchmark header explicitly warns that its equalities are exact-real identities and C doubles can have rounding residuals.
- `--prove`, `--nonterm`, and ranking/Houdini options are exposed by `data.symex_c`, not the main `dig.py` parser. Show the actual command/module for these features and avoid implying automatic final-proof integration.
- Dynamic Gröbner reduction uses SymPy's default order (`src/helpers/miscs.py:363,371`), not the grevlex order claimed at `paper.tex:185`.

## 13. High: the CLI figure contains a false invariant

Location: `paper.tex:326`, Figure 2.

The displayed inner-head congruence `q*r === 0 (mod 8)` is false for the supplied benchmark. With permitted input `x=7, y=2`, the first outer subtraction leaves `q=2, r=3`; the next inner head has `a=1, b=2`. Thus `q*r=6`, which is not divisible by 8. I reproduced these values by executing the benchmark's integer updates. Replace the illustration with captured, validated output from the declared source/configuration. Abridging an output does not justify including an invalid relation.

## 14. Lower severity: document/build checks

Verified:

- `make -B` completed successfully: **25-page PDF**, zero LaTeX errors, zero undefined references/citations, zero duplicate hyperref destination warnings in the final log.
- There are **24 overfull hboxes**, including a 54.63 pt architecture figure overflow at source lines 150–151. Fix figure/table widths and long code/math strings.
- All **26** displayed Appendix A rows match the report generator's counts and medians after mapping the abbreviated `continued_fract_sign` label to `continued_fraction_sign`. The problem is coverage/interpretation, rather than copied row values.
- Appendix A claims a full program breakdown, but shows only 26 of 113 programs. Its introductory suite list omits NLA-mosaic. Rename it “selected results” or provide the full table.
- `\tbd` and `\TODO` definitions remain at lines 22–23, but have no active uses. They produce no visible placeholders. Remove the unused definitions to satisfy the handoff's stricter literal check.
- Main text uses `\dig` and prior tool `\digold` consistently; title/running header and the historical memorial mention use explicit names. Credits/disclosure blocks are commented out as described.
- NLA-mosaic says 11 families but enumerates ten groups. The paired Chebyshev benchmark has a different target equation from the one collectively given for both variants.

The main text ends on PDF page 17; references start on page 18, Appendix A on page 20. This audit does not independently verify current venue rules, live web UI behavior, author biographical facts, or submission metadata.

## Recommended order of work

1. Address incomplete-exploration false proofs and separate bounded/trace/inductive statuses.
2. Establish target-level recovery/proof evidence and complete or honestly scope the benchmark campaign.
3. Rebuild comparison, ablation, and case-study tables from identified datasets; reconcile prose automatically.
4. Rewrite the degree, static-engine, and worked verification explanations against the code.
5. Clean up layout and document coverage after the substantive corrections.

Audit generated `benchmark/results/sample_run/REPORT.md` using the existing generator and rebuilt LaTeX outputs. Raw benchmark result files were not changed; a new full benchmark campaign was not run.
