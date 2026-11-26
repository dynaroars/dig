# NLA-mosaic DIG results

Seed 42; 90.0s per program; `eqt,recurrence`; explicit degree caps from manifest; Kapur=True; dynamic=False; trace input=False.

Recovery means the target equality is present up to a nonzero scalar factor. Counts alone are not a recovery criterion. DIG's ordinary equality checking uses bounded symbolic states; these results do not establish unbounded proofs.

| Program | Run status | Seconds | Target equalities recovered | All invariants |
|---|---|---:|---:|---:|
| [berggren](berggren.log) | timeout | 90.029 | 0/1 | 0 |
| [chebyshev](chebyshev.log) | ok | 8.825 | 1/1 | 1 |
| [chebyshev_pair](chebyshev_pair.log) | no_summary | 7.266 | 0/1 | 0 |
| [continued_fraction](continued_fraction.log) | no_summary | 6.389 | 0/1 | 0 |
| [fibonacci_trace](fibonacci_trace.log) | timeout | 90.110 | 0/1 | 0 |
| [markov](markov.log) | no_summary | 16.797 | 0/1 | 0 |
| [nagata](nagata.log) | ok | 64.791 | 1/1 | 1 |
| [symplectic_euler](symplectic_euler.log) | no_summary | 24.003 | 0/1 | 0 |
| [welford](welford.log) | no_summary | 8.779 | 0/2 | 0 |

## Equality output

### berggren

```text
```

### chebyshev

```text
-a**2 + 2*a*b*t - b**2 - t**2 + 1
```

### chebyshev_pair

```text
```

### continued_fraction

```text
```

### fibonacci_trace

```text
```

### markov

```text
```

### nagata

```text
-constant + x*z + y**2
```

### symplectic_euler

```text
```

### welford

```text
```

