# NLA-mosaic DIG results

Seed 42; 120.0s per program; `eqt,recurrence`; explicit degree caps from manifest; Kapur=False; dynamic=False; trace input=False.

Recovery means the target equality is present up to a nonzero scalar factor. Counts alone are not a recovery criterion. DIG's ordinary equality checking uses bounded symbolic states; these results do not establish unbounded proofs.

| Program | Run status | Seconds | Target equalities recovered | All invariants |
|---|---|---:|---:|---:|
| [berggren](berggren.log) | timeout | 120.018 | 0/1 | 0 |
| [binomial](binomial.log) | ok | 7.199 | 1/1 | 1 |
| [chebyshev](chebyshev.log) | no_summary | 11.581 | 0/1 | 0 |
| [chebyshev_pair](chebyshev_pair.log) | no_summary | 18.292 | 0/1 | 0 |
| [continued_fraction](continued_fraction.log) | no_summary | 27.788 | 0/1 | 0 |
| [continued_fraction_sign](continued_fraction_sign.log) | ok | 12.494 | 1/1 | 2 |
| [fibonacci](fibonacci.log) | ok | 4.131 | 1/1 | 1 |
| [fibonacci_sign](fibonacci_sign.log) | ok | 3.984 | 1/1 | 2 |
| [fibonacci_trace](fibonacci_trace.log) | no_summary | 22.513 | 0/1 | 0 |
| [markov](markov.log) | no_summary | 10.298 | 0/1 | 0 |
| [nagata](nagata.log) | no_summary | 25.213 | 0/1 | 0 |
| [pell](pell.log) | ok | 4.283 | 1/1 | 1 |
| [symplectic_euler](symplectic_euler.log) | no_summary | 24.141 | 0/1 | 0 |
| [welford](welford.log) | no_summary | 10.965 | 0/2 | 0 |

## Equality output

### berggren

```text
```

### binomial

```text
-N*prev + c*k + k*prev - prev
```

### chebyshev

```text
```

### chebyshev_pair

```text
```

### continued_fraction

```text
```

### continued_fraction_sign

```text
sign**2 - 1
-p*s + q*r + sign
```

### fibonacci

```text
a**4 + 2*a**3*b - a**2*b**2 - 2*a*b**3 + b**4 - 1
```

### fibonacci_sign

```text
sign**2 - 1
-a**2 - a*b + b**2 + sign
```

### fibonacci_trace

```text
```

### markov

```text
```

### nagata

```text
```

### pell

```text
-x**2 + 2*y**2 + 1
```

### symplectic_euler

```text
```

### welford

```text
```

## Concrete C validation

Compiled instrumented programs with GCC warnings as errors and UBSan. Checked the expected polynomial on every captured trace using exact integers and the exact rationals represented by C doubles.

| Program | Input cases | Trace rows | Nonzero residual rows per target |
|---|---:|---:|---|
| berggren | 75 | 465 | [0] |
| binomial | 21 | 231 | [0] |
| chebyshev | 30 | 136 | [0] |
| chebyshev_pair | 30 | 136 | [0] |
| continued_fraction | 75 | 465 | [0] |
| continued_fraction_sign | 75 | 465 | [0] |
| fibonacci | 31 | 496 | [0] |
| fibonacci_sign | 31 | 496 | [0] |
| fibonacci_trace | 209 | 955 | [0] |
| markov | 49 | 208 | [0] |
| nagata | 210 | 1145 | [0] |
| pell | 11 | 66 | [0] |
| symplectic_euler | 121 | 609 | [0] |
| welford | 67 | 453 | [60, 79] |

Welford specifies exact-real invariants; nonzero residuals in its C double traces expose rounding and are recorded in results.json.

