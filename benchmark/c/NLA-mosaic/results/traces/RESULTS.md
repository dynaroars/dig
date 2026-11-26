# NLA-mosaic DIG results

Seed 42; 120.0s per program; `eqt`; explicit degree caps from manifest; Kapur=False; dynamic=False; trace input=True.

Recovery means the target equality is present up to a nonzero scalar factor. Counts alone are not a recovery criterion. DIG's ordinary equality checking uses bounded symbolic states; these results do not establish unbounded proofs.

| Program | Run status | Seconds | Target equalities recovered | All invariants |
|---|---|---:|---:|---:|
| [berggren](berggren.log) | ok | 5.410 | 1/1 | 1 |
| [binomial](binomial.log) | ok | 3.323 | 1/1 | 1 |
| [chebyshev](chebyshev.log) | ok | 4.244 | 1/1 | 1 |
| [chebyshev_pair](chebyshev_pair.log) | ok | 4.200 | 1/1 | 1 |
| [continued_fraction](continued_fraction.log) | ok | 15.091 | 1/1 | 1 |
| [continued_fraction_sign](continued_fraction_sign.log) | ok | 5.014 | 1/1 | 2 |
| [fibonacci](fibonacci.log) | ok | 4.090 | 1/1 | 1 |
| [fibonacci_sign](fibonacci_sign.log) | ok | 4.276 | 1/1 | 2 |
| [fibonacci_trace](fibonacci_trace.log) | ok | 7.137 | 1/1 | 1 |
| [markov](markov.log) | ok | 3.463 | 1/1 | 1 |
| [nagata](nagata.log) | ok | 3.456 | 1/1 | 1 |
| [pell](pell.log) | ok | 4.480 | 1/1 | 1 |
| [symplectic_euler](symplectic_euler.log) | ok | 8.794 | 1/1 | 1 |
| [welford](welford.log) | no_summary | 4.785 | 0/2 | 0 |

## Equality output

### berggren

```text
-a**2 - b**2 + c**2
```

### binomial

```text
-N*prev + c*k + k*prev - prev
```

### chebyshev

```text
-a**2 + 2*a*b*t - b**2 - t**2 + 1
```

### chebyshev_pair

```text
-T**2 + U**2*t**2 - U**2 + 1
```

### continued_fraction

```text
p**2*s**2 - 2*p*q*r*s + q**2*r**2 - 1
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
constant - x**2 + 2*x*y*z - y**2 - z**2
```

### markov

```text
-x**2 + 3*x*y*z - y**2 - z**2
```

### nagata

```text
-constant + x*z + y**2
```

### pell

```text
-x**2 + 2*y**2 + 1
```

### symplectic_euler

```text
energy + h*p*q - p**2 - q**2
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

