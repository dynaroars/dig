# Additional programs with nonlinear numerical invariants

Research date: 2026-10-06.

Implemented as 14 C benchmarks in
[NLA-mosaic](../../benchmark/c/NLA-mosaic/README.md), including measured DIG
results from source and from collected C traces. The implementation notes
distinguish inferred relations, bounded checks, and floating-point limitations.

## Existing coverage

The project has 33 top-level C programs in `benchmark/c/nla` and 26 in
`benchmark/c/nla_full`; these directories overlap substantially. Existing
families include extended GCD and LCM, several division and multiplication
algorithms, square/cube-root computations, Fermat factorization, power sums,
geometric sums, Bresenham line drawing, and Wensley division.

Representative relations already present include:

- `egcd.c`: `p*s - r*q = 1`, `a = y*r + x*p`.
- `prodbin.c`: `z + x*y = a*b`.
- `prod4br.c`: `q + a*b*p = x*y`.
- `dijkstra.c`: `p*p + r*q = n*q`.
- `ps3.c`: `6*x - 2*y^3 - 3*y^2 - y = 0`.
- `bresenham.c`: `2*Y*x - 2*X*y - X + 2*Y - v = 0`.

A search of names and contents under `benchmark` and `examples` found none
of the candidate families below. This establishes absence of recognizable
implementations there, rather than a formal equivalence check of every program.

## Candidate programs

All tuple updates below are simultaneous: a C translation must use temporaries.
Degrees count every observed variable, including immutable input parameters.
The invariants use mathematical integer or exact real arithmetic. Loop heads
are the intended observation points. Each unbounded example can be wrapped
in a loop with an input iteration limit.

### 1. Pell equation solution generator

Initialize `(x,y) = (1,0)` and repeat

```text
(x,y) <- (3*x + 4*y, 2*x + 3*y)
```

Invariant: **`x^2 - 2*y^2 = 1`**, degree 2. Generates `(3,2)`, `(17,12)`,
`(99,70)`, etc. This is a benchmark adaptation of multiplication by
`3 + 2*sqrt(2)`, as developed in §4 of
[Conrad, Pell's Equation I](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/pelleqn1.pdf).

Useful as a small integer recurrence benchmark with exponential growth and a
quadratic relation that does not directly involve the iteration counter.
Specializing other nonsquare constants gives variants; treating the radicand
as an input raises the degree of the corresponding invariant to 3.

### 2. Fibonacci / Cassini

Initialize `(a,b) = (0,1)` and repeat `(a,b) <- (b,a+b)`.

Invariant: **`(a^2 + a*b - b^2)^2 = 1`**, degree 4.
The unsquared expression alternates between -1 and +1; it is not a constant
quadratic equality. An additional sign variable initialized to -1 and negated
each iteration gives `a^2 + a*b - b^2 = sign`.

This loop and the expanded quartic appear in the
[Polar documentation](https://github.com/probing-lab/polar#introduction).
It exercises parity, polynomial representations of disjunctions, and the
difference between linear updates and nonlinear invariant degree.

### 3. Markov triples

The published toggling loop starts at `(x,y,z,branch) = (1,1,2,0)`:

```text
branch = 0: (x,y,z,branch) <- (x, 3*x*y-z, y, 1)
branch = 1: (x,y,z,branch) <- (y, 3*y*z-x, z, 0)
```

Invariant: **`x^2 + y^2 + z^2 = 3*x*y*z`**, degree 3.
Source: Example 39 of
[(Un)Solvable Loop Analysis](https://link.springer.com/article/10.1007/s10703-024-00455-0).
A variant can choose either branch nondeterministically; both preserve the relation.

### 4. Fibonacci trace map

Repeat `(x,y,z) <- (y,z,2*y*z-x)`.

Invariant: **`x^2 + y^2 + z^2 - 2*x*y*z = C`**, degree 3,
where `C` is its initial value. A fixed start `(1,2,3)` gives `C=2`.
Source: Example 36 of
[(Un)Solvable Loop Analysis](https://link.springer.com/article/10.1007/s10703-024-00455-0).
It tests a nonlinear cyclic dependency with a conserved polynomial.

### 5. Berggren's Pythagorean triple generator

Initialize `(a,b,c) = (3,4,5)`. At each iteration choose one of these updates:

```text
A: (a,b,c) <- ( a-2*b+2*c,  2*a-b+2*c,  2*a-2*b+3*c)
B: (a,b,c) <- (-a+2*b+2*c, -2*a+b+2*c, -2*a+2*b+3*c)
C: (a,b,c) <- ( a+2*b+2*c,  2*a+b+2*c,  2*a+2*b+3*c)
```

Invariant: **`a^2 + b^2 = c^2`**, degree 2. The transformations come from
[Conrad, Pythagorean Descent, equation (1.1)](https://kconrad.math.uconn.edu/blurbs/linmultialg/descentPythag.pdf).
An implementation can use an input branch selector, a cyclic selector, or
nondeterministic choices. The latter explores more of the solution tree.

This is a useful three-branch benchmark with a common quadratic invariant.
Single-branch versions may have additional special invariants, so they should
be recorded as separate variants.

### 6. Continued-fraction convergents

Start `(p,r,q,s,sign) = (1,0,0,1,1)`. For each partial quotient `t`, repeat

```text
(p,r,q,s,sign) <- (t*p+r, p, t*q+s, q, -sign)
```

Invariant: **`p*s - r*q = sign`**, degree 2. Without the sign variable,
**`(p*s-r*q)^2 = 1`**, degree 4. These follow from the determinant identity
in Proposition 30.7 of
[Al-Faisal's Elementary Number Theory notes](https://math.uwaterloo.ca/~f2alfais/notes/pm340-notes.pdf).

This adaptation permits varying positive partial quotients, testing an
invariant that survives changing coefficients. It shares determinant algebra
with `egcd.c`, but computes rational approximations instead of reducing a GCD.
Fixed quotients would produce a simpler recurrence variant.

### 7. Chebyshev polynomial evaluation

For an immutable input `t`, start `(a,b)=(1,t)` and repeat
`(a,b) <- (b,2*t*b-a)`.

Invariant: **`a^2 + b^2 - 2*t*a*b = 1-t^2`**, degree 3.
A paired evaluator starts `(T,U)=(1,0)` and repeats

```text
(T,U) <- (t*T + (t*t-1)*U, T + t*U)
```

It satisfies **`T^2 - (t^2-1)*U^2 = 1`**, degree 4, with
`T=T_n(t)` and `U=U_(n-1)(t)` after n iterations.
These are derived benchmark formulations using the definitions and recurrence
relations in [NIST DLMF §18.5](https://dlmf.nist.gov/18.5)
and [§18.9](https://dlmf.nist.gov/18.9).

Integer `t` permits integer arithmetic. An input parameter increases polynomial
degree compared with fixing `t`; these should be distinct benchmark variants.

### 8. Nagata polynomial map

Compute `d=x*z+y*y` from the old state, then update

```text
(x,y,z) <- (x-2*y*d-z*d*d, y+z*d, z)
```

Invariants: **`z=z0`**, **`x*z+y^2=x0*z0+y0^2`**, degrees 1 and 2.
Source: Example 43 of
[(Un)Solvable Loop Analysis](https://link.springer.com/article/10.1007/s10703-024-00455-0).
Degree-5 assignments preserve a quadratic relation.

### 9. Multiplicative binomial coefficient computation

For `N>=0`, start `(k,c,prev)=(0,1,0)`; while `k<N`, perform

```text
prev = c
k = k+1
c = prev*(N-k+1)/k
```

Loop-head invariant: **`k*c = (N-k+1)*prev`**, degree 2. Here
`c=binomial(N,k)`, and `prev` retains the preceding coefficient.
The recurrence comes from
[NIST DLMF equation 26.3.6](https://dlmf.nist.gov/26.3#E6).

This benchmark adaptation exercises exact integer division by a changing
denominator. The polynomial relation is between adjacent coefficients; a
formula involving only `N`, `k`, and `c` should not be assumed to have bounded
polynomial degree. Multiplication must precede division.

### 10. Welford's online mean and variance

Initialize `(n,mean,M2,S,Q)=(0,0,0,0,0)`. For each sample `v`, perform

```text
n = n+1
delta = v-mean
mean = mean+delta/n
M2 = M2+delta*(v-mean)
S = S+v
Q = Q+v*v
```

In exact arithmetic, **`n*mean=S`** and
**`M2-Q+n*mean^2=0`**, degrees 2 and 3. Equivalently,
**`n*M2-n*Q+S^2=0`** is quadratic. `S` and `Q` are auxiliary prefix sums
added to expose the relation to observed scalar variables.

The algorithm originates in
[Welford, Note on a Method for Calculating Corrected Sums of Squares and Products (1962)](https://www.tandfonline.com/doi/abs/10.1080/00401706.1962.10490022).
The variance definitions are documented in the
[GNU Scientific Library](https://www.gnu.org/software/gsl/doc/html/statistics.html).
This is an application benchmark adaptation; floating-point execution generally
needs an error bound rather than these exact equalities.

### 11. Symplectic Euler harmonic oscillator

For a fixed step `h`, perform the sequential updates

```text
p = p-h*q
q = q+h*p
```

Invariant: **`p^2+q^2-h*p*q = E0`**, where `E0` is its initial value.
Degree 2 for a specialized `h`, or 3 when `h` is an observed input parameter.
This is the momentum-first ordering. The position-first ordering has a positive
cross term; related modified-energy conservation is discussed in
[Hairer and Vilmart, Computing the Long Term Evolution of the Solar System with Geometric Numerical Integrators, §3](https://www.unige.ch/~vilmart/snapshots-2017-009.pdf).
The displayed sign and coefficient were independently derived and checked.

This gives a numerical-integration benchmark. Exact rational arithmetic is the
natural specification; ordinary floating-point runs need a rounding-error model.

## Suggested first additions

My suggested first set is **Pell, Fibonacci, Markov triples, Fibonacci trace
map, and Berggren**, followed by **Chebyshev with an input parameter**. They
cover integer arithmetic, degrees 2–4, multiple branches, parity, and cyclic
nonlinear updates. Each has a mathematical origin independent of the existing
power-sum and division examples.

Continued fractions and binomial coefficients add changing coefficients and
exact division. Nagata stresses the relationship between assignment degree and
invariant degree. Welford and symplectic Euler add practical application areas
and should carry an explicit exact-real or floating-point specification.

## Existing artifacts to inspect

- [Polar's benchmark collection](https://github.com/probing-lab/polar/tree/master/benchmarks)
  includes `fibtrace`, `defective`, and a `markov-triples.prob` file. Its input
  format requires translation to the project's C instrumentation.
- [Algebraic Tools for Computing Polynomial Loop Invariants, extended paper](https://arxiv.org/html/2412.14043v1)
  points to the authors'
  [Macaulay2 implementation and examples](https://github.com/FatemehMohammadi/Algebraic_PolyLoop_Invariants).
  Reported examples include MarkovTriples, Nagata, Squares, and higher-dimensional
  Yagzhev maps. The repository landing page was inspected; individual loop files
  could not be retrieved through the browser during this search.

## Verification and translation considerations

Seventeen SymPy checks established exact symbolic preservation for the displayed
updates across eleven families, including both Markov branches, all three
Berggren branches, both Chebyshev formulations, and the two Welford relations.
Binomial loops were additionally checked for `N=0..20`, including divisibility
and equality to the corresponding binomial coefficients. These checks establish
the stated arithmetic relations; DIG inference and runtime have not been measured.

For C versions, use the project's `mainQ` and `vtrace` conventions, preserve
simultaneous-assignment semantics with temporaries, and retain immutable initial
values when a conserved quantity depends on them. Expose parameters to `vtrace`
when evaluating parameterized invariant degree. Bound integer runs or use exact
integer semantics to avoid signed overflow, including overflow in assertions.
Small fixed seeds give convenient first examples; varied seeds and branch
choices reduce the chance of incidental relations from narrow traces.
