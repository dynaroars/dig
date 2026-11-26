# TSE inferred equality catalog

Actual equations from saved current-source runs, grouped by program and trace location. Different bases are retained; no exact match to a historical formula is required. Degree and monomial count help identify interesting candidates. Target success is checked separately by semantic implication.

This is an observational record, not an automatically accepted golden baseline. The companion JSON preserves every run's equations, DIG status, command, targets, source hashes, timing, and evidence paths. Regenerate with `/usr/bin/python3 benchmark/catalog_tse_invariants.py`; this reads saved results only.

## complexity/cav09_fig1a

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 2 | 5 | `-m*tCtr + 100*m + tCtr**2 - 200*tCtr + 10000 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/cav09_fig1d

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 2 | 5 | `-m*tCtr + 100*m + tCtr**2 - 200*tCtr + 10000 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/cav09_fig2d

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 2 | 2 | `m*n - tCtr = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/cav09_fig3a

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 2 | 2 | `-n*tCtr + tCtr**2 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/cav09_fig5b

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 1 | 3 | `a + tCtr - y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace_post | 2 | 4 | `tCtr**2 - 2*tCtr*y - tCtr + 2*x = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/pldi09_ex6

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 3 | 8 | `16*m*n + 2*m*tCtr**2 - 12*m*tCtr + 8*n**2 + n*tCtr**2 - 14*n*tCtr - tCtr**3 + 6*tCtr**2 = 0` | 2 |
| vtrace_post | 3 | 6 | `2*m*n**2 - 2*m*n + n**3 - n**2*tCtr - n**2 + n*tCtr = 0` | 0, 2, 3, 4, 5, 6 |
| vtrace_post | 3 | 6 | `2*m*n*tCtr - 2*m*tCtr + n**2*tCtr - n*tCtr**2 - n*tCtr + tCtr**2 = 0` | 0, 2, 3, 4, 5, 6 |
| vtrace_post | 3 | 6 | `2*m*tCtr**2 - 8*m*tCtr + n*tCtr**2 - 4*n*tCtr - tCtr**3 + 4*tCtr**2 = 0` | 1 |
| vtrace_post | 3 | 9 | `4*m**2*n + 6*m*n - 6*m*tCtr - n**3 + 2*n**2*tCtr + 3*n**2 - n*tCtr**2 - 6*n*tCtr + 3*tCtr**2 = 0` | 0, 2, 3, 4, 5, 6 |
| vtrace_post | 3 | 9 | `4*m**2*tCtr + 48*m*n - 30*m*tCtr - n**2*tCtr + 24*n**2 + 2*n*tCtr**2 - 39*n*tCtr - tCtr**3 + 15*tCtr**2 = 0` | 2 |
| vtrace_post | 3 | 7 | `4*m**2*tCtr - 18*m*tCtr - n**2*tCtr + 2*n*tCtr**2 - 9*n*tCtr - tCtr**3 + 9*tCtr**2 = 0` | 1 |
| vtrace_post | 3 | 8 | `4*m**2*tCtr - 6*m*tCtr**2 + 6*m*tCtr - n**2*tCtr - n*tCtr**2 + 3*n*tCtr + 2*tCtr**3 - 3*tCtr**2 = 0` | 0, 3, 4, 5, 6 |
| vtrace_post | 2 | 5 | `8*m*n - 2*m*tCtr + 4*n**2 - 5*n*tCtr + tCtr**2 = 0` | 1 |
| vtrace_post | 1 | 3 | `i - n - 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/pldi09_fig2

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 4 | 24 | `-M**2*N**2 + M**2*N*P + M**2*N*tCtr - M**2*P*tCtr - M*N**2*P + M*N**2*tCtr - 2*M*N**2 + M*N*P**2 + M*N*P - M*N*tCtr**2 + 3*M*N*tCtr - M*P**2*tCtr + M*P*tCtr**2 - M*P*tCtr - M*tCtr**2 - N**2*P + N**2*tCtr - N**2 + 2*N*P*tCtr - 2*N*tCtr**2 + 2*N*tCtr - P*tCtr**2 + tCtr**3 - tCtr**2 = 0` | 0, 1, 2, 5, 6 |
| vtrace_post | 4 | 37 | `131*M**3*N - 131*M**3*P + 137*M**2*N**2 + 131*M**2*N*P - 131*M**2*N*tCtr - 40784*M**2*N - 268*M**2*P**2 + 131*M**2*P*tCtr + 40915*M**2*P - 131*M**2*tCtr + 137*M*N**2*P - 137*M*N**2*tCtr + 274*M*N**2 - 40778*M*N*P + 40778*M*N*tCtr - 81961*M*N - 137*M*P**3 + 137*M*P**2*tCtr + 40909*M*P**2 - 41314*M*P*tCtr + 41046*M*P + 131*M*tCtr**2 + 40915*M*tCtr + 137*N**2*P - 137*N**2*tCtr + 137*N**2 + 137*N*P**2 - 274*N*P*tCtr - 40909*N*P + 137*N*tCtr**2 + 40909*N*tCtr - 41046*N - 137*P**2*tCtr + 137*P*tCtr**2 + 40909*P*tCtr - 41046*tCtr**2 + 41046*tCtr = 0` | 3 |
| vtrace_post | 4 | 31 | `131*M**3*N - 131*M**3*P + 268*M**2*N*P + 6*M**2*N*tCtr - 40784*M**2*N - 268*M**2*P**2 - 6*M**2*P*tCtr + 40915*M**2*P - 131*M**2*tCtr + 137*M*N*P**2 - 40641*M*N*P - 137*M*N*tCtr**2 + 41189*M*N*tCtr - 81961*M*N - 137*M*P**3 + 40909*M*P**2 + 137*M*P*tCtr**2 - 41451*M*P*tCtr + 41046*M*P - 6*M*tCtr**2 + 40915*M*tCtr + 137*N*P**2 - 40909*N*P - 137*N*tCtr**2 + 41183*N*tCtr - 41046*N - 137*P**2*tCtr + 40909*P*tCtr + 137*tCtr**3 - 41183*tCtr**2 + 41046*tCtr = 0` | 3 |
| vtrace_post | 4 | 37 | `176*M**3*N - 176*M**3*P + 191*M**2*N**2 + 176*M**2*N*P - 176*M**2*N*tCtr - 69713*M**2*N - 367*M**2*P**2 + 176*M**2*P*tCtr + 69889*M**2*P - 176*M**2*tCtr + 191*M*N**2*P - 191*M*N**2*tCtr + 382*M*N**2 - 69698*M*N*P + 69698*M*N*tCtr - 139954*M*N - 191*M*P**3 + 191*M*P**2*tCtr + 69874*M*P**2 - 70432*M*P*tCtr + 70065*M*P + 176*M*tCtr**2 + 69889*M*tCtr + 191*N**2*P - 191*N**2*tCtr + 191*N**2 + 191*N*P**2 - 382*N*P*tCtr - 69874*N*P + 191*N*tCtr**2 + 69874*N*tCtr - 70065*N - 191*P**2*tCtr + 191*P*tCtr**2 + 69874*P*tCtr - 70065*tCtr**2 + 70065*tCtr = 0` | 4 |
| vtrace_post | 4 | 31 | `176*M**3*N - 176*M**3*P + 367*M**2*N*P + 15*M**2*N*tCtr - 69713*M**2*N - 367*M**2*P**2 - 15*M**2*P*tCtr + 69889*M**2*P - 176*M**2*tCtr + 191*M*N*P**2 - 69507*M*N*P - 191*M*N*tCtr**2 + 70271*M*N*tCtr - 139954*M*N - 191*M*P**3 + 69874*M*P**2 + 191*M*P*tCtr**2 - 70623*M*P*tCtr + 70065*M*P - 15*M*tCtr**2 + 69889*M*tCtr + 191*N*P**2 - 69874*N*P - 191*N*tCtr**2 + 70256*N*tCtr - 70065*N - 191*P**2*tCtr + 69874*P*tCtr + 191*tCtr**3 - 70256*tCtr**2 + 70065*tCtr = 0` | 4 |
| vtrace_post | 4 | 15 | `M**2*N**2 - M**2*N*P + M*N**2*P - M*N**2*tCtr + 2*M*N**2 - M*N*P**2 + M*N*P*tCtr - M*N*P - M*N*tCtr + N**2*P - N**2*tCtr + N**2 - N*P*tCtr + N*tCtr**2 - N*tCtr = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/pldi09_fig4_1

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 1 | 3 | `-n + tCtr - 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/pldi09_fig4_2

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 2 | 4 | `m*n - m*tCtr + n - y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace_post | 1 | 1 | `x = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/pldi09_fig4_3

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 2 | 3 | `m*n + n - tCtr = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/pldi09_fig4_5

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 2 | 4 | `-m**2 + m*n - n*tCtr + tCtr**2 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/popl09_fig2_1

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 3 | 12 | `a**2*tCtr + a*b*tCtr - a*m*tCtr - 2*a*n*tCtr + 2*a*tCtr**2 - b*n*tCtr + b*tCtr**2 + m*n*tCtr - m*tCtr**2 + n**2*tCtr - 2*n*tCtr**2 + tCtr**3 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/popl09_fig2_2

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 3 | 9 | `a**2*tCtr + a*b*tCtr - 3*a*n*tCtr + 2*a*tCtr**2 - b*n*tCtr + b*tCtr**2 + 2*n**2*tCtr - 3*n*tCtr**2 + tCtr**3 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/popl09_fig3_4

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 3 | 4 | `m*n*tCtr - m*tCtr**2 - n*tCtr**2 + tCtr**3 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/popl09_fig4_1

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 2 | 3 | `-m*tCtr - n*tCtr + tCtr**2 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/popl09_fig4_2

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 3 | 12 | `a**2*tCtr + a*b*tCtr - a*m*tCtr - 2*a*n*tCtr + 2*a*tCtr**2 - b*n*tCtr + b*tCtr**2 + m*n*tCtr - m*tCtr**2 + n**2*tCtr - 2*n*tCtr**2 + tCtr**3 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/popl09_fig4_3

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 2 | 3 | `m*x - tCtr + x = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace_post | 1 | 2 | `n - x = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace_post | 1 | 1 | `y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## complexity/popl09_fig4_4

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace_post | 2 | 3 | `m*n + n - tCtr = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/01.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `-x + y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/02.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `-x + y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/03.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

No polynomial equalities emitted; see saved output for other invariant types.

## hola/04.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

No polynomial equalities emitted; see saved output for other invariant types.

## hola/05.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 3 | 7 | `-i**3 + 3*i**2*j + 3*i**2 - 3*i*j**2 - 4*i*j + j**3 + j**2 = 0` | 0, 1, 2, 3, 5, 6 |

## hola/06.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `-x + y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/07.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 3 | `-a - b + 3*n = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/08.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

No polynomial equalities emitted; see saved output for other invariant types.

## hola/09.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

No polynomial equalities emitted; see saved output for other invariant types.

## hola/10.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `x - 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace | 1 | 2 | `y - 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/11.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `j - 200 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace | 1 | 2 | `x - 100 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/12.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

No polynomial equalities emitted; see saved output for other invariant types.

## hola/13.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 2 | 3 | `-j*k + 2*k**2 + 2*k = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/14.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 2 | 2 | `-a**2 + m**2 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/15.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

No polynomial equalities emitted; see saved output for other invariant types.

## hola/16.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 3 | `i - j + y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/17.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 3 | 4 | `-6*k + n**3 - n + 6 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/18.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 1 | 2 | `j - 100 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/19.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `n - y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/20.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 3 | `k - x - y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace | 2 | 3 | `m**2 - m*n + m = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/21.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 2 | 3 | `k**2 - 6000*k*n + 8000000*n**2 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/22.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `-x + y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace | 1 | 2 | `-x + z = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/23.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

No polynomial equalities emitted; see saved output for other invariant types.

## hola/24.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

No polynomial equalities emitted; see saved output for other invariant types.

## hola/25.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 1 | `j = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/26.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `-x + y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/27.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

No polynomial equalities emitted; see saved output for other invariant types.

## hola/28.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 1 | `n = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace | 1 | 1 | `y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/29.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 3 | `-a + d - 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace | 1 | 3 | `-b + c - 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/30.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `c - 499500 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/31.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace2 | 1 | 1 | `i = 0` | 0, 2, 4 |

## hola/32.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `-i + j = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/33.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `-i + j = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/34.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `x - 10 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace | 1 | 2 | `y - 5 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/35.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `n - x = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/36.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `-a + b = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace | 1 | 2 | `-w + z = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/37.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 3 | `m - n + 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/38.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `-x + 2*y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/39.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

No polynomial equalities emitted; see saved output for other invariant types.

## hola/40.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `-a + b = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/41.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 2 | 4 | `-2*j + n**2 + 3*n + 2 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace | 1 | 3 | `i - n - 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/43.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

No polynomial equalities emitted; see saved output for other invariant types.

## hola/44.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `flag - 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace | 1 | 2 | `i - j = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/45.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `-x + y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## hola/46.dig

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace | 1 | 2 | `x - 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/bresenham

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 5 | `-2*X*y - X + 2*Y*x + 2*Y - v = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/cohencu

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 4 | `-12*y + z**2 - 6*z + 12 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 5 | `-18*x + y*z - 12*y + 2*z - 6 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 6 | `-3*x*z - 18*x + 2*y**2 - 10*y + 3*z - 10 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 4 | `12*y - z**2 + 6*z - 12 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 3 | 5 | `216*x - z**3 + 18*z**2 - 108*z + 216 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 1 | 3 | `6*n - z + 6 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/cohendiv

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 2 | `a*y - b = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 3 | `q*y + r - x = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace2 | 2 | 2 | `a*y - b = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace2 | 2 | 3 | `q*y + r - x = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/dijkstra

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 1 | 1 | `h = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 1 | 2 | `n - r = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 1 | 1 | `p = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace2 | 2 | 3 | `n*q - p**2 - q*r = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/divbin

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 1 | 2 | `A - r = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 1 | 1 | `q = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace2 | 2 | 3 | `-A + b*q + r = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/egcd

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 3 | `-a + p*x + r*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 3 | `-a*q + b*p - y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 3 | `-a*s + b*r + x = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 3 | `-b + q*x + s*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 3 | `-p*s + q*r + 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/egcd2

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 3 | `-a + p*x + r*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 3 | `-b + q*x + s*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace2 | 2 | 3 | `-a + b*k + c = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace2 | 2 | 3 | `-a + p*x + r*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace2 | 2 | 3 | `-b + q*x + s*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace3 | 2 | 3 | `-a + p*x + r*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace3 | 2 | 2 | `q*x + s*y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/egcd3

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtraces1 | 2 | 3 | `-a + p*x + r*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces1 | 2 | 3 | `-b + q*x + s*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces2 | 2 | 3 | `-a + b*k + c = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces2 | 2 | 3 | `-a + p*x + r*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces2 | 2 | 3 | `-b + q*x + s*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces3 | 2 | 3 | `-a + b*k + c = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces3 | 2 | 3 | `-a + p*x + r*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces3 | 2 | 3 | `-b + q*x + s*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces3 | 2 | 2 | `b*d - v = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces4 | 2 | 3 | `-a + p*x + r*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces4 | 1 | 1 | `b = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces4 | 2 | 2 | `q*x + s*y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/fermat1

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtraces1 | 2 | 6 | `4*A + 4*r - u**2 + 2*u + v**2 - 2*v = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces2 | 2 | 6 | `4*A + 4*r - u**2 + 2*u + v**2 - 2*v = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtraces3 | 2 | 6 | `4*A + 4*r - u**2 + 2*u + v**2 - 2*v = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/fermat2

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtraces1 | 2 | 6 | `4*A + 4*r - u**2 + 2*u + v**2 - 2*v = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/freire1

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 4 | `-a + r**2 - r + 2*x = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/freire1_int

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 4 | `-a + r**2 - r + 2*x = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/freire2

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 3 | 13 | `-15264*a**2 + 64*a*s**2 + 46384*a*s + 30528*a*x + 3740932*a + 4707045*r - 64*s**2*x - 95856*s**2 - 46384*s*x - 578868*s - 15264*x**2 - 3740932*x - 1813245 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 3 | 11 | `-1728*a**2 - 1728*a*s + 3456*a*x - 432*a + 64*s**3 - 192*s**2 + 1728*s*x - 24*s - 1728*x**2 + 432*x - 91 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 6 | `-24*a + 8*r*s + 16*r - 12*s + 24*x - 3 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 3 | `12*r**2 - 4*s + 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 3 | 14 | `256*a**2*s - 293248*a**2 - 512*a*s*x + 1266560*a*s + 586496*a*x + 115907056*a + 159757164*r - 2848384*s**2 + 256*s*x**2 - 1266560*s*x - 20718460*s - 293248*x**2 - 115907056*x - 62336113 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 3 | 15 | `768*a**3 - 2304*a**2*x - 3104352*a**2 + 15273888*a*s + 2304*a*x**2 + 6208704*a*x + 1519820676*a + 2227641759*r - 36318016*s**2 - 15273888*s*x - 297336004*s - 768*x**3 - 3104352*x**2 - 1519820676*x - 877690702 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/geo1

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 4 | `x*z - x - y + 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/geo2

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 4 | `-x*z + x + y*z - 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 4 | `x*z - x - y*z + 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/geo3

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 3 | 4 | `a*y*z - a - x*z + x = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/hard

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 1 | 2 | `A - r = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 2 | `B*p - d = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 1 | 1 | `q = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace2 | 2 | 3 | `-A + B*q + r = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace2 | 2 | 2 | `B*p - d = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/knuth

No current-source results recorded (Knuth is deferred).

## nla/lcm1

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 3 | `-a*b + u*x + v*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace2 | 2 | 3 | `-a*b + u*x + v*y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace3 | 2 | 3 | `-a*b + u*x + v*y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/lcm2

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 3 | `-2*a*b + u*x + v*y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/mannadiv

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 4 | `a + b + q*y - x = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/prod4br

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 3 | 3 | `a*b*p + q - x*y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/prodbin

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 3 | `-a*b + x*y + z = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace2 | 2 | 2 | `a*b - z = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/ps2

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 2 | 3 | `2*x - y**2 - y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/ps3

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 3 | 4 | `-6*x + 2*y**3 + 3*y**2 + y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 3 | 4 | `6*x - 2*y**3 - 3*y**2 - y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/ps4

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 4 | 4 | `4*x - y**4 - 2*y**3 - y**2 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/ps5

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 5 | 5 | `-30*x + 6*y**5 + 15*y**4 + 10*y**3 - y = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 5 | 5 | `30*x - 6*y**5 - 15*y**4 - 10*y**3 + y = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/ps6

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 6 | 5 | `-12*x + 2*y**6 + 6*y**5 + 5*y**4 - y**2 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 6 | 5 | `12*x - 2*y**6 - 6*y**5 - 5*y**4 + y**2 = 0` | 0, 1, 2, 3, 4, 5, 6 |

## nla/sqrt1

Recorded seeds: 0, 1, 2, 3, 4, 5, 6. Target-confirmed seeds: 0, 1, 2, 3, 4, 5, 6.

| Location | Degree | Monomials | Equation | Seeds |
| :--- | ---: | ---: | :--- | :--- |
| vtrace1 | 1 | 3 | `2*a - t + 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |
| vtrace1 | 2 | 4 | `4*s - t**2 - 2*t - 1 = 0` | 0, 1, 2, 3, 4, 5, 6 |
