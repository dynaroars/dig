4/24

Results

sage: benchmark_dir('../invgen/Traces/NLA/multi_locs/',runs=2)

********** BEGIN BENCHMARK **********
Invariant Type: eqt
Trace Directory: ../invgen/Traces/NLA/multi_locs/
Number of runs for each trace file: 2
********** *************** **********



***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/cohencu.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 84 traces
dig:Info:Refine 34 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: nvu^3 - x == 0
  1: -6*nvu + z - 6 == 0
  2: nvu^2 + nvu - 1/3*y + 1/3 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 84 traces
dig:Info:Refine 34 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: nvu^3 - x == 0
  1: -6*nvu + z - 6 == 0
  2: nvu^2 + nvu - 1/3*y + 1/3 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/cohencu.l0.tcs'
Expect []
* Run 0 (time 11.279923)
  0: nvu^3 - x == 0
  1: -6*nvu + z - 6 == 0
  2: nvu^2 + nvu - 1/3*y + 1/3 == 0
* Run 1 (time 9.789675)
  0: nvu^3 - x == 0
  1: -6*nvu + z - 6 == 0
  2: nvu^2 + nvu - 1/3*y + 1/3 == 0
TIME AVG 4.9 (../invgen/Traces/NLA/multi_locs/cohencu.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/cohencu.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 84 traces
dig:Info:Refine 46 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: nvu^3 - x == 0
  1: -a + nvu - 1 == 0
  2: -6*a + z - 12 == 0
  3: a^2 + 3*a - 1/3*y + 7/3 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 84 traces
dig:Info:Refine 46 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: nvu^3 - x == 0
  1: -a + nvu - 1 == 0
  2: -6*a + z - 12 == 0
  3: a^2 + 3*a - 1/3*y + 7/3 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/cohencu.l1.tcs'
Expect []
* Run 0 (time 11.901062)
  0: nvu^3 - x == 0
  1: -a + nvu - 1 == 0
  2: -6*a + z - 12 == 0
  3: a^2 + 3*a - 1/3*y + 7/3 == 0
* Run 1 (time 12.321128)
  0: nvu^3 - x == 0
  1: -a + nvu - 1 == 0
  2: -6*a + z - 12 == 0
  3: a^2 + 3*a - 1/3*y + 7/3 == 0
TIME AVG 6.2 (../invgen/Traces/NLA/multi_locs/cohencu.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/cohendiv.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 3 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a*y - b == 0
  1: q*y + rvu - x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 3 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a*y - b == 0
  1: -q*y - rvu + x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/cohendiv.l0.tcs'
Expect []
* Run 0 (time 1.019851)
  0: a*y - b == 0
  1: q*y + rvu - x == 0
* Run 1 (time 1.108844)
  0: a*y - b == 0
  1: -q*y - rvu + x == 0
TIME AVG 0.6 (../invgen/Traces/NLA/multi_locs/cohendiv.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/cohendiv.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 3 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a*y - b == 0
  1: q*y + rvu - x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 8 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a*y - b == 0
  1: -q*y - rvu + x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/cohendiv.l1.tcs'
Expect []
* Run 0 (time 1.087127)
  0: a*y - b == 0
  1: q*y + rvu - x == 0
* Run 1 (time 6.235371)
  0: a*y - b == 0
  1: -q*y - rvu + x == 0
TIME AVG 3.1 (../invgen/Traces/NLA/multi_locs/cohendiv.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/cohendiv.l2.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 23 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: q*y + rvu - x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 23 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: q*y + rvu - x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/cohendiv.l2.tcs'
Expect []
* Run 0 (time 0.250857)
  0: q*y + rvu - x == 0
* Run 1 (time 0.284738)
  0: q*y + rvu - x == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/cohendiv.l2.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/dijkstra.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -nvu*q + p^2 + q*rvu == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -nvu*q + p^2 + q*rvu == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/dijkstra.l0.tcs'
Expect []
* Run 0 (time 0.421344)
  0: -nvu*q + p^2 + q*rvu == 0
* Run 1 (time 0.446366)
  0: -nvu*q + p^2 + q*rvu == 0
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/dijkstra.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/dijkstra.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 8 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: q - 1 == 0
  1: p^2 - nvu + rvu == 0
  2: -1/4*h^2 + h*p - nvu + rvu + 1/4 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 8 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: q - 1 == 0
  1: p^2 - nvu + rvu == 0
  2: -1/4*h^2 + h*p - nvu + rvu + 1/4 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/dijkstra.l1.tcs'
Expect []
* Run 0 (time 13.114113)
  0: q - 1 == 0
  1: p^2 - nvu + rvu == 0
  2: -1/4*h^2 + h*p - nvu + rvu + 1/4 == 0
* Run 1 (time 2.809419)
  0: q - 1 == 0
  1: p^2 - nvu + rvu == 0
  2: -1/4*h^2 + h*p - nvu + rvu + 1/4 == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/dijkstra.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/dijkstra.l2.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 15 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: p == 0
  1: h^2 == 0
  2: -nvu + rvu == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 15 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: p == 0
  1: h^2 == 0
  2: -nvu + rvu == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/dijkstra.l2.tcs'
Expect []
* Run 0 (time 2.484213)
  0: p == 0
  1: h^2 == 0
  2: -nvu + rvu == 0
* Run 1 (time 2.375525)
  0: p == 0
  1: h^2 == 0
  2: -nvu + rvu == 0
TIME AVG 1.2 (../invgen/Traces/NLA/multi_locs/dijkstra.l2.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/divbin.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: b*q - A + rvu == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: b*q - A + rvu == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/divbin.l0.tcs'
Expect []
* Run 0 (time 0.361717)
  0: b*q - A + rvu == 0
* Run 1 (time 0.357492)
  0: b*q - A + rvu == 0
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/divbin.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/divbin.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -B + b == 0
  1: B*q - A + rvu == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -B + b == 0
  1: B*q - A + rvu == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/divbin.l1.tcs'
Expect []
* Run 0 (time 1.523365)
  0: -B + b == 0
  1: B*q - A + rvu == 0
* Run 1 (time 6.655145)
  0: -B + b == 0
  1: B*q - A + rvu == 0
TIME AVG 3.3 (../invgen/Traces/NLA/multi_locs/divbin.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/divbin.l2.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 11 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: q == 0
  1: -A + rvu == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 11 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: q == 0
  1: -A + rvu == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/divbin.l2.tcs'
Expect []
* Run 0 (time 1.872042)
  0: q == 0
  1: -A + rvu == 0
* Run 1 (time 1.989212)
  0: q == 0
  1: -A + rvu == 0
TIME AVG 1.0 (../invgen/Traces/NLA/multi_locs/divbin.l2.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/egcd.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 68 traces
dig:Info:Refine 5 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: A*i + B*j - x == 0
  1: -i*m + j*k + 1 == 0
  2: A*k + B*m - y == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 68 traces
dig:Info:Refine 5 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: A*i + B*j - x == 0
  1: -i*m + j*k + 1 == 0
  2: A*k + B*m - y == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/egcd.l0.tcs'
Expect []
* Run 0 (time 2.433864)
  0: A*i + B*j - x == 0
  1: -i*m + j*k + 1 == 0
  2: A*k + B*m - y == 0
* Run 1 (time 2.437611)
  0: A*i + B*j - x == 0
  1: -i*m + j*k + 1 == 0
  2: A*k + B*m - y == 0
TIME AVG 1.2 (../invgen/Traces/NLA/multi_locs/egcd.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/egcd.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 68 traces
dig:Info:Refine 14 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -x + y == 0
  1: -j*x + m*x - A == 0
  2: -i*x + k*x + B == 0
  3: -i*m + j*k + 1 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 68 traces
dig:Info:Refine 14 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -x^2 + y^2 == 0
  1: -x^2 + x*y == 0
  2: -j*x + m*x - A == 0
  3: -i*x + k*x + B == 0
  4: -i*m + j*k + 1 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/egcd.l1.tcs'
Expect []
* Run 0 (time 3.855868)
  0: -x + y == 0
  1: -j*x + m*x - A == 0
  2: -i*x + k*x + B == 0
  3: -i*m + j*k + 1 == 0
* Run 1 (time 4.040588)
  0: -x^2 + y^2 == 0
  1: -x^2 + x*y == 0
  2: -j*x + m*x - A == 0
  3: -i*x + k*x + B == 0
  4: -i*m + j*k + 1 == 0
TIME AVG 2.0 (../invgen/Traces/NLA/multi_locs/egcd.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/euclidex1.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 99 traces
dig:Info:Refine 8 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: q*x + s*y - b == 0
  1: p*x + rvu*y - a == 0
  2: b*k - a + c == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 99 traces
dig:Info:Refine 6 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: q*x + s*y - b == 0
  1: p*x + rvu*y - a == 0
  2: b*k - a + c == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex1.l0.tcs'
Expect []
* Run 0 (time 4.477107)
  0: q*x + s*y - b == 0
  1: p*x + rvu*y - a == 0
  2: b*k - a + c == 0
* Run 1 (time 4.287956)
  0: q*x + s*y - b == 0
  1: p*x + rvu*y - a == 0
  2: b*k - a + c == 0
TIME AVG 2.1 (../invgen/Traces/NLA/multi_locs/euclidex1.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/euclidex1.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: b^2 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: b^2 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex1.l1.tcs'
Expect []
* Run 0 (time 1.147817)
  0: b^2 == 0
* Run 1 (time 1.085477)
  0: b^2 == 0
TIME AVG 0.5 (../invgen/Traces/NLA/multi_locs/euclidex1.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/euclidex1.l2.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 99 traces
dig:Info:Refine 13 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: b - c == 0
  1: q*x + s*y - c == 0
  2: p*x + rvu*y - a == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 99 traces
dig:Info:Refine 13 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -b + c == 0
  1: q*x + s*y - b == 0
  2: p*x + rvu*y - a == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex1.l2.tcs'
Expect []
* Run 0 (time 6.685469)
  0: b - c == 0
  1: q*x + s*y - c == 0
  2: p*x + rvu*y - a == 0
* Run 1 (time 7.111271)
  0: -b + c == 0
  1: q*x + s*y - b == 0
  2: p*x + rvu*y - a == 0
TIME AVG 3.6 (../invgen/Traces/NLA/multi_locs/euclidex1.l2.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/euclidex2.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 68 traces
dig:Info:Refine 5 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -p*s + q*rvu + 1 == 0
  1: p*x + q*y - a == 0
  2: rvu*x + s*y - b == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 68 traces
dig:Info:Refine 5 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a*rvu - b*p + y == 0
  1: -p*s + q*rvu + 1 == 0
  2: a*s - b*q - x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex2.l0.tcs'
Expect []
* Run 0 (time 2.613702)
  0: -p*s + q*rvu + 1 == 0
  1: p*x + q*y - a == 0
  2: rvu*x + s*y - b == 0
* Run 1 (time 2.769476)
  0: a*rvu - b*p + y == 0
  1: -p*s + q*rvu + 1 == 0
  2: a*s - b*q - x == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/euclidex2.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/euclidex2.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 68 traces
dig:Info:Refine 14 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a - b == 0
  1: -b*q + b*s - x == 0
  2: -b*p + b*rvu + y == 0
  3: -p*s + q*rvu + 1 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 68 traces
dig:Info:Refine 14 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -a + b == 0
  1: -a*q + a*s - x == 0
  2: -a*p + a*rvu + y == 0
  3: -p*s + q*rvu + 1 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex2.l1.tcs'
Expect []
* Run 0 (time 9.578160)
  0: a - b == 0
  1: -b*q + b*s - x == 0
  2: -b*p + b*rvu + y == 0
  3: -p*s + q*rvu + 1 == 0
* Run 1 (time 4.417597)
  0: -a + b == 0
  1: -a*q + a*s - x == 0
  2: -a*p + a*rvu + y == 0
  3: -p*s + q*rvu + 1 == 0
TIME AVG 2.2 (../invgen/Traces/NLA/multi_locs/euclidex2.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/euclidex3.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 137 traces
dig:Info:Refine 5 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: b*d - v == 0
  1: -p*x - rvu*y + a == 0
  2: q*x + s*y - b == 0
  3: b*k - p*x - rvu*y + c == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 137 traces
dig:Info:Refine 5 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: b*d - v == 0
  1: q*x + s*y - b == 0
  2: p*x + rvu*y - a == 0
  3: b*k - a + c == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex3.l0.tcs'
Expect []
* Run 0 (time 10.734012)
  0: b*d - v == 0
  1: -p*x - rvu*y + a == 0
  2: q*x + s*y - b == 0
  3: b*k - p*x - rvu*y + c == 0
* Run 1 (time 11.237697)
  0: b*d - v == 0
  1: q*x + s*y - b == 0
  2: p*x + rvu*y - a == 0
  3: b*k - a + c == 0
TIME AVG 5.6 (../invgen/Traces/NLA/multi_locs/euclidex3.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/euclidex3.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 68 traces
dig:Info:Refine 11 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: b^2 == 0
  1: q*x + s*y == 0
  2: p*x + rvu*y - a == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 68 traces
dig:Info:Refine 11 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: b == 0
  1: q*x + s*y == 0
  2: p*x + rvu*y - a == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex3.l1.tcs'
Expect []
* Run 0 (time 3.422360)
  0: b^2 == 0
  1: q*x + s*y == 0
  2: p*x + rvu*y - a == 0
* Run 1 (time 2.836749)
  0: b == 0
  1: q*x + s*y == 0
  2: p*x + rvu*y - a == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/euclidex3.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/fermat1.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 12 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -2*R + u - 1 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 12 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -2*R + u - 1 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/fermat1.l0.tcs'
Expect []
* Run 0 (time 0.909730)
  0: -2*R + u - 1 == 0
* Run 1 (time 0.983374)
  0: -2*R + u - 1 == 0
TIME AVG 0.5 (../invgen/Traces/NLA/multi_locs/fermat1.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/fermat1.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 19 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -2*R + u - 1 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 19 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -2*R + u - 1 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/fermat1.l1.tcs'
Expect []
* Run 0 (time 1.168331)
  0: -2*R + u - 1 == 0
* Run 1 (time 6.321780)
  0: -2*R + u - 1 == 0
TIME AVG 3.2 (../invgen/Traces/NLA/multi_locs/fermat1.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/fermat2.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/fermat2.l0.tcs'
Expect []
* Run 0 (time 0.535643)
* Run 1 (time 0.659924)
TIME AVG 0.3 (../invgen/Traces/NLA/multi_locs/fermat2.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/fermat2.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 18 candidate invariants
dig:Info:Detected invariants for Eqt:

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 19 candidate invariants
dig:Info:Detected invariants for Eqt:


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/fermat2.l1.tcs'
Expect []
* Run 0 (time 0.742430)
* Run 1 (time 0.448880)
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/fermat2.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/freire1.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: rvu^2 - a - rvu + 2*x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: rvu^2 - a - rvu + 2*x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/freire1.l0.tcs'
Expect []
* Run 0 (time 0.212925)
  0: rvu^2 - a - rvu + 2*x == 0
* Run 1 (time 0.198758)
  0: rvu^2 - a - rvu + 2*x == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/freire1.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/freire1.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: rvu^2 - a - rvu + 2*x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: rvu^2 - a - rvu + 2*x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/freire1.l1.tcs'
Expect []
* Run 0 (time 0.149832)
  0: rvu^2 - a - rvu + 2*x == 0
* Run 1 (time 0.162295)
  0: rvu^2 - a - rvu + 2*x == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/freire1.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/freire2.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 53 traces
dig:Info:Refine 13 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -3*rvu^2 + s - 1/4 == 0
  1: -9/4*rvu^2 + 1/2*rvu*s - 3/2*a + rvu + 3/2*x - 3/8 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 53 traces
dig:Info:Refine 13 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -3*rvu^2 + s - 1/4 == 0
  1: rvu^3 - 3/2*rvu^2 - a + 3/4*rvu + x - 1/4 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/freire2.l0.tcs'
Expect []
* Run 0 (time 3.811266)
  0: -3*rvu^2 + s - 1/4 == 0
  1: -9/4*rvu^2 + 1/2*rvu*s - 3/2*a + rvu + 3/2*x - 3/8 == 0
* Run 1 (time 3.429003)
  0: -3*rvu^2 + s - 1/4 == 0
  1: rvu^3 - 3/2*rvu^2 - a + 3/4*rvu + x - 1/4 == 0
TIME AVG 1.7 (../invgen/Traces/NLA/multi_locs/freire2.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/freire2.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 53 traces
dig:Info:Refine 13 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -3*rvu^2 + s - 1/4 == 0
  1: -9/4*rvu^2 + 1/2*rvu*s - 3/2*a + rvu + 3/2*x - 3/8 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 53 traces
dig:Info:Refine 13 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -3*rvu^2 + s - 1/4 == 0
  1: -9/4*rvu^2 + 1/2*rvu*s - 3/2*a + rvu + 3/2*x - 3/8 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/freire2.l1.tcs'
Expect []
* Run 0 (time 3.553518)
  0: -3*rvu^2 + s - 1/4 == 0
  1: -9/4*rvu^2 + 1/2*rvu*s - 3/2*a + rvu + 3/2*x - 3/8 == 0
* Run 1 (time 3.328237)
  0: -3*rvu^2 + s - 1/4 == 0
  1: -9/4*rvu^2 + 1/2*rvu*s - 3/2*a + rvu + 3/2*x - 3/8 == 0
TIME AVG 1.7 (../invgen/Traces/NLA/multi_locs/freire2.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/geo1.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: x*z - x - y + 1 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: x*z - x - y + 1 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo1.l0.tcs'
Expect []
* Run 0 (time 0.068161)
  0: x*z - x - y + 1 == 0
* Run 1 (time 0.063046)
  0: x*z - x - y + 1 == 0
TIME AVG 0.0 (../invgen/Traces/NLA/multi_locs/geo1.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/geo1.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 4 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -x + y - 1 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 4 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -x + y - 1 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo1.l1.tcs'
Expect []
* Run 0 (time 0.150831)
  0: -x + y - 1 == 0
* Run 1 (time 0.166051)
  0: -x + y - 1 == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/geo1.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/geo2.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 23 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -x*z + y*z + x - 1 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 23 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -x*z + y*z + x - 1 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo2.l0.tcs'
Expect []
* Run 0 (time 0.137867)
  0: -x*z + y*z + x - 1 == 0
* Run 1 (time 0.141305)
  0: -x*z + y*z + x - 1 == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/geo2.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/geo2.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 23 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -x*z + y*z + x - 1 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 23 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -x*z + y*z + x - 1 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo2.l1.tcs'
Expect []
* Run 0 (time 0.094918)
  0: -x*z + y*z + x - 1 == 0
* Run 1 (time 0.102636)
  0: -x*z + y*z + x - 1 == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/geo2.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/geo3.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 84 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -a*y*z + x*z + a - x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 84 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a*y*z - x*z - a + x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo3.l0.tcs'
Expect []
* Run 0 (time 2.549773)
  0: -a*y*z + x*z + a - x == 0
* Run 1 (time 2.740078)
  0: a*y*z - x*z - a + x == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/geo3.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/geo3.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 84 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a*y*z - x*z - a + x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 84 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -a*y*z + x*z + a - x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo3.l1.tcs'
Expect []
* Run 0 (time 2.391567)
  0: a*y*z - x*z - a + x == 0
* Run 1 (time 2.489583)
  0: -a*y*z + x*z + a - x == 0
TIME AVG 1.2 (../invgen/Traces/NLA/multi_locs/geo3.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/hard.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 3 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: D*p - d1 == 0
  1: D*q - A + rvu == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 3 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: D*p - d1 == 0
  1: D*q - A + rvu == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/hard.l0.tcs'
Expect []
* Run 0 (time 0.990480)
  0: D*p - d1 == 0
  1: D*q - A + rvu == 0
* Run 1 (time 0.983316)
  0: D*p - d1 == 0
  1: D*q - A + rvu == 0
TIME AVG 0.5 (../invgen/Traces/NLA/multi_locs/hard.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/hard.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 14 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -D^2 + d1^2 == 0
  1: -D^2 + D*d1 == 0
  2: p - 1 == 0
  3: D*q - A + rvu == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 14 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -D^2 + d1^2 == 0
  1: -D^2 + D*d1 == 0
  2: p - 1 == 0
  3: D*q - A + rvu == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/hard.l1.tcs'
Expect []
* Run 0 (time 2.812907)
  0: -D^2 + d1^2 == 0
  1: -D^2 + D*d1 == 0
  2: p - 1 == 0
  3: D*q - A + rvu == 0
* Run 1 (time 2.700641)
  0: -D^2 + d1^2 == 0
  1: -D^2 + D*d1 == 0
  2: p - 1 == 0
  3: D*q - A + rvu == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/hard.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/hard.l2.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 14 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: q == 0
  1: D*p - d1 == 0
  2: -A + rvu == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 14 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: q == 0
  1: D*p - d1 == 0
  2: -A + rvu == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/hard.l2.tcs'
Expect []
* Run 0 (time 2.596618)
  0: q == 0
  1: D*p - d1 == 0
  2: -A + rvu == 0
* Run 1 (time 2.781376)
  0: q == 0
  1: D*p - d1 == 0
  2: -A + rvu == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/hard.l2.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/knuth.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 248 traces
dig:Info:Refine 44 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -1/4*d^2*q - d*k + 1/2*d*q + d*rvu + 2*nvu - 2*rvu == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 248 traces
dig:Info:Refine 43 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -k*t + t^2 == 0
  1: d*k - d*t - d1*k + d1*t == 0
  2: d^2*q + 4*d*k - 2*d*q - 4*d*rvu - 8*nvu + 8*rvu == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/knuth.l0.tcs'
Expect []
* Run 0 (time 67.476244)
  0: -1/4*d^2*q - d*k + 1/2*d*q + d*rvu + 2*nvu - 2*rvu == 0
* Run 1 (time 69.847847)
  0: -k*t + t^2 == 0
  1: d*k - d*t - d1*k + d1*t == 0
  2: d^2*q + 4*d*k - 2*d*q - 4*d*rvu - 8*nvu + 8*rvu == 0
TIME AVG 34.9 (../invgen/Traces/NLA/multi_locs/knuth.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/knuth.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 248 traces
dig:Info:Refine 33 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -k*t + t^2 == 0
  1: -d^2*k + d^2*t + d1^2*k - d1^2*t == 0
  2: d*d1*k - d*d1*t - d1^2*k + d1^2*t == 0
  3: d^2*q + 4*d*k - 2*d*q - 4*d*rvu - 8*nvu + 8*rvu == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 248 traces
dig:Info:Refine 36 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: k*t - t^2 == 0
  1: -d*k^2 + d*t^2 + d1*k^2 - d1*k*t == 0
  2: d^2*q + 4*d*k - 2*d*q - 4*d*rvu - 8*nvu + 8*rvu == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/knuth.l1.tcs'
Expect []
* Run 0 (time 46.144468)
  0: -k*t + t^2 == 0
  1: -d^2*k + d^2*t + d1^2*k - d1^2*t == 0
  2: d*d1*k - d*d1*t - d1^2*k + d1^2*t == 0
  3: d^2*q + 4*d*k - 2*d*q - 4*d*rvu - 8*nvu + 8*rvu == 0
* Run 1 (time 42.795097)
  0: k*t - t^2 == 0
  1: -d*k^2 + d*t^2 + d1*k^2 - d1*k*t == 0
  2: d^2*q + 4*d*k - 2*d*q - 4*d*rvu - 8*nvu + 8*rvu == 0
TIME AVG 21.4 (../invgen/Traces/NLA/multi_locs/knuth.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/lcm1.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -a*b + u*x + v*y == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -a*b + u*x + v*y == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/lcm1.l0.tcs'
Expect []
* Run 0 (time 0.493827)
  0: -a*b + u*x + v*y == 0
* Run 1 (time 0.516707)
  0: -a*b + u*x + v*y == 0
TIME AVG 0.3 (../invgen/Traces/NLA/multi_locs/lcm1.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/lcm1.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 54 traces
dig:Info:Refine 16 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -a*b + rvu*x == 0
  1: x - y == 0
  2: -rvu + u + v == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 54 traces
dig:Info:Refine 16 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -a*b + rvu*x == 0
  1: -x + y == 0
  2: -rvu + u + v == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/lcm1.l1.tcs'
Expect []
* Run 0 (time 3.642042)
  0: -a*b + rvu*x == 0
  1: x - y == 0
  2: -rvu + u + v == 0
* Run 1 (time 4.219587)
  0: -a*b + rvu*x == 0
  1: -x + y == 0
  2: -rvu + u + v == 0
TIME AVG 2.1 (../invgen/Traces/NLA/multi_locs/lcm1.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/lcm2.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -2*a*b + u*x + v*y == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 42 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -2*a*b + u*x + v*y == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/lcm2.l0.tcs'
Expect []
* Run 0 (time 0.814195)
  0: -2*a*b + u*x + v*y == 0
* Run 1 (time 0.767432)
  0: -2*a*b + u*x + v*y == 0
TIME AVG 0.4 (../invgen/Traces/NLA/multi_locs/lcm2.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/lcm2.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 54 traces
dig:Info:Refine 16 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -a*b + rvu*x == 0
  1: x - y == 0
  2: -2*rvu + u + v == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 54 traces
dig:Info:Refine 16 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -a*b + rvu*x == 0
  1: -x + y == 0
  2: -2*rvu + u + v == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/lcm2.l1.tcs'
Expect []
* Run 0 (time 4.413459)
  0: -a*b + rvu*x == 0
  1: x - y == 0
  2: -2*rvu + u + v == 0
* Run 1 (time 3.729082)
  0: -a*b + rvu*x == 0
  1: -x + y == 0
  2: -2*rvu + u + v == 0
TIME AVG 1.9 (../invgen/Traces/NLA/multi_locs/lcm2.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/mannadiv.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: x2*y1 - x1 + y2 + y3 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: x2*y1 - x1 + y2 + y3 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/mannadiv.l0.tcs'
Expect []
* Run 0 (time 0.742552)
  0: x2*y1 - x1 + y2 + y3 == 0
* Run 1 (time 0.695179)
  0: x2*y1 - x1 + y2 + y3 == 0
TIME AVG 0.3 (../invgen/Traces/NLA/multi_locs/mannadiv.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/mannadiv.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y3^2 == 0
  1: x2*y1 - x1 + y2 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y3^2 == 0
  1: x2*y1 - x1 + y2 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/mannadiv.l1.tcs'
Expect []
* Run 0 (time 1.032378)
  0: y3^2 == 0
  1: x2*y1 - x1 + y2 == 0
* Run 1 (time 1.145732)
  0: y3^2 == 0
  1: x2*y1 - x1 + y2 == 0
TIME AVG 0.6 (../invgen/Traces/NLA/multi_locs/mannadiv.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/prod4br.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 126 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a*b*p - x*y + q == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 126 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a*b*p - x*y + q == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/prod4br.l0.tcs'
Expect []
* Run 0 (time 8.608172)
  0: a*b*p - x*y + q == 0
* Run 1 (time 9.170654)
  0: a*b*p - x*y + q == 0
TIME AVG 4.6 (../invgen/Traces/NLA/multi_locs/prod4br.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/prod4br.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 126 traces
dig:Info:Refine 14 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a*b^2 == 0
  1: x*y - q == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 126 traces
dig:Info:Refine 14 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: a*b == 0
  1: x*y - q == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/prod4br.l1.tcs'
Expect []
* Run 0 (time 6.224628)
  0: a*b^2 == 0
  1: x*y - q == 0
* Run 1 (time 6.144722)
  0: a*b == 0
  1: x*y - q == 0
TIME AVG 3.1 (../invgen/Traces/NLA/multi_locs/prod4br.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/prodbin.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -a*b + x*y + z == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -a*b + x*y + z == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/prodbin.l0.tcs'
Expect []
* Run 0 (time 0.354877)
  0: -a*b + x*y + z == 0
* Run 1 (time 0.329739)
  0: -a*b + x*y + z == 0
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/prodbin.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/prodbin.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y == 0
  1: a*b - z == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^2 == 0
  1: a*b - z == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/prodbin.l1.tcs'
Expect []
* Run 0 (time 1.060681)
  0: y == 0
  1: a*b - z == 0
* Run 1 (time 1.191327)
  0: y^2 == 0
  1: a*b - z == 0
TIME AVG 0.6 (../invgen/Traces/NLA/multi_locs/prodbin.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps1.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 4 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -x + y == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 4 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -x + y == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps1.l0.tcs'
Expect []
* Run 0 (time 0.510844)
  0: -x + y == 0
* Run 1 (time 0.493772)
  0: -x + y == 0
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/ps1.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps1.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -k + x == 0
  1: -k + y == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 7 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -k + x == 0
  1: -k + y == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps1.l1.tcs'
Expect []
* Run 0 (time 0.639122)
  0: -k + x == 0
  1: -k + y == 0
* Run 1 (time 0.641210)
  0: -k + x == 0
  1: -k + y == 0
TIME AVG 0.3 (../invgen/Traces/NLA/multi_locs/ps1.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps2.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^2 - 2*x + y == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^2 - 2*x + y == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps2.l0.tcs'
Expect []
* Run 0 (time 0.143679)
  0: y^2 - 2*x + y == 0
* Run 1 (time 0.139834)
  0: y^2 - 2*x + y == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/ps2.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps2.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 5 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -k + y == 0
  1: y^2 + k - 2*x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 15 traces
dig:Info:Refine 5 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -k + y == 0
  1: y^2 + k - 2*x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps2.l1.tcs'
Expect []
* Run 0 (time 0.227513)
  0: -k + y == 0
  1: y^2 + k - 2*x == 0
* Run 1 (time 0.227882)
  0: -k + y == 0
  1: y^2 + k - 2*x == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/ps2.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps3.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 30 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^3 + 3/2*y^2 - 3*x + 1/2*y == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 30 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^3 + 3/2*y^2 - 3*x + 1/2*y == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps3.l0.tcs'
Expect []
* Run 0 (time 0.280095)
  0: y^3 + 3/2*y^2 - 3*x + 1/2*y == 0
* Run 1 (time 0.299273)
  0: y^3 + 3/2*y^2 - 3*x + 1/2*y == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/ps3.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps3.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 30 traces
dig:Info:Refine 11 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -k^2 + k*y == 0
  1: -k^2 + y^2 == 0
  2: k^3 + 3/2*k^2 + 1/2*k - 3*x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 30 traces
dig:Info:Refine 11 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -k^2 + k*y == 0
  1: -k^2 + y^2 == 0
  2: k^3 + 3/2*k^2 + 1/2*k - 3*x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps3.l1.tcs'
Expect []
* Run 0 (time 0.468295)
  0: -k^2 + k*y == 0
  1: -k^2 + y^2 == 0
  2: k^3 + 3/2*k^2 + 1/2*k - 3*x == 0
* Run 1 (time 0.480073)
  0: -k^2 + k*y == 0
  1: -k^2 + y^2 == 0
  2: k^3 + 3/2*k^2 + 1/2*k - 3*x == 0
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/ps3.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps4.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 53 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^4 + 2*y^3 + y^2 - 4*x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 53 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^4 + 2*y^3 + y^2 - 4*x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps4.l0.tcs'
Expect []
* Run 0 (time 0.811916)
  0: y^4 + 2*y^3 + y^2 - 4*x == 0
* Run 1 (time 0.843541)
  0: y^4 + 2*y^3 + y^2 - 4*x == 0
TIME AVG 0.4 (../invgen/Traces/NLA/multi_locs/ps4.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps4.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 53 traces
dig:Info:Refine 21 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -k^3 + y^3 == 0
  1: k^4 + 2*k^3 + k^2 - 4*x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 53 traces
dig:Info:Refine 21 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -k^3 + y^3 == 0
  1: k^4 + 2*k^3 + k^2 - 4*x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps4.l1.tcs'
Expect []
* Run 0 (time 1.399376)
  0: -k^3 + y^3 == 0
  1: k^4 + 2*k^3 + k^2 - 4*x == 0
* Run 1 (time 1.398881)
  0: -k^3 + y^3 == 0
  1: k^4 + 2*k^3 + k^2 - 4*x == 0
TIME AVG 0.7 (../invgen/Traces/NLA/multi_locs/ps4.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps5.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 84 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^5 + 5/2*y^4 + 5/3*y^3 - 5*x - 1/6*y == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 84 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^5 + 5/2*y^4 + 5/3*y^3 - 5*x - 1/6*y == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps5.l0.tcs'
Expect []
* Run 0 (time 2.508805)
  0: y^5 + 5/2*y^4 + 5/3*y^3 - 5*x - 1/6*y == 0
* Run 1 (time 2.619825)
  0: y^5 + 5/2*y^4 + 5/3*y^3 - 5*x - 1/6*y == 0
TIME AVG 1.3 (../invgen/Traces/NLA/multi_locs/ps5.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps5.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 42 traces
dig_miscs:Warn:eqts 42 <= unknown coefs 56
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for Eqt:

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 42 traces
dig_miscs:Warn:eqts 42 <= unknown coefs 56
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for Eqt:


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps5.l1.tcs'
Expect []
* Run 0 (time 0.060818)
* Run 1 (time 0.065634)
TIME AVG 0.0 (../invgen/Traces/NLA/multi_locs/ps5.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps6.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 126 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^6 + 3*y^5 + 5/2*y^4 - 1/2*y^2 - 6*x == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 126 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^6 + 3*y^5 + 5/2*y^4 - 1/2*y^2 - 6*x == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps6.l0.tcs'
Expect []
* Run 0 (time 8.418140)
  0: y^6 + 3*y^5 + 5/2*y^4 - 1/2*y^2 - 6*x == 0
* Run 1 (time 8.083366)
  0: y^6 + 3*y^5 + 5/2*y^4 - 1/2*y^2 - 6*x == 0
TIME AVG 4.0 (../invgen/Traces/NLA/multi_locs/ps6.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps6.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 40 traces
dig_miscs:Warn:eqts 40 <= unknown coefs 84
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for Eqt:

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 40 traces
dig_miscs:Warn:eqts 40 <= unknown coefs 84
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for Eqt:


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps6.l1.tcs'
Expect []
* Run 0 (time 0.112781)
* Run 1 (time 0.111475)
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/ps6.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps7.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 180 traces
dig:Info:Refine 14 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^7 + 7/2*y^6 + 7/2*y^5 - 7/6*y^3 - 7*x + 1/6*y == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 180 traces
dig:Info:Refine 15 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: y^7 + 7/2*y^6 + 7/2*y^5 - 7/6*y^3 - 7*x + 1/6*y == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps7.l0.tcs'
Expect []
* Run 0 (time 27.903965)
  0: y^7 + 7/2*y^6 + 7/2*y^5 - 7/6*y^3 - 7*x + 1/6*y == 0
* Run 1 (time 25.364050)
  0: y^7 + 7/2*y^6 + 7/2*y^5 - 7/6*y^3 - 7*x + 1/6*y == 0
TIME AVG 12.7 (../invgen/Traces/NLA/multi_locs/ps7.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/ps7.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 27 traces
dig_miscs:Warn:eqts 27 <= unknown coefs 120
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for Eqt:

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 27 traces
dig_miscs:Warn:eqts 27 <= unknown coefs 120
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for Eqt:


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps7.l1.tcs'
Expect []
* Run 0 (time 0.156940)
* Run 1 (time 0.160689)
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/ps7.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/sqrt1.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 23 traces
dig:Info:Refine 6 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -2*a + t - 1 == 0
  1: t^2 + 4*a - 4*s + 3 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 23 traces
dig:Info:Refine 6 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -2*a + t - 1 == 0
  1: -a^2 - 2*a*s + s*t - 2*a - 1 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/sqrt1.l0.tcs'
Expect []
* Run 0 (time 1.076187)
  0: -2*a + t - 1 == 0
  1: t^2 + 4*a - 4*s + 3 == 0
* Run 1 (time 1.170828)
  0: -2*a + t - 1 == 0
  1: -a^2 - 2*a*s + s*t - 2*a - 1 == 0
TIME AVG 0.6 (../invgen/Traces/NLA/multi_locs/sqrt1.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/sqrt1.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 23 traces
dig:Info:Refine 6 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: -2*a + t - 1 == 0
  1: t^2 + 4*a - 4*s + 3 == 0

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 23 traces
dig:Info:Refine 6 candidate invariants
dig:Info:Detected invariants for Eqt:
  0: t^2 - 4*s + 2*t + 1 == 0
  1: a - 1/2*t + 1/2 == 0


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/sqrt1.l1.tcs'
Expect []
* Run 0 (time 0.971879)
  0: -2*a + t - 1 == 0
  1: t^2 + 4*a - 4*s + 3 == 0
* Run 1 (time 0.943845)
  0: t^2 - 4*s + 2*t + 1 == 0
  1: a - 1/2*t + 1/2 == 0
TIME AVG 0.5 (../invgen/Traces/NLA/multi_locs/sqrt1.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/wensley.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 54 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig_miscs:Warn:set tcs2 to 1000
dig:Info:Compute candidate invariants over 54 traces
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for Eqt:


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/wensley.l0.tcs'
Expect []
* Run 0 (time 0.663173)
* Run 1 (time 0.666780)
TIME AVG 0.3 (../invgen/Traces/NLA/multi_locs/wensley.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/wensley.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 54 traces
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for Eqt:

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 54 traces
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for Eqt:


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/wensley.l1.tcs'
Expect []
* Run 0 (time 0.718309)
* Run 1 (time 0.753014)
TIME AVG 0.4 (../invgen/Traces/NLA/multi_locs/wensley.l1.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/z3sqrt.l0.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for Eqt:


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/z3sqrt.l0.tcs'
Expect []
* Run 0 (time 0.213420)
* Run 1 (time 0.202385)
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/z3sqrt.l0.tcs)


***** Generate Invs From File '../invgen/Traces/NLA/multi_locs/z3sqrt.l1.tcs' *****


*** Run 0 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for Eqt:

*** Run 1 ***

dig:Info:*** Eqt ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 32 traces
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for Eqt:


SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/z3sqrt.l1.tcs'
Expect []
* Run 0 (time 0.192648)
* Run 1 (time 0.202935)
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/z3sqrt.l1.tcs)



***** BENCHMARK SUMMARY (inv_typ "eqt")*****




SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/cohencu.l0.tcs'
Expect []
* Run 0 (time 11.279923)
  0: nvu^3 - x == 0
  1: -6*nvu + z - 6 == 0
  2: nvu^2 + nvu - 1/3*y + 1/3 == 0
* Run 1 (time 9.789675)
  0: nvu^3 - x == 0
  1: -6*nvu + z - 6 == 0
  2: nvu^2 + nvu - 1/3*y + 1/3 == 0
TIME AVG 4.9 (../invgen/Traces/NLA/multi_locs/cohencu.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/cohencu.l1.tcs'
Expect []
* Run 0 (time 11.901062)
  0: nvu^3 - x == 0
  1: -a + nvu - 1 == 0
  2: -6*a + z - 12 == 0
  3: a^2 + 3*a - 1/3*y + 7/3 == 0
* Run 1 (time 12.321128)
  0: nvu^3 - x == 0
  1: -a + nvu - 1 == 0
  2: -6*a + z - 12 == 0
  3: a^2 + 3*a - 1/3*y + 7/3 == 0
TIME AVG 6.2 (../invgen/Traces/NLA/multi_locs/cohencu.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/cohendiv.l0.tcs'
Expect []
* Run 0 (time 1.019851)
  0: a*y - b == 0
  1: q*y + rvu - x == 0
* Run 1 (time 1.108844)
  0: a*y - b == 0
  1: -q*y - rvu + x == 0
TIME AVG 0.6 (../invgen/Traces/NLA/multi_locs/cohendiv.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/cohendiv.l1.tcs'
Expect []
* Run 0 (time 1.087127)
  0: a*y - b == 0
  1: q*y + rvu - x == 0
* Run 1 (time 6.235371)
  0: a*y - b == 0
  1: -q*y - rvu + x == 0
TIME AVG 3.1 (../invgen/Traces/NLA/multi_locs/cohendiv.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/cohendiv.l2.tcs'
Expect []
* Run 0 (time 0.250857)
  0: q*y + rvu - x == 0
* Run 1 (time 0.284738)
  0: q*y + rvu - x == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/cohendiv.l2.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/dijkstra.l0.tcs'
Expect []
* Run 0 (time 0.421344)
  0: -nvu*q + p^2 + q*rvu == 0
* Run 1 (time 0.446366)
  0: -nvu*q + p^2 + q*rvu == 0
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/dijkstra.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/dijkstra.l1.tcs'
Expect []
* Run 0 (time 13.114113)
  0: q - 1 == 0
  1: p^2 - nvu + rvu == 0
  2: -1/4*h^2 + h*p - nvu + rvu + 1/4 == 0
* Run 1 (time 2.809419)
  0: q - 1 == 0
  1: p^2 - nvu + rvu == 0
  2: -1/4*h^2 + h*p - nvu + rvu + 1/4 == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/dijkstra.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/dijkstra.l2.tcs'
Expect []
* Run 0 (time 2.484213)
  0: p == 0
  1: h^2 == 0
  2: -nvu + rvu == 0
* Run 1 (time 2.375525)
  0: p == 0
  1: h^2 == 0
  2: -nvu + rvu == 0
TIME AVG 1.2 (../invgen/Traces/NLA/multi_locs/dijkstra.l2.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/divbin.l0.tcs'
Expect []
* Run 0 (time 0.361717)
  0: b*q - A + rvu == 0
* Run 1 (time 0.357492)
  0: b*q - A + rvu == 0
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/divbin.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/divbin.l1.tcs'
Expect []
* Run 0 (time 1.523365)
  0: -B + b == 0
  1: B*q - A + rvu == 0
* Run 1 (time 6.655145)
  0: -B + b == 0
  1: B*q - A + rvu == 0
TIME AVG 3.3 (../invgen/Traces/NLA/multi_locs/divbin.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/divbin.l2.tcs'
Expect []
* Run 0 (time 1.872042)
  0: q == 0
  1: -A + rvu == 0
* Run 1 (time 1.989212)
  0: q == 0
  1: -A + rvu == 0
TIME AVG 1.0 (../invgen/Traces/NLA/multi_locs/divbin.l2.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/egcd.l0.tcs'
Expect []
* Run 0 (time 2.433864)
  0: A*i + B*j - x == 0
  1: -i*m + j*k + 1 == 0
  2: A*k + B*m - y == 0
* Run 1 (time 2.437611)
  0: A*i + B*j - x == 0
  1: -i*m + j*k + 1 == 0
  2: A*k + B*m - y == 0
TIME AVG 1.2 (../invgen/Traces/NLA/multi_locs/egcd.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/egcd.l1.tcs'
Expect []
* Run 0 (time 3.855868)
  0: -x + y == 0
  1: -j*x + m*x - A == 0
  2: -i*x + k*x + B == 0
  3: -i*m + j*k + 1 == 0
* Run 1 (time 4.040588)
  0: -x^2 + y^2 == 0
  1: -x^2 + x*y == 0
  2: -j*x + m*x - A == 0
  3: -i*x + k*x + B == 0
  4: -i*m + j*k + 1 == 0
TIME AVG 2.0 (../invgen/Traces/NLA/multi_locs/egcd.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex1.l0.tcs'
Expect []
* Run 0 (time 4.477107)
  0: q*x + s*y - b == 0
  1: p*x + rvu*y - a == 0
  2: b*k - a + c == 0
* Run 1 (time 4.287956)
  0: q*x + s*y - b == 0
  1: p*x + rvu*y - a == 0
  2: b*k - a + c == 0
TIME AVG 2.1 (../invgen/Traces/NLA/multi_locs/euclidex1.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex1.l1.tcs'
Expect []
* Run 0 (time 1.147817)
  0: b^2 == 0
* Run 1 (time 1.085477)
  0: b^2 == 0
TIME AVG 0.5 (../invgen/Traces/NLA/multi_locs/euclidex1.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex1.l2.tcs'
Expect []
* Run 0 (time 6.685469)
  0: b - c == 0
  1: q*x + s*y - c == 0
  2: p*x + rvu*y - a == 0
* Run 1 (time 7.111271)
  0: -b + c == 0
  1: q*x + s*y - b == 0
  2: p*x + rvu*y - a == 0
TIME AVG 3.6 (../invgen/Traces/NLA/multi_locs/euclidex1.l2.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex2.l0.tcs'
Expect []
* Run 0 (time 2.613702)
  0: -p*s + q*rvu + 1 == 0
  1: p*x + q*y - a == 0
  2: rvu*x + s*y - b == 0
* Run 1 (time 2.769476)
  0: a*rvu - b*p + y == 0
  1: -p*s + q*rvu + 1 == 0
  2: a*s - b*q - x == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/euclidex2.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex2.l1.tcs'
Expect []
* Run 0 (time 9.578160)
  0: a - b == 0
  1: -b*q + b*s - x == 0
  2: -b*p + b*rvu + y == 0
  3: -p*s + q*rvu + 1 == 0
* Run 1 (time 4.417597)
  0: -a + b == 0
  1: -a*q + a*s - x == 0
  2: -a*p + a*rvu + y == 0
  3: -p*s + q*rvu + 1 == 0
TIME AVG 2.2 (../invgen/Traces/NLA/multi_locs/euclidex2.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex3.l0.tcs'
Expect []
* Run 0 (time 10.734012)
  0: b*d - v == 0
  1: -p*x - rvu*y + a == 0
  2: q*x + s*y - b == 0
  3: b*k - p*x - rvu*y + c == 0
* Run 1 (time 11.237697)
  0: b*d - v == 0
  1: q*x + s*y - b == 0
  2: p*x + rvu*y - a == 0
  3: b*k - a + c == 0
TIME AVG 5.6 (../invgen/Traces/NLA/multi_locs/euclidex3.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/euclidex3.l1.tcs'
Expect []
* Run 0 (time 3.422360)
  0: b^2 == 0
  1: q*x + s*y == 0
  2: p*x + rvu*y - a == 0
* Run 1 (time 2.836749)
  0: b == 0
  1: q*x + s*y == 0
  2: p*x + rvu*y - a == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/euclidex3.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/fermat1.l0.tcs'
Expect []
* Run 0 (time 0.909730)
  0: -2*R + u - 1 == 0
* Run 1 (time 0.983374)
  0: -2*R + u - 1 == 0
TIME AVG 0.5 (../invgen/Traces/NLA/multi_locs/fermat1.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/fermat1.l1.tcs'
Expect []
* Run 0 (time 1.168331)
  0: -2*R + u - 1 == 0
* Run 1 (time 6.321780)
  0: -2*R + u - 1 == 0
TIME AVG 3.2 (../invgen/Traces/NLA/multi_locs/fermat1.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/fermat2.l0.tcs'
Expect []
* Run 0 (time 0.535643)
* Run 1 (time 0.659924)
TIME AVG 0.3 (../invgen/Traces/NLA/multi_locs/fermat2.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/fermat2.l1.tcs'
Expect []
* Run 0 (time 0.742430)
* Run 1 (time 0.448880)
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/fermat2.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/freire1.l0.tcs'
Expect []
* Run 0 (time 0.212925)
  0: rvu^2 - a - rvu + 2*x == 0
* Run 1 (time 0.198758)
  0: rvu^2 - a - rvu + 2*x == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/freire1.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/freire1.l1.tcs'
Expect []
* Run 0 (time 0.149832)
  0: rvu^2 - a - rvu + 2*x == 0
* Run 1 (time 0.162295)
  0: rvu^2 - a - rvu + 2*x == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/freire1.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/freire2.l0.tcs'
Expect []
* Run 0 (time 3.811266)
  0: -3*rvu^2 + s - 1/4 == 0
  1: -9/4*rvu^2 + 1/2*rvu*s - 3/2*a + rvu + 3/2*x - 3/8 == 0
* Run 1 (time 3.429003)
  0: -3*rvu^2 + s - 1/4 == 0
  1: rvu^3 - 3/2*rvu^2 - a + 3/4*rvu + x - 1/4 == 0
TIME AVG 1.7 (../invgen/Traces/NLA/multi_locs/freire2.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/freire2.l1.tcs'
Expect []
* Run 0 (time 3.553518)
  0: -3*rvu^2 + s - 1/4 == 0
  1: -9/4*rvu^2 + 1/2*rvu*s - 3/2*a + rvu + 3/2*x - 3/8 == 0
* Run 1 (time 3.328237)
  0: -3*rvu^2 + s - 1/4 == 0
  1: -9/4*rvu^2 + 1/2*rvu*s - 3/2*a + rvu + 3/2*x - 3/8 == 0
TIME AVG 1.7 (../invgen/Traces/NLA/multi_locs/freire2.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo1.l0.tcs'
Expect []
* Run 0 (time 0.068161)
  0: x*z - x - y + 1 == 0
* Run 1 (time 0.063046)
  0: x*z - x - y + 1 == 0
TIME AVG 0.0 (../invgen/Traces/NLA/multi_locs/geo1.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo1.l1.tcs'
Expect []
* Run 0 (time 0.150831)
  0: -x + y - 1 == 0
* Run 1 (time 0.166051)
  0: -x + y - 1 == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/geo1.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo2.l0.tcs'
Expect []
* Run 0 (time 0.137867)
  0: -x*z + y*z + x - 1 == 0
* Run 1 (time 0.141305)
  0: -x*z + y*z + x - 1 == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/geo2.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo2.l1.tcs'
Expect []
* Run 0 (time 0.094918)
  0: -x*z + y*z + x - 1 == 0
* Run 1 (time 0.102636)
  0: -x*z + y*z + x - 1 == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/geo2.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo3.l0.tcs'
Expect []
* Run 0 (time 2.549773)
  0: -a*y*z + x*z + a - x == 0
* Run 1 (time 2.740078)
  0: a*y*z - x*z - a + x == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/geo3.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/geo3.l1.tcs'
Expect []
* Run 0 (time 2.391567)
  0: a*y*z - x*z - a + x == 0
* Run 1 (time 2.489583)
  0: -a*y*z + x*z + a - x == 0
TIME AVG 1.2 (../invgen/Traces/NLA/multi_locs/geo3.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/hard.l0.tcs'
Expect []
* Run 0 (time 0.990480)
  0: D*p - d1 == 0
  1: D*q - A + rvu == 0
* Run 1 (time 0.983316)
  0: D*p - d1 == 0
  1: D*q - A + rvu == 0
TIME AVG 0.5 (../invgen/Traces/NLA/multi_locs/hard.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/hard.l1.tcs'
Expect []
* Run 0 (time 2.812907)
  0: -D^2 + d1^2 == 0
  1: -D^2 + D*d1 == 0
  2: p - 1 == 0
  3: D*q - A + rvu == 0
* Run 1 (time 2.700641)
  0: -D^2 + d1^2 == 0
  1: -D^2 + D*d1 == 0
  2: p - 1 == 0
  3: D*q - A + rvu == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/hard.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/hard.l2.tcs'
Expect []
* Run 0 (time 2.596618)
  0: q == 0
  1: D*p - d1 == 0
  2: -A + rvu == 0
* Run 1 (time 2.781376)
  0: q == 0
  1: D*p - d1 == 0
  2: -A + rvu == 0
TIME AVG 1.4 (../invgen/Traces/NLA/multi_locs/hard.l2.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/knuth.l0.tcs'
Expect []
* Run 0 (time 67.476244)
  0: -1/4*d^2*q - d*k + 1/2*d*q + d*rvu + 2*nvu - 2*rvu == 0
* Run 1 (time 69.847847)
  0: -k*t + t^2 == 0
  1: d*k - d*t - d1*k + d1*t == 0
  2: d^2*q + 4*d*k - 2*d*q - 4*d*rvu - 8*nvu + 8*rvu == 0
TIME AVG 34.9 (../invgen/Traces/NLA/multi_locs/knuth.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/knuth.l1.tcs'
Expect []
* Run 0 (time 46.144468)
  0: -k*t + t^2 == 0
  1: -d^2*k + d^2*t + d1^2*k - d1^2*t == 0
  2: d*d1*k - d*d1*t - d1^2*k + d1^2*t == 0
  3: d^2*q + 4*d*k - 2*d*q - 4*d*rvu - 8*nvu + 8*rvu == 0
* Run 1 (time 42.795097)
  0: k*t - t^2 == 0
  1: -d*k^2 + d*t^2 + d1*k^2 - d1*k*t == 0
  2: d^2*q + 4*d*k - 2*d*q - 4*d*rvu - 8*nvu + 8*rvu == 0
TIME AVG 21.4 (../invgen/Traces/NLA/multi_locs/knuth.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/lcm1.l0.tcs'
Expect []
* Run 0 (time 0.493827)
  0: -a*b + u*x + v*y == 0
* Run 1 (time 0.516707)
  0: -a*b + u*x + v*y == 0
TIME AVG 0.3 (../invgen/Traces/NLA/multi_locs/lcm1.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/lcm1.l1.tcs'
Expect []
* Run 0 (time 3.642042)
  0: -a*b + rvu*x == 0
  1: x - y == 0
  2: -rvu + u + v == 0
* Run 1 (time 4.219587)
  0: -a*b + rvu*x == 0
  1: -x + y == 0
  2: -rvu + u + v == 0
TIME AVG 2.1 (../invgen/Traces/NLA/multi_locs/lcm1.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/lcm2.l0.tcs'
Expect []
* Run 0 (time 0.814195)
  0: -2*a*b + u*x + v*y == 0
* Run 1 (time 0.767432)
  0: -2*a*b + u*x + v*y == 0
TIME AVG 0.4 (../invgen/Traces/NLA/multi_locs/lcm2.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/lcm2.l1.tcs'
Expect []
* Run 0 (time 4.413459)
  0: -a*b + rvu*x == 0
  1: x - y == 0
  2: -2*rvu + u + v == 0
* Run 1 (time 3.729082)
  0: -a*b + rvu*x == 0
  1: -x + y == 0
  2: -2*rvu + u + v == 0
TIME AVG 1.9 (../invgen/Traces/NLA/multi_locs/lcm2.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/mannadiv.l0.tcs'
Expect []
* Run 0 (time 0.742552)
  0: x2*y1 - x1 + y2 + y3 == 0
* Run 1 (time 0.695179)
  0: x2*y1 - x1 + y2 + y3 == 0
TIME AVG 0.3 (../invgen/Traces/NLA/multi_locs/mannadiv.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/mannadiv.l1.tcs'
Expect []
* Run 0 (time 1.032378)
  0: y3^2 == 0
  1: x2*y1 - x1 + y2 == 0
* Run 1 (time 1.145732)
  0: y3^2 == 0
  1: x2*y1 - x1 + y2 == 0
TIME AVG 0.6 (../invgen/Traces/NLA/multi_locs/mannadiv.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/prod4br.l0.tcs'
Expect []
* Run 0 (time 8.608172)
  0: a*b*p - x*y + q == 0
* Run 1 (time 9.170654)
  0: a*b*p - x*y + q == 0
TIME AVG 4.6 (../invgen/Traces/NLA/multi_locs/prod4br.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/prod4br.l1.tcs'
Expect []
* Run 0 (time 6.224628)
  0: a*b^2 == 0
  1: x*y - q == 0
* Run 1 (time 6.144722)
  0: a*b == 0
  1: x*y - q == 0
TIME AVG 3.1 (../invgen/Traces/NLA/multi_locs/prod4br.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/prodbin.l0.tcs'
Expect []
* Run 0 (time 0.354877)
  0: -a*b + x*y + z == 0
* Run 1 (time 0.329739)
  0: -a*b + x*y + z == 0
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/prodbin.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/prodbin.l1.tcs'
Expect []
* Run 0 (time 1.060681)
  0: y == 0
  1: a*b - z == 0
* Run 1 (time 1.191327)
  0: y^2 == 0
  1: a*b - z == 0
TIME AVG 0.6 (../invgen/Traces/NLA/multi_locs/prodbin.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps1.l0.tcs'
Expect []
* Run 0 (time 0.510844)
  0: -x + y == 0
* Run 1 (time 0.493772)
  0: -x + y == 0
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/ps1.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps1.l1.tcs'
Expect []
* Run 0 (time 0.639122)
  0: -k + x == 0
  1: -k + y == 0
* Run 1 (time 0.641210)
  0: -k + x == 0
  1: -k + y == 0
TIME AVG 0.3 (../invgen/Traces/NLA/multi_locs/ps1.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps2.l0.tcs'
Expect []
* Run 0 (time 0.143679)
  0: y^2 - 2*x + y == 0
* Run 1 (time 0.139834)
  0: y^2 - 2*x + y == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/ps2.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps2.l1.tcs'
Expect []
* Run 0 (time 0.227513)
  0: -k + y == 0
  1: y^2 + k - 2*x == 0
* Run 1 (time 0.227882)
  0: -k + y == 0
  1: y^2 + k - 2*x == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/ps2.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps3.l0.tcs'
Expect []
* Run 0 (time 0.280095)
  0: y^3 + 3/2*y^2 - 3*x + 1/2*y == 0
* Run 1 (time 0.299273)
  0: y^3 + 3/2*y^2 - 3*x + 1/2*y == 0
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/ps3.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps3.l1.tcs'
Expect []
* Run 0 (time 0.468295)
  0: -k^2 + k*y == 0
  1: -k^2 + y^2 == 0
  2: k^3 + 3/2*k^2 + 1/2*k - 3*x == 0
* Run 1 (time 0.480073)
  0: -k^2 + k*y == 0
  1: -k^2 + y^2 == 0
  2: k^3 + 3/2*k^2 + 1/2*k - 3*x == 0
TIME AVG 0.2 (../invgen/Traces/NLA/multi_locs/ps3.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps4.l0.tcs'
Expect []
* Run 0 (time 0.811916)
  0: y^4 + 2*y^3 + y^2 - 4*x == 0
* Run 1 (time 0.843541)
  0: y^4 + 2*y^3 + y^2 - 4*x == 0
TIME AVG 0.4 (../invgen/Traces/NLA/multi_locs/ps4.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps4.l1.tcs'
Expect []
* Run 0 (time 1.399376)
  0: -k^3 + y^3 == 0
  1: k^4 + 2*k^3 + k^2 - 4*x == 0
* Run 1 (time 1.398881)
  0: -k^3 + y^3 == 0
  1: k^4 + 2*k^3 + k^2 - 4*x == 0
TIME AVG 0.7 (../invgen/Traces/NLA/multi_locs/ps4.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps5.l0.tcs'
Expect []
* Run 0 (time 2.508805)
  0: y^5 + 5/2*y^4 + 5/3*y^3 - 5*x - 1/6*y == 0
* Run 1 (time 2.619825)
  0: y^5 + 5/2*y^4 + 5/3*y^3 - 5*x - 1/6*y == 0
TIME AVG 1.3 (../invgen/Traces/NLA/multi_locs/ps5.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps5.l1.tcs'
Expect []
* Run 0 (time 0.060818)
* Run 1 (time 0.065634)
TIME AVG 0.0 (../invgen/Traces/NLA/multi_locs/ps5.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps6.l0.tcs'
Expect []
* Run 0 (time 8.418140)
  0: y^6 + 3*y^5 + 5/2*y^4 - 1/2*y^2 - 6*x == 0
* Run 1 (time 8.083366)
  0: y^6 + 3*y^5 + 5/2*y^4 - 1/2*y^2 - 6*x == 0
TIME AVG 4.0 (../invgen/Traces/NLA/multi_locs/ps6.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps6.l1.tcs'
Expect []
* Run 0 (time 0.112781)
* Run 1 (time 0.111475)
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/ps6.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps7.l0.tcs'
Expect []
* Run 0 (time 27.903965)
  0: y^7 + 7/2*y^6 + 7/2*y^5 - 7/6*y^3 - 7*x + 1/6*y == 0
* Run 1 (time 25.364050)
  0: y^7 + 7/2*y^6 + 7/2*y^5 - 7/6*y^3 - 7*x + 1/6*y == 0
TIME AVG 12.7 (../invgen/Traces/NLA/multi_locs/ps7.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/ps7.l1.tcs'
Expect []
* Run 0 (time 0.156940)
* Run 1 (time 0.160689)
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/ps7.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/sqrt1.l0.tcs'
Expect []
* Run 0 (time 1.076187)
  0: -2*a + t - 1 == 0
  1: t^2 + 4*a - 4*s + 3 == 0
* Run 1 (time 1.170828)
  0: -2*a + t - 1 == 0
  1: -a^2 - 2*a*s + s*t - 2*a - 1 == 0
TIME AVG 0.6 (../invgen/Traces/NLA/multi_locs/sqrt1.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/sqrt1.l1.tcs'
Expect []
* Run 0 (time 0.971879)
  0: -2*a + t - 1 == 0
  1: t^2 + 4*a - 4*s + 3 == 0
* Run 1 (time 0.943845)
  0: t^2 - 4*s + 2*t + 1 == 0
  1: a - 1/2*t + 1/2 == 0
TIME AVG 0.5 (../invgen/Traces/NLA/multi_locs/sqrt1.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/wensley.l0.tcs'
Expect []
* Run 0 (time 0.663173)
* Run 1 (time 0.666780)
TIME AVG 0.3 (../invgen/Traces/NLA/multi_locs/wensley.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/wensley.l1.tcs'
Expect []
* Run 0 (time 0.718309)
* Run 1 (time 0.753014)
TIME AVG 0.4 (../invgen/Traces/NLA/multi_locs/wensley.l1.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/z3sqrt.l0.tcs'
Expect []
* Run 0 (time 0.213420)
* Run 1 (time 0.202385)
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/z3sqrt.l0.tcs)



SUMMARY (inv_typ 'eqt')
Invariants Generated from '../invgen/Traces/NLA/multi_locs/z3sqrt.l1.tcs'
Expect []
* Run 0 (time 0.192648)
* Run 1 (time 0.202935)
TIME AVG 0.1 (../invgen/Traces/NLA/multi_locs/z3sqrt.l1.tcs)


4/25
sage: %attach dig_benchmark.py
sage:  benchmark_dir('../invgen/Traces/AES/Simple/', inv_typ='simple_nested', runs=2)

********** BEGIN BENCHMARK **********
Invariant Type: simple_nested
Trace Directory: ../invgen/Traces/AES/Simple/
Number of runs for each trace file: 2
********** *************** **********



***** Generate invs from file '../invgen/Traces/AES/Simple/aes_Block2State.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 1
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for NestedArray:
  0: lambda rvu,t,i1,i2: rvu[i1][i2] == t[4*i1 + i2]

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 1
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for NestedArray:
  0: lambda rvu,t,i1,i2: rvu[i1][i2] == t[4*i1 + i2]


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_Block2State.tc'
Expect ['r[i][j] + t[4i + j] = 0']
* Run 0 (time 0.519701)
  0: lambda rvu,t,i1,i2: rvu[i1][i2] == t[4*i1 + i2]
* Run 1 (time 0.234866)
  0: lambda rvu,t,i1,i2: rvu[i1][i2] == t[4*i1 + i2]
TIME AVG 0.1 (../invgen/Traces/AES/Simple/aes_Block2State.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/aes_InvShiftRows.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_InvShiftRows.tc'
Expect ['rvu = [[st[0][0], st[3][1], st[2][2], st[1][3]],[st[1][0], st[0][1], st[3][2], st[2][3]], [st[2][0], st[1][1], st[0][2], st[3][3]], [st[3][0], st[2][1], st[1][2], st[0][3]]];']
* Run 0 (time 0.081961)
* Run 1 (time 0.085814)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_InvShiftRows.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/aes_KeySetupEnc4.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 1
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for NestedArray:
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 1
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for NestedArray:
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc4.tc'
Expect ['cipherKey[4i+j] - rk[i][j] = 0']
* Run 0 (time 0.170942)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
* Run 1 (time 0.171712)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
TIME AVG 0.1 (../invgen/Traces/AES/Simple/aes_KeySetupEnc4.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/aes_KeySetupEnc4_disj.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc4_disj.tc'
Expect ['cipherKey[4i+j] - rk[i][j] = 0 for i=0..4,j=0..4']
* Run 0 (time 0.018859)
* Run 1 (time 0.022001)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_KeySetupEnc4_disj.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/aes_KeySetupEnc4_else.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc4_else.tc'
Expect []
* Run 0 (time 0.005376)
* Run 1 (time 0.007102)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_KeySetupEnc4_else.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/aes_KeySetupEnc6.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 1
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for NestedArray:
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 1
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for NestedArray:
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc6.tc'
Expect ['cipherKey[4i+j] - rk[i][j] = 0']
* Run 0 (time 0.233987)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
* Run 1 (time 0.226881)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
TIME AVG 0.1 (../invgen/Traces/AES/Simple/aes_KeySetupEnc6.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/aes_KeySetupEnc6_disj.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc6_disj.tc'
Expect ['cipherKey[4i+j] - rk[i][j] = 0 for i=0..6,j=0..4']
* Run 0 (time 0.018510)
* Run 1 (time 0.021634)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_KeySetupEnc6_disj.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/aes_KeySetupEnc8.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 1
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for NestedArray:
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 1
dig:Info:Refine 1 candidate invariants
dig:Info:Detected invariants for NestedArray:
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc8.tc'
Expect ['cipherKey[6i+j] - rk[i][j] = 0']
* Run 0 (time 0.486429)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
* Run 1 (time 0.390748)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
TIME AVG 0.2 (../invgen/Traces/AES/Simple/aes_KeySetupEnc8.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/aes_RotWord.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_RotWord.tc'
Expect ['rvu = [w[1],w[2],w[3],w[0]]']
* Run 0 (time 0.063490)
* Run 1 (time 0.051934)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_RotWord.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/aes_ShiftRows.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_ShiftRows.tc'
Expect ['rvu = [[st[0][0], st[1][1], st[2][2], st[3][3]], [st[1][0], st[2][1], st[3][2], st[0][3]], [st[2][0], st[3][1], st[0][2], st[1][3]], [st[3][0], st[0][1], st[1][2], st[2][3]]]']
* Run 0 (time 0.081922)
* Run 1 (time 0.085692)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_ShiftRows.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/aes_State2Block.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_State2Block.tc'
Expect ['r[4i+j] - st[i][j] = 0']
* Run 0 (time 0.083199)
* Run 1 (time 0.082234)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_State2Block.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/paper_multidim.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/paper_multidim.tc'
Expect ['A[i] - 7B[2i] - 3i == 0']
* Run 0 (time 0.001569)
* Run 1 (time 0.003183)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/paper_multidim.tc)


***** Generate invs from file '../invgen/Traces/AES/Simple/test_1.tc' *****


*** Run 0 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:

*** Run 1 ***

dig:Info:*** NestedArray ***
dig:Info:Select traces
dig:Info:Compute candidate invariants over 1 traces
Preprocessing arrays
Generate array expressions (nestings)
* Find valid nestings using reachability analysis
* Relations: 0
dig:Info:Refine 0 candidate invariants
dig:Info:Detected invariants for NestedArray:


SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/test_1.tc'
Expect []
* Run 0 (time 0.001450)
* Run 1 (time 0.003445)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/test_1.tc)



***** BENCHMARK SUMMARY (inv_typ "simple_nested")*****




SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_Block2State.tc'
Expect ['r[i][j] + t[4i + j] = 0']
* Run 0 (time 0.519701)
  0: lambda rvu,t,i1,i2: rvu[i1][i2] == t[4*i1 + i2]
* Run 1 (time 0.234866)
  0: lambda rvu,t,i1,i2: rvu[i1][i2] == t[4*i1 + i2]
TIME AVG 0.1 (../invgen/Traces/AES/Simple/aes_Block2State.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_InvShiftRows.tc'
Expect ['rvu = [[st[0][0], st[3][1], st[2][2], st[1][3]],[st[1][0], st[0][1], st[3][2], st[2][3]], [st[2][0], st[1][1], st[0][2], st[3][3]], [st[3][0], st[2][1], st[1][2], st[0][3]]];']
* Run 0 (time 0.081961)
* Run 1 (time 0.085814)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_InvShiftRows.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc4.tc'
Expect ['cipherKey[4i+j] - rk[i][j] = 0']
* Run 0 (time 0.170942)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
* Run 1 (time 0.171712)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
TIME AVG 0.1 (../invgen/Traces/AES/Simple/aes_KeySetupEnc4.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc4_disj.tc'
Expect ['cipherKey[4i+j] - rk[i][j] = 0 for i=0..4,j=0..4']
* Run 0 (time 0.018859)
* Run 1 (time 0.022001)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_KeySetupEnc4_disj.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc4_else.tc'
Expect []
* Run 0 (time 0.005376)
* Run 1 (time 0.007102)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_KeySetupEnc4_else.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc6.tc'
Expect ['cipherKey[4i+j] - rk[i][j] = 0']
* Run 0 (time 0.233987)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
* Run 1 (time 0.226881)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
TIME AVG 0.1 (../invgen/Traces/AES/Simple/aes_KeySetupEnc6.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc6_disj.tc'
Expect ['cipherKey[4i+j] - rk[i][j] = 0 for i=0..6,j=0..4']
* Run 0 (time 0.018510)
* Run 1 (time 0.021634)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_KeySetupEnc6_disj.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_KeySetupEnc8.tc'
Expect ['cipherKey[6i+j] - rk[i][j] = 0']
* Run 0 (time 0.486429)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
* Run 1 (time 0.390748)
  0: lambda rk,cipherKey,i1,i2: rk[i1][i2] == cipherKey[4*i1 + i2]
TIME AVG 0.2 (../invgen/Traces/AES/Simple/aes_KeySetupEnc8.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_RotWord.tc'
Expect ['rvu = [w[1],w[2],w[3],w[0]]']
* Run 0 (time 0.063490)
* Run 1 (time 0.051934)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_RotWord.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_ShiftRows.tc'
Expect ['rvu = [[st[0][0], st[1][1], st[2][2], st[3][3]], [st[1][0], st[2][1], st[3][2], st[0][3]], [st[2][0], st[3][1], st[0][2], st[1][3]], [st[3][0], st[0][1], st[1][2], st[2][3]]]']
* Run 0 (time 0.081922)
* Run 1 (time 0.085692)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_ShiftRows.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/aes_State2Block.tc'
Expect ['r[4i+j] - st[i][j] = 0']
* Run 0 (time 0.083199)
* Run 1 (time 0.082234)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/aes_State2Block.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/paper_multidim.tc'
Expect ['A[i] - 7B[2i] - 3i == 0']
* Run 0 (time 0.001569)
* Run 1 (time 0.003183)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/paper_multidim.tc)



SUMMARY (inv_typ 'simple_nested')
Invariants generated from '../invgen/Traces/AES/Simple/test_1.tc'
Expect []
* Run 0 (time 0.001450)
* Run 1 (time 0.003445)
TIME AVG 0.0 (../invgen/Traces/AES/Simple/test_1.tc)
