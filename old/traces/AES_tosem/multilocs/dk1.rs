

sage: dig = DIG('../invgen/Traces/AES_tosem/All/dk1.tcs',verbose=3);  _ = dig.getInvs(inv_typ='simple',seed=0)
inv_arrays:Info:2013-06-03 11:21:28.471076, Sage Version 5.9, Release Date: 2013-04-30, fermat Darwin 10.8.0 x86_64
dig_miscs:Debug:Read Info:
0. |tcs|: 100
1. vs: [A, B]
2. xinfo: 
 0. All: ['A', 'B']
 1. Assume: []
 2. Const: []
 3. Expect: []
 4. ExtFun: []
 5. ExtVar: []
 6. Global: []
 7. Input: []
 8. Output: []
inv_arrays:Debug:Seed: 0
inv_arrays:Info:*** SimpleArray ***
inv_arrays:Debug:|terms|=0, |tcs|=100
inv_arrays:Info:Select traces
inv_arrays:Info:Compute candidate invariants over 100 traces
inv_arrays:Info:Compute new traces (treating array elems as new vars)
inv_arrays:Debug:Find linear eqts over 15 array elems
inv_arrays:Info:*** Eqt ***
inv_arrays:Debug:|terms|=16, |tcs|=100
inv_arrays:Info:Select traces (note: |tcs|=|terms|=16)
dig_miscs:Debug:sample_traces: chose |tcs1|=16, |tcs2|=84 (attempted 16/100 tcs)
inv_arrays:Info:Compute candidate invariants over 16 traces
dig_miscs:Debug:Create equations from 16 traces
dig_miscs:Debug:Solve 16 (uniq) eqts for 16 unknowns
inv_arrays:Info:Refine 5 candidate invariants
refine:Debug:rrank(|ps|=5)
refine:Debug:rrank (before 5, after 5, diff 0)
refine:Debug:rfilter(|ps|=5, |tcs|=84)
refine:Debug:rfilter (before 5, after 5, diff 0)
refine:Debug:rinfer(|ps|=5)
refine:Debug:rinfer (before 5, after 5, diff 0)
inv_arrays:Info:Detected invariants for Eqt:
  0: A_0 - 2*B_1 - 10 == 0
  1: A_1 - 5*B_3 - 10 == 0
  2: A_2 - 8*B_5 - 10 == 0
  3: A_3 - 11*B_7 - 10 == 0
  4: A_4 - 14*B_9 - 10 == 0
inv_arrays:Info:Partition 5 eqts into 1 groups
inv_arrays:Debug:0. Find rels over idx from 5 eqts (group ('A', 'B'))
inv_arrays:Debug:a_solve: Assume 'A' is pivot
inv_arrays:Debug:solve 'B' with respect to pivot with |tcs|=5
dig_miscs:Debug:Create equations from 5 traces
dig_miscs:Debug:Solve 5 (uniq) eqts for 2 unknowns
dig_miscs:Debug:Create equations from 5 traces
dig_miscs:Debug:Solve 5 (uniq) eqts for 2 unknowns
inv_arrays:Debug:a_solve: Assume 'A' is pivot
inv_arrays:Debug:solve 'coef' with respect to pivot with |tcs|=5
dig_miscs:Debug:Create equations from 5 traces
dig_miscs:Debug:Solve 5 (uniq) eqts for 2 unknowns
inv_arrays:Debug:Result (pivot A): lambda A, B, A0: (A[A0]) + ((-3*A0 - 2) *B[2*A0 + 1]) + (-10) == 0
inv_arrays:Debug:a_solve: Assume 'B' is pivot
inv_arrays:Debug:solve 'A' with respect to pivot with |tcs|=5
dig_miscs:Debug:Create equations from 5 traces
dig_miscs:Debug:Solve 5 (uniq) eqts for 2 unknowns
dig_miscs:Debug:Create equations from 5 traces
dig_miscs:Debug:Solve 5 (uniq) eqts for 2 unknowns
inv_arrays:Debug:a_solve: Assume 'B' is pivot
inv_arrays:Debug:solve 'coef' with respect to pivot with |tcs|=5
dig_miscs:Debug:Create equations from 5 traces
dig_miscs:Debug:Solve 5 (uniq) eqts for 2 unknowns
inv_arrays:Debug:Result (pivot B): lambda B, A, B0: ((-2) *B[B0]) + (A[1/2*B0 - 1/2]) + (-10) == 0
inv_arrays:Info:Detected invariants for SimpleArray:
  0: ('lambda B, A, B0: ((-2) *B[B0]) + (A[1/2*B0 - 1/2]) + (-10) == 0', [{'B0': 1}, {'B0': 3}, {'B0': 5}, {'B0': 7}, {'B0': 9}])
  1: ('lambda A, B, A0: (A[A0]) + ((-3*A0 - 2) *B[2*A0 + 1]) + (-10) == 0', [{'A0': 0}, {'A0': 1}, {'A0': 2}, {'A0': 3}, {'A0': 4}])
inv_arrays:Info:Refine 2 candidate invariants
refine:Debug:rfilter(|ps|=2, |tcs|=100)
refine:Debug:rfilter (before 2, after 1, diff 1)
inv_arrays:Info:Detected invariants for SimpleArray:
  0: ('lambda A, B, A0: (A[A0]) + ((-3*A0 - 2) *B[2*A0 + 1]) + (-10) == 0', [{'A0': 0}, {'A0': 1}, {'A0': 2}, {'A0': 3}, {'A0': 4}])
