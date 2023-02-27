sage: ig = InvGen("Examples/paper_nested.tc")
*** InvGen ***
Tue May 22 13:38:24 2012
Sage Version 4.8, Release Date: 2012-01-20
Godel.local Darwin 10.8.0 x86_64
*** ReadFile ***
read 'Examples/paper_nested.tc'
number of traces (tcs) read: 1
read 'Examples/paper_nested.ext'
0. |tcs|: 1
1. |tcs2|: 0
2. vs: [A, B, C]
3. xinfo: 
 0. All: ['A', 'B', 'C']
 1. Assume: []
 2. Const: []
 3. Expect: ['A[i]=B[C[2i+1]]']
 4. ExtFun: []
 5. Global: []
 6. Input: []
 7. Output: []
Time elapsed: 0.0032 s (ReadFile)
sage: rs = ig.getInvs(invtype='nested',seed=1)
seed 1 (test 0.829402 0.595912 0.429361)
sample_traces: chose |tcs1|=1, |tcs2|=0 (attempted 1/1 tcs)
Time elapsed: 0.0000 s (function sample_traces)
*** NestedArray ***
0. All: ['A', 'B', 'C']
1. Assume: []
2. Const: []
3. Expect: ['A[i]=B[C[2i+1]]']
4. ExtFun: []
5. Global: []
6. Input: []
7. Output: []
Generate Expressions
* genArrExps [A,C,B]: 2 expressions generated
* Find expressions with possible relationships ..
0. A[i1] == B[C[(i1)_]] has possible relationship: lambda A,C,B,i1: A[i1] == B[C[2*i1 + 1]]
1. A[i1] == B[(i1)_] has possible relationship: lambda A,B,i1: A[i1] == B[-2*i1 + 5]
* Possible Relationships: 2
Time elapsed: 0.0575 s (solve)
Refine 2 candidate invariants
* rfilter(|ps|=2,|tcs|=1)
rfilter (before 2, after 2, diff 0)
Time elapsed: 0.0015 s (refine)
Detected Invariants for NestedArray:
  0: lambda A,B,i1: A[i1] == B[-2*i1 + 5]
  1: lambda A,C,B,i1: A[i1] == B[C[2*i1 + 1]]
