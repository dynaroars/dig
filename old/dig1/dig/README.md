# README #
DIG (Dynamic Invariant Generator) is a dynamic analysis tool that discovers polynomial and array invariants from program traces. For polynomial invariants, DIG supports conjunction of (potentially nonlinear) polynomial relations over numerical variables.  DIG also supports the max and min-plus forms of disjunction polynomial invariants. For array invariants, DIG supports flat and nested form of relations among multidimentional array variables.

## Setup ##

The source code of DIG is released under the **BSD** license and can be obtained using the commands
```
hg clone https://nguyenthanhvuh@bitbucket.org/nguyenthanhvuh/dig/ 
hg clone https://nguyenthanhvuh@bitbucket.org/nguyenthanhvuh/common_python/
```

DIG uses Python/SAGE. Some tasks such as verifying candidate invariants require a recent SMT solver. The tool has been tested using the following setup:

* Debian Linux 7 (Wheezy)
* Sage 6.2
* Microsoft Z3 SMT solver 4.x

### Installing Z3 and SAGE ###
First, setup Z3 using its own build instruction. Make sure Z3 is installed correctly so that you can do `import z3` in a Python interpreter. Next, setup SAGE (you can simply download the tarball consisting of precompiled SAGE, or build SAGE directly from source). Finally, setup the SAGE environment and add Z3's lib to its path as follows.
```
#!shell
# ~/.bash_profile
export Z3=PATH/TO/z3   #Z3 dir
export SAGE=PATH/TO/sage  #where your SAGE dir is
export $DIG=/PATH/TO/dig  #DIG main dir
export SAGE_PATH=/PATH/TO/common_python:$DIG:$Z3/src/api/python:$DIG/dig:$DIG/miscs
export PATH=$SAGE:$PATH
```
Now we should be able to do `import z3` in SAGE. For additional testings, execute the `run_doctests.sh` script to tests all doctests in DIG's files.

### Installing compute_ext_rays_polar ###
For max/min inequalities, compile the program [`tplib`](http://opam.ocaml.org/packages/tplib/tplib.1.3/) package.  Then put the compiled program `compute_ext_rays_polar` in your PATH (e.g., in `/usr/local/bin`).

Note that this installation can be discarded if we don't need max/min inequalities.

## Usage ##
Here are some usage examples of DIG.  The following assumes we are currently in the `$DIG/dig` directory.

### (Nonlinear) Polynomial Invariants ###
```
#!shell
sage: %attach dig.py
sage: dig = DIG('../traces/NLA/tcs/cohendiv.l1a.tcs')
...
sage: dig.get_invs()
dig:Debug:*** Generate Polynomial Invs over [a, b, q, r, x, y] ***
...
dig:Info:Detected 2 invs for Eqt:
    0: a*y - b == 0
    1: q*y + r - x == 0
```

Here DIG discovers the invariants `a*y = b, q*y + r = x` from the traces in `../traces/NLA/tcs/cohendiv.l1a.tcs`

```
#!
x y q a b r
102031 19229 0 1 19229 102031
102031 19229 0 2 38458 102031
165043 78404 0 1 78404 165043
603505 47638 0 1 47638 603505
603505 47638 0 2 95276 603505
603505 47638 0 4 190552 603505
603505 47638 8 1 47638 222401
603505 47638 8 2 95276 222401
...
```
These traces (values of the variables *x, y, q, a, b, r*) are obtained at location `li1` in the program 

```
#!C

int cohendiv(int x, int y){
  //Cohen's integer division that returns x % y
  assert(x>0 && y>0);
  int q=0; 
  int r=x;
  while(1){
    if (!(r>=y)) break;
    int a=1; 
    int b=y;
    while(1){
      printf("li1: %d %d %d %d %d %d\n",x,y,q,a,b,r);  //traces
      if (!(r >= 2*b)) break;
      a = 2*a;
      b = 2*b;
    }
    r=r-b;
    q=q+a;    
  }
  return q;
}
```

Thus DIG finds the *nonlinear* equalities `a*y = b, q*y + r = x` at location `l1i` of `cohendiv`. The directory `../programs/polynomials/` contains many programs having such nonlinear invariants.


### Array Invariants ###

**Flat array invariants**

```
#!
sage: dig = DIG('../traces/Examples/array_flat.tcs')
...
sage: dig.get_flat_array()
dig:Info:*** FlatArray ***
dig:Info:Select traces
dig:Info:Compute invs over 9 tcs
....
dig:Info:Detected 2 invs for FlatArray:
    0: (-A[A0]) + ((7) *B[2*A0]) + (3*A0) == 0
    1: ((7) *B[B0]) + (-A[1/2*B0]) + (3/2*B0) == 0
```

Here DIG discovers the array invariants `A[i] = 7*B[2i] + 3i` from the traces in `../traces/Examples/array_flat.tcs`

```
#!
A B
[-546,-641,34] [-78,3,-92,-34,4]
[-448,-585,118] [-64,40,-84,78,16]
[539,-487,517] [77,55,-70,74,73]
[-7,-18,482] [-1,51,-3,-19,68]
[-119,192,216] [-17,80,27,32,30]
[-273,591,699] [-39,13,84,56,99]
[133,-333,-323] [19,96,-48,-80,-47]
[-168,157,643] [-24,8,22,-61,91]
[-84,-18,300] [-12,-60,-3,-16,42]
```

**Nested array invariants**

```
#!

sage: dig = DIG('../traces/Examples/array_nested.tcs')
...
sage: dig.get_nested_array()
dig:Info:*** NestedArray ***
dig:Info:Select traces
...
dig:Info:Detected 2 invs for NestedArray:
    0: A[i1] == B[-2*i1 + 5]
    1: A[i1] == B[C[2*i1 + 1]]
```

Here DIG discovers the array invariants `A[i] = B[C[2i+1]]` from the traces in `../traces/Examples/array_nested.tcs`
```
#!
A B C
[7,1,-3] [1,-3,5,1,0,7,1] [8,5,6,6,2,1,4]
```


The directory `../programs/AES/` contains many programs having such array invariants.

## Publications ##
Additional information on DIG can be found from these papers: 

* Automating Program Verification and Repair Using Invariant Analysis and Test-input Generation Nguyen, T. Ph.D. Thesis, University of New Mexico, August 2014. 
* ThanhVu Nguyen, Deepak Kapur, Westley Weimer, Stephanie Forrest, "DIG: A Dynamic Invariant Generator for Polynomial and Array Invariants", ACM Trans. on Software Engineering and Methodology, pages 30:1-30:30, 2014.
* Using Dynamic Analysis to Generate Disjunctive Invariants Nguyen, T.; Kapur, D.; Weimer, W.; and Forrest, S. In International Conference on Software Engineering, pages 608-619, 2014. 
* Using Dynamic Analysis to Discover Polynomial and Array Invariants Nguyen, T.; Kapur, D.; Weimer, W.; and Forrest, S. In International Conference on Software Engineering, pages 683-693, 2012.