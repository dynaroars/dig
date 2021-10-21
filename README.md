# DIG

**DIG** is a tool for generating program invariants at arbitrary program locations (e.g., loop invariants, post conditions). DIG infers (potentially **nonlinear**) numerical invariants using symbolic states extracted from a symbolic execution tool. DIG supports equalities such as `x+y=5`, `x*y=z`, `x*3y^3 + 2*zw + pq + q^3 = 3`, inequalities such as `x <= y^2 + 3`, and min/max inequalities such as `max(x,y) <= z + 2`.  The user can also use *terms* to represent desired information, e.g., `t = 2^x`, and have DIG infer invariants over terms.

DIG's numerical relations (in particular, nonlinear equalities) have been used for
- nonlinear program understanding and correctness checking (`TSE21`, `ICSE12`, `ICSE14`, `ASE17`, `FSE17`, `TOSEM13`)
- complexity analysis by providing program run time complexity such as `O(N^2)` or `O(NM)` (`ASE17`, `FSE17`)
- recurrence relations for complexity analysis (e.g., finding recurrence relations for recursive programs such as `T(n)=3*T(n/2) + f(n)`, `SEAD20`)
- termination and non-termination analyses (use nonlinear invariants to reason about ranking function for termination and recurrent sets for non-termination, `OOPSLA20`)
- array analysis (finding invariant relations over array data structures such as `A[i] = B[C[2i + 3]]`, `ICSE12`, `TOSEM13`)

DIG is written in Python and uses **Sympy** and **Z3**. It infers invariants using dynamic analysis (over execution traces).  If source code (C, Java, Java Bytecode) is available, DIG can iteratively infer and check invariants.
DIG uses symbolic execution (**Symbolic PathFinder** for Java and **CIVL** for C) to collect symbolic states to check candidate invariants.

---
## Setup using Docker

```bash
# clone DIG
$ git clone --depth 1 https://github.com/unsat/dig.git 

# Then go to DIG's directory 
$ cd dig # in DIG's directory

# build the docker image, will take sometime to build everything
$ docker build . -t='dig'
...
...

# then run dig
$ docker run -it dig

# docker will drop you into a Linux prompt like below.
$ root@b53e0bd86c11:/dig/src#


# now we can run DIG on a trace file
root@931ac8632c7f:/dig/src# time ~/miniconda3/bin/python3 -O dig.py  ../tests/traces/cohendiv.csv -log 4
...
...

# or on a C program
root@931ac8632c7f:/dig/src# time ~/miniconda3/bin/python3 -O dig.py  ../benchmark/c/nla/cohendiv.c -log 4
...

# to update DIG to the latest from github,  do a git pull in the main DIG directory in the Docker
root@931ac8632c7f:/dig/src# git pull
...
...

```

## Usage

DIG can generate invariants from a [trace file](#generating-invariants-from-traces) (a plain text semi-colon separated `csv` file consisting of concrete values of variables) or a [program](#generating-invariants-from-a-program) (either a Java file `.java`, a bytecode file `.class`, or a C file `.c`).

### Generating Invariants From Traces

DIG can infer invariants directly from an `CSV` file consisting of concreting program execution traces.  Below is an example of traces generated when running the above `CohenDiv` program with various inputs

```csv
# in DIG's src directory
$ less ../test/traces/cohendiv.csv
vtrace1; I q; I r; I a; I b; I x; I y
vtrace1; 4; 8; 1; 4; 24; 4
vtrace1; 16; 89; 1; 13; 297; 13
vtrace1; 8; 138; 4; 76; 290; 19
vtrace1; 0; 294; 8; 192; 294; 24
vtrace1; 64; 36; 4; 16; 292; 4
...
vtrace2; I x; I y; I q; I r
vtrace2; 280; 24; 11; 16
vtrace2; 352; 11; 32; 0
vtrace2; 22; 298; 0; 22
vtrace2; 274; 275; 0; 274
vtrace2; 2; 287; 0; 2
...
```

```txt
# in DIG's src directory
$ time ~/miniconda3/bin/python3 -O dig.py  ../tests/traces/cohendiv.csv -log 3                                                                                                                                            (base) 
settings:INFO:2021-10-20 22:07:46.378997: dig.py ../tests/traces/cohendiv.csv -log 3
alg:INFO:analyzing '../tests/traces/cohendiv.csv'
alg:INFO:testing 540 invs using 181 traces (0.31s)
alg:INFO:simplify 538 invs (3.38s)
vtrace1 (16 invs):
1. a*y - b == 0
2. q*y + r - x == 0
3. -q <= 0
4. a - b <= 0
5. b - r <= 0
6. r - x <= 0
7. a - x <= -5
8. -b + y <= 0
9. -x + y <= -6
10. -a - b <= -2
11. -a - q <= -1
12. -q - r <= -8
13. -x - y <= -10
14. -r - x <= -16
15. y + 2 - max(q, r, 0) <= 0
16. a + 2 - max(b, q, r, y) <= 0
vtrace2 (8 invs):
1. q*y + r - x == 0
2. -q <= 0
3. -r <= 0
4. q - x <= 0
5. r - x <= 0
6. r - y <= -1
7. -q - r <= -1
8. -x - y <= -10
```

*Note*: if we just run Dig over traces, then we likely can get spurious inequalities, i.e., they are correct with the given traces, but not real invariants.  If given the program source code [as shown here](#using-symbolic-execution-default-option), DIG can check and remove spurious results.


### Generating Invariants From a Program

Consider the following `cohendiv.c` program

```c
// in DIG's src directory
// $ less ../test/cohendiv.c

#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int q, int r, int a, int b, int x, int y){}
void vtrace2(int q, int r, int a, int b, int x, int y){}
void vtrace3(int q, int r, int x, int y){}

int mainQ(int x, int y){
    vassume(x >= 1 && y >= 1);
    
    int q=0;
    int r=x;
    int a=0;
    int b=0;
    while(1) {
	vtrace1(q, r, a, b, x, y);
	if(!(r>=y))
	    break;
	a=1;
	b=y;
	  
	while (1){
	    vtrace2(q, r, a, b, x, y);
	    if(!(r >= 2*b))
		break;
	       
	    a = 2*a;
	    b = 2*b;
	}
	r=r-b;
	q=q+a;
    }
    vtrace3(q, r,x, y);
    return q;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

```

* To find invariants at some location, we declare a function `vtraceX` where `X` is some distinct number and call that function at that location.
  * For example, in `cohendiv.c`,  we call `vtrace0`, `vtrace1` at the head of the outter and inner while loops find loop invariants  and  `vtrace2` before the function exit to find post conditions.
  * `vtraceX` takes a list of arguments that are variables in scope at the desired location. This tells DIG to find invariants over these variables.


##### Using Symbolic Execution (default option)


* We now run DIG on `cohendiv.c` and discover the following invariants at the `vtracesX` locations:

```sh
settings:INFO:2021-10-20 14:11:22.139334: dig.py ../tests/cohendiv.c -log 3
alg:INFO:analyzing '../tests/cohendiv.c'
alg:INFO:got symbolic states at 3 locs: (4.10s)
alg:INFO:found 11 eqts (19.18s)
alg:INFO:found 67 ieqs (0.55s)
alg:INFO:found 377 minmax (1.89s)
alg:INFO:test 455 invs using 611 traces (0.74s)
alg:INFO:simplify 451 invs (2.15s)
* prog cohendiv locs 3; invs 28 (Eqt: 5, MMP: 1, Oct: 22) V 6 T 3 D 2; NL 5 (2) ;
-> time eqts 19.2s, ieqs 0.5s, minmax 1.9s, simplify 2.9s, symbolic_states 4.1s, total 28.7s
rand seed 1634757082.14, test 10
vtrace1 (12 invs):
1. a*y - b == 0
2. q*y + r - x == 0
3. -a <= 0
4. -r <= 0
5. a - b <= 0
6. r - x <= 0
7. b - x <= 0
8. a - q <= 0
9. q - x <= 0
10. -b - y <= -1
11. -q - r <= -1
12. min(q, y) - b <= 0
vtrace2 (9 invs):
1. a*y - b == 0
2. q*y + r - x == 0
3. -q <= 0
4. a - b <= 0
5. b - r <= 0
6. r - x <= 0
7. -b + y <= 0
8. -b - y <= -2
9. -a - q <= -1
vtrace3 (7 invs):
1. q*y + r - x == 0
2. -q <= 0
3. -r <= 0
4. -x <= -1
5. r - x <= 0
6. q - x <= 0
7. r - y <= -1
tmpdir: /var/tmp/dig_322818264817232346_kr7neztj
```

### Other programs

* The directory `../benchmarks/c/nla` contains many programs having nonlinear invariants.


### Additional Options

<details>
<summary><kbd>CLICK</kbd> for further details</summary>

Most of DIG's behaviors can be controlled by the users (the `src\settings.py` lists all the defaut parameters).  Use `-h` or `--help` to see options that can be passed into DIG. Below we show several ones

#### Specify max degree for equalities

By default, DIG automatically to find equalities up to certain degree.  We can specify this degree directly with `-maxdeg X`

```sh
tnguyen@debian ~/dig/src> python3 -O dig.py  ../benchmark/java/nla/CohenDiv.java   -log 3 -maxdeg 2 -noieqs  #find equalities up to degree 2 and donot infer inequalities
...
```

#### Customizing Inequalities

By default, DIG infers octagonal inequalities (i.e., linear inequalities among 2 variables with coefs in in the set {-1,0,1}).  But we can customize DIG to find more expression inequalities (of course, with the trade-off that it takes more time to generate more expressive invs).

Below we use a different example `Sqrt1.java` to demonstrate

```sh
tnguyen@debian ~/dig/src> python3 -O dig.py  ../benchmark/java/nla/CohenDiv.java  -log 3  -noeqts  # for demonstration, only find default, octagonal, ieq's.
...
1. a <= 10
2. a - n <= 0
3. -t <= -1
4. -s <= -1
5. -n + t <= 2
6. -a <= 0


tnguyen@debian ~/dig/src> python3 -O dig.py  ../tests/paper/Sqrt1.java  -log 4 -noeqts -ideg 2  # find nonlinear octagonal inequalities
...
1. a*s - n*t <= 1
2. a <= 10
3. -t <= -1
4. -s <= -1
5. -n*t + s <= 1
6. -n*s + t <= 1
7. -n*s + a*t <= 0
8. -n + t <= 2
9. -a*n + t <= 2
10. -a*n + s <= 3
11. -a <= 0

tnguyen@debian ~/dig/src> timeout 900 python3 -O dig.py  ../tests/paper/Sqrt1.java  -log 4 -noeqts -icoefs 2  # find linear inequalities with coefs in {2,-1,0,1,2}
...
1. a <= 10
2. 2*a - n <= 1
3. -t <= -1
4. -s <= -1
5. -n + 2*t <= 6
6. -a <= 0
7. -2*n + t <= 1
8. -2*n + s <= 2
```

---
</details>


## :page_with_curl: Publications

Technical information about DIG can be found from these papers.  The `Symbolic States (TSE'21)` paper is probably a good start.

* ThanhVu Nguyen, KimHao Nguyen, Matthew Dwyer. **Using Symbolic States to Infer Numerical Invariants, Transactions on Software Engineering (TSE)**. to appear, 2021
* Ton Chanh Le, Timos Antonopoulos, Parisa Fathololumi, Eric Koskinen, ThanhVu Nguyen. **DynamiTe: Dynamic Termination and Non-termination** Proofs. Proc. ACM Program. Lang. (OOPSLA), 2020
* ThanhVu Nguyen, Didier Ishimwe, Alexey Malyshev, Timos Antonopoulos, and Quoc-Sang Phan. **Using Dynamically Inferred Invariants to Analyze Program Runtime Complexity**. Workshop on Software Security from Design to Deployment, 2020
* ThanhVu Nguyen, Matthew Dwyer, and William Visser. **SymInfer: Inferring Program Invariants using Symbolic States**. In Automated Software Engineering (ASE). IEEE, 2017.
* ThanhVu Nguyen, Timos Antopoulos, Andrew Ruef, and Michael Hicks. **A Counterexample-guided Approach to Finding Numerical Invariants**. In 11th Joint Meeting on Foundations of Software Engineering (ESEC/FSE), pages 605--615. ACM, 2017.
* ThanhVu Nguyen, Deepak Kapur, Westley Weimer, and Stephanie Forrest. **DIG: A Dynamic Invariant Generator for Polynomial and Array Invariants**. Transactions on Software Engineering Methodology (TOSEM), 23(4):30:1--30:30, 2014.
* ThanhVu Nguyen, Deepak Kapur, Westley Weimer, and Stephanie Forrest. **Using Dynamic Analysis to Generate Disjunctive Invariants**. In 36th International Conference on Software Engineering (ICSE), pages 608--619. IEEE, 2014.
* ThanhVu Nguyen, Deepak Kapur, Westley Weimer, and Stephanie Forrest. **Using Dynamic Analysis to Discover Polynomial and Array Invariants**. In 34th International Conference on Software Engineering (ICSE), pages 683--693. IEEE, 2012.  `Distinguish Paper award`

## ACKNOWLEDGEMENTS

* This project is supported in part by NSF grant CCF-1948536 and ARO grant W911NF-19-1-0054.

