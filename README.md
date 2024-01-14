# DIG

**DIG** is an _invariant generation_ tool. It can discover program invariants at _arbitrary_ program locations (e.g., loop invariants, post conditions). DIG focuses on _numerical_ invariants and currently supports the following numerical relations:
- *nonlinear / linear equalities* among arbitrary variables,  e.g.,  `x+y=5`, `x*y=z`, `x*3y^3 + 2*zw + pq + q^3 = 3`
- *linear inequalities* (e.g., interval and octagonal invariants), e.g., `-4 <= x <= 7,  -2 <= - x - y <= 10`
- *disjunction*:  certain types of disjunctions under the *min/max* forms, e.g., `max(x,y) <= z + 2`, and nonlinear forms, e.g., `x^2 −xy −xz +yz =0` is `(x −y)=0 v (x − z)=0`
- *congruence* relations, e.g.,  `x == 0 (mod 4),  x+y == 1 (mod 5)`
- *nested relations* among arrays, e.g., `A[i] = B[C[3*i+2]]`
- The user can also use *terms* to represent desired information, e.g., `t1 = 2^x, t2 = log(n)`, and have DIG infer invariants over terms.

> :boom: This [page](./EXAMPLES.md) has various examples demonstrating the power of DIG.

DIG's numerical relations (in particular, nonlinear relations) have been used for:
- *program understanding and correctness/safety checking* (`TSE21`, `ICSE12`, `ICSE14`, `ASE17`, `FSE17`, `TOSEM13`)
- *complexity analysis* by providing program run time complexity such as `O(N^2)` or `O(NM)` (`ASE17`, `FSE17`)
- *recurrence relations* for complexity analysis (e.g., finding recurrence relations for recursive programs such as `T(n)=3*T(n/2) + f(n)`, (`SEAD20`)
- *termination and non-termination analyses* (use nonlinear invariants to infer and reason about ranking functions for termination and recurrent sets for non-termination, `OOPSLA20`)
- *array analysis*, finding invariant relations over array data structures such as `A[i] = B[C[2i + 3]]`, (`ICSE12`, `TOSEM13`)
- **Benchmarks**: The DIG project also produces a large set of **NLA** [benchmark programs](https://github.com/dynaroars/dig/tree/dev/benchmark) that contain nonlinear invariants.  Many of these programs are used in the annual SV-COMP (Software verification competition), e.g., [`dig-nla`](https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/tree/main/c/nla-digbench) and [`dig-nla-scaling`](https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks/-/tree/main/c/nla-digbench-scaling).




<details>

<summary><kbd>details</kbd></summary>
	
DIG is written in Python and uses **Sympy** and **Z3**. It infers invariants using dynamic analysis, i.e., analyzing program execution traces.  If a C source code is available, DIG can check and refine invariants.
DIG uses symbolic execution to collect symbolic states to check candidate invariants.
DIG aims to be fully automated and can find good invariants with its default configuration (i.e., the user doesn't need to try different configurations for good performance).  

</details>


>:rocket: A good starting point to understand DIG and its usage at high level is reading our [ICSE'22 tool](https://dynaroars.github.io/pubs/nguyen2022syminfer.pdf) and [TSE'21](https://dynaroars.github.io/pubs/nguyen2021using.pdf) papers . 



---

## Setup using Docker

```bash
# clone DIG
$ git clone --depth 1 https://github.com/dynaroars/dig.git 

# Then go to DIG's directory 
$ cd dig # in DIG's directory

# build the docker image, will take some time to install and build everything
$ docker build . -t='dig'
...
...

# then run dig
$ docker run -it dig

# docker will drop you into a Linux prompt like below
$ root@b53e0bd86c11:/dig/src#

# now you can run DIG -- the more CPUs/CORES your machine has, the faster DIG will run.  

# run DIG on a trace file
root@931ac8632c7f:/dig/src# time ~/miniconda3/bin/python3 -O dig.py  ../tests/traces/cohendiv.csv -log 4
...
...

# or on a C program

# FASTER: restrict nonlinear eqts to degree 2 and but don't generate inequalities or minmax invariants and 
root@931ac8632c7f:/dig/src# time ~/miniconda3/bin/python3 -O dig.py  ../benchmark/c/nla/cohendiv.c -maxdeg 2 -noieqs -nominmax -log 4

# SLOWER: but gives everything
root@931ac8632c7f:/dig/src# time ~/miniconda3/bin/python3 -O dig.py  ../benchmark/c/nla/cohendiv.c -log 4
...

# to update DIG to the latest from github, do a git pull in the main DIG directory in the Docker
root@931ac8632c7f:/dig/src# git pull
...
...
```

## Usage

DIG can generate invariants from a [trace file](#generating-invariants-from-traces) (a plain text semi-colon separated `csv` file consisting of concrete values of variables) or a [program](#generating-invariants-from-a-program) (a C file `.c`).

### Generating Invariants From Traces

DIG can infer invariants directly from an `csv` file consisting of concreting program execution traces as shown below.

```txt
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

tnguyen@origin ~/d/src (dev)> time ~/miniconda3/bin/python3 -O dig.py  ../tests/traces/cohendiv.csv -log 3                                                                                                                                            (base) 
settings:INFO:2021-10-29 13:51:40.966898: dig.py ../tests/traces/cohendiv.csv -log 3
alg:INFO:analyzing '../tests/traces/cohendiv.csv'
alg:INFO:check 546 invs using 181 traces (0.26s)
alg:INFO:simplify 544 invs (2.35s)
vtrace1(17 invs):
1. a*y - b == 0
2. q*y + r - x == 0
3. -q <= 0
4. -y <= -1
5. a - b <= 0
6. r - x <= 0
7. b - r <= 0
8. a - x <= -5
9. -b + y <= 0
10. -x + y <= -6
11. -q - r <= -8
12. -r - x <= -16
13. -x - y <= -10
14. a + 2 - max(q, r, y) <= 0
15. y + 2 - max(b, q, r, 0) <= 0
16. -q === 0 (mod 2)
17. -r - x === 0 (mod 2)
vtrace2(8 invs):
1. q*y + r - x == 0
2. -q <= 0
3. -r <= 0
4. q - x <= 0
5. r - x <= 0
6. r - y <= -1
7. -q - r <= -1
8. -x - y <= -10
```

*Note*: if we just run Dig over traces, then we likely can get spurious inequalities, i.e., they are correct with the given traces, but not real invariants.  If given the program source code as shown below, DIG can check the source code and remove spurious results.


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

* To find invariants at some abitrary location, we declare a function `vtraceX` where `X` is some distinct number and call that function at that location.
  * For example, in `cohendiv.c`,  we call `vtrace0`, `vtrace1` at the head of the outter and inner while loops find loop invariants  and  `vtrace2` before the function exit to find post conditions.
  * `vtraceX` takes a list of arguments that are variables in scope at the desired location. This tells DIG to find invariants over these variables.


> Using symbolic states collected from symbolic execution (default option)


* We now run DIG on `cohendiv.c` and discover the following invariants at the `vtracesX` locations:

```sh
$ time ~/miniconda3/bin/python3  -O dig.py  ../tests/cohendiv.c -log 3
settings:INFO:2021-10-29 13:51:11.038391: dig.py ../tests/cohendiv.c -log 3
alg:INFO:analyzing '../tests/cohendiv.c'
alg:INFO:got symbolic states at 4 locs in 4.21s
alg:INFO:got 69 ieqs in 1.11s
alg:INFO:got 377 minmax in 1.69s
alg:INFO:got 6 eqts in 5.50s
alg:INFO:check 452 invs using 680 traces (0.33s)
alg:INFO:simplify 452 invs (1.40s)
* prog cohendiv locs 4; invs 29 (Eqt: 5, MMP: 1, Oct: 23) V 6 T 3 D 2; NL 5 (2) ;
-> time eqts 5.5s, ieqs 1.1s, minmax 1.7s, simplify 1.8s, symbolic_states 4.2s, total 11.5s
rand seed 1635533471.04, test 62
tmpdir: /var/tmp/dig_92233634043151007_2nugp63w
vtrace0(2 invs):
1. -y <= -1
2. -x <= -1
vtrace1(12 invs):
1. a*y - b == 0
2. q*y + r - x == 0
3. -r <= 0
4. -a <= 0
5. -y <= -1
6. q - x <= 0
7. a - q <= 0
8. b - x <= 0
9. r - x <= 0
10. a - b <= 0
11. -q - r <= -1
12. min(q, y) - b <= 0
vtrace2(8 invs):
1. a*y - b == 0
2. q*y + r - x == 0
3. -q <= 0
4. -y <= -1
5. r - x <= 0
6. b - r <= 0
7. a - b <= 0
8. -b + y <= 0
vtrace3(7 invs):
1. q*y + r - x == 0
2. -q <= 0
3. -r <= 0
4. q - x <= 0
5. r - x <= 0
6. r - y <= -1
7. -r - x <= -1
```

> Using Random Inputs 

The `-noss` option disables symbolic states and thus makes DIG behaves as a pure *dynamic* invariant generation tools.  Here, DIG runs the program on random inputs, collects traces, and infers invariants.  It does not use symbolic states and thus does not require symbolic execution tools, but it can have spurious results.

```sh
$ time ~/miniconda3/bin/python3  -O dig.py  ../tests/cohendiv.c -log 3 -noss -nrandinps 10
settings:INFO:2021-10-23 12:37:15.965808: dig.py ../tests/cohendiv.c -log 3 -noss -nrandinps 10
alg:INFO:analyzing '../tests/cohendiv.c'
alg:INFO:analyzing '../tests/cohendiv.c'
infer.eqt:WARNING:18 traces < 35 uks, reducing to deg 2
infer.eqt:WARNING:38 traces < 84 uks, reducing to deg 2
infer.eqt:WARNING:50 traces < 84 uks, reducing to deg 2
alg:INFO:testing 678 invs using 106 traces (0.30s)
alg:INFO:simplify 670 invs (3.26s)
vtrace1 (17 invs):
1. a*y - b == 0
2. q*y + r - x == 0
3. -a <= 0
4. -r <= 0
5. -y <= -9
6. a - b <= 0
7. a - q <= 0
8. r - x <= 0
9. q - x <= -6
10. b - x <= -2
11. -a - r <= -2
12. -x - y <= -16
13. min(q, r, x) - b <= 0
14. a + q === 0 (mod 2)
15. a - q === 0 (mod 2)
16. -a - q === 0 (mod 2)
17. -a + q === 0 (mod 2)
vtrace2 (17 invs):
1. a*y - b == 0
2. q*y + r - x == 0
3. -q <= 0
4. -y <= -9
5. r - x <= 0
6. b - r <= 0
7. -b + y <= 0
8. -r + y <= -2
9. -q - x <= -12
10. min(a, b, q) - y - 1 <= 0
11. b + 2 - max(a, q, r, y) <= 0
12. q === 0 (mod 2)
13. -q === 0 (mod 2)
14. r - x === 0 (mod 4)
15. r + x === 0 (mod 2)
16. -r + x === 0 (mod 4)
17. -r - x === 0 (mod 2)
vtrace3 (9 invs):
1. q*y + r - x == 0
2. -r <= 0
3. -q <= 0
4. -y <= -9
5. r - x <= 0
6. r - y <= -1
7. -q - x <= -6
8. -q - r <= -3
9. -x - y <= -16
```

### Other programs

* The directory [`benchmark/c/nla`](./benchmark/c/nla) contains many programs having nonlinear invariants.

### Additional Options 

<details>

<summary><kbd>details</kbd></summary>


Most of DIG's behaviors can be controlled by the user (the `src/settings.py` lists all the defaut parameters).  Use `-h` or `--help` to see options that can be passed into DIG. Below we show several ones

#### Specify max degree for equalities

By default, DIG automatically to find equalities that can have high degrees (e.g., `x^7`).  This can take time and so we can specify DIG to search for equalities no more than some maximum degree `X` using the option `-maxdeg X`.  This will make DIG runs faster (with the cost of not able to find equalities with higher degrees than `X`). 

#### Disabling Invariants
By default DIG searches for all supported forms of invariants.  However, we can turn them off using `-noeqts`, `-noieqs` , `-nominmax`, `nocongruences`  

```sh
$ ~/miniconda3/bin/python3  -O dig.py  ../tests/cohendiv.c -log 3 -maxdeg 2 -noieqs  #find equalities up to degree 2 and do not infer inequalities
...
```

#### Customizing Inequalities

By default, DIG infers octagonal inequalities (i.e., linear inequalities among `2` variables with coefs in in the set `{-1,0,1}`).   We can customize DIG to find more expression inequalities (of course, with the trade-off that it takes more time to generate more expressive invs).

Below we use a different example `Sqrt1.java` to demonstrate

```sh
$ ~/miniconda3/bin/python3  -O dig.py  ../benchmark/c/nla/sqrt1.c -nominmax -nocongruences  # find default, octagonal, ieq's.
...
1. 2*a - t + 1 == 0
2. 4*s - t**2 - 2*t - 1 == 0
3. -a <= 0
4. a - n <= 0
5. -n + t <= 2
6. -s + t <= 0


$ ~/miniconda3/bin/python3  -O dig.py  ../benchmark/c/nla/sqrt1.c -nominmax -nocongruences -ideg 2   # find nonlinear octagonal inequalities
...
1. 2*a - t + 1 == 0
2. 4*s - t**2 - 2*t - 1 == 0
3. -a <= 0
4. a - n <= 0
5. -s + t <= 0
6. -n + t <= 2
7. -s**2 + t**2 <= 0

$ ~/miniconda3/bin/python3  -O dig.py  ../benchmark/c/nla/sqrt1.c -nominmax -nocongruences -icoefs 2   # find linear inequalities with coefs in {2,-1,0,1,2}
...
1. 2*a - t + 1 == 0
2. 4*s - t**2 - 2*t - 1 == 0
3. -a <= 0
4. a - n <= 0
5. -n + 2*t <= 6
6. -2*n + s <= 2
7. -2*s + 2*t <= 0
```

---
</details>

## :question: FAQs

<details>

<summary><kbd>Information that might be useful for researches (e.g., what makes DIG different than others?)</kbd></summary>

> What is the input to DIG? 
  - DIG takes as input a C program.  This program must be compilable (i.e., syntactically correct) and is annnotated with locations of interest (where you want to infer invariants at).  
  - DIG can also take as input a `csv` file consisting of program traces and it will infer invariants just over those traces (i.e., pure dynamic).
  
>  Do I need to tune DIG to infer invariants?
  - No, DIG should work out of the box and does not require user inputs.  However, if you want to tweak the behavior of DIG, you can do so as shown [here](#additional-options). 
  
> What kind of invariants are supported?
  
  - This DIG tool supports **numerical invariants**. This includes both nonlinear and linear (affine) properties. See programs and examples [here](./EXAMPLES.md)
  - Note many [research projects](#page_with_curl-publications) build upon DIG to support other kinds of invariants (e.g., ranking functions and recurrent sets for termination and non-termination analysis, or recurrence relations for complexity analysis). These projects will have their own, separate research prototypes.
  
> What makes DIG different from other invariant generation tools? 

- A good starting place to understanding DIG's technical details is our [TSE'21](https://dynaroars.github.io/pubs/nguyen2021using.pdf) paper.
- Main purpose of DIG is to discover strongest possible invariants at desired locations, *not* to prove an assertion or post condition, which is the goal of many invariant tools.
  - Of course if the invariants found are stronger than the assertion or post condition, then those are proved
- DIG infers invariants at arbitrary location and thus is not restricted to, e.g.,  inductive loop invariants
- The input of DIG is a _program_, not SMT formulae representing transitions as in many invariant tools
- Checking is done by extracting _symbolic states_ using _symbolic execution_ and applying Z3 SMT solver to reason about the states and candidate invariant.s
- DIG's inferrence is dynamic (mostly), i.e., DIG *is* a data-driven approach
  - Some parts, e.g., inequalities, use static analysis by analyzing symbolic states
  - Does not use ML for inference (not neural networks, classifers, etc)
- DIG follows an _iterative guess-and-check approach_, which infers candidate invs from traces, checks and obtains counterexample traces to improve inference, and repeats

> How to to speed up DIG?
- By default, DIG performs multiple algorithms to find different invariants and its nonlinear equality invariants can have very large degree, all of which contribute to large search space.  To speed up DIG, you have several options
  - Use a computer with many cores.  DIG leverages multiprocessing and can run significantly faster with a modern multicore computer.  As an example, our [lab machine](https://github.com/dynaroars/dynaroars.github.io/wiki/Servers) has 64 cores.  Of course you don't need that many, but the more, the better.
    - Note that DIG does not leverage GPU processing
  - Tweak its parameters as shown [here](#additional-options). For example, reducing the number of degree to `d` (`-maxdeg d`) will tell DIG not to search for nonlinear invariants with degree more than `d` or disabling certain types of invariants if you're not intested in them (e.g., `-nominmax` to disable the computation of min/max properties)

---
</details>

## :page_with_curl: Publications

Technical information about DIG can be found from these papers.  The `tool` paper (`ICSE22`) and `Symbolic States` paper (`TSE21`) are probably a good start.
1. ThanhVu Nguyen, KimHao Nguyen, and Hai Duong. [**SymInfer: Inferring Numerical Invariants using Symbolic States**](https://dynaroars.github.io/pubs/nguyen2022syminfer.pdf). International Conference on Software Engineering-Tool Demo, pages 197--201, 2022
1. ThanhVu Nguyen, KimHao Nguyen, Matthew Dwyer. [**Using Symbolic States to Infer Numerical Invariants**](https://dynaroars.github.io/pubs/nguyen2021using.pdf). Transactions on Software Engineering (TSE), 2021
1. Ton Chanh Le, Timos Antonopoulos, Parisa Fathololumi, Eric Koskinen, ThanhVu Nguyen. **DynamiTe: Dynamic Termination and Non-termination** Proofs. Proc. ACM Program. Lang. (OOPSLA), 2020
1. ThanhVu Nguyen, Didier Ishimwe, Alexey Malyshev, Timos Antonopoulos, and Quoc-Sang Phan. **Using Dynamically Inferred Invariants to Analyze Program Runtime Complexity**. Workshop on Software Security from Design to Deployment, 2020
1. ThanhVu Nguyen, Matthew Dwyer, and William Visser. **SymInfer: Inferring Program Invariants using Symbolic States**. In Automated Software Engineering (ASE). IEEE, 2017.
1. ThanhVu Nguyen, Timos Antopoulos, Andrew Ruef, and Michael Hicks. **A Counterexample-guided Approach to Finding Numerical Invariants**. In 11th Joint Meeting on Foundations of Software Engineering (ESEC/FSE), pages 605--615. ACM, 2017.
1. ThanhVu Nguyen, Deepak Kapur, Westley Weimer, and Stephanie Forrest. **DIG: A Dynamic Invariant Generator for Polynomial and Array Invariants**. Transactions on Software Engineering Methodology (TOSEM), 23(4):30:1--30:30, 2014.
1. ThanhVu Nguyen, Deepak Kapur, Westley Weimer, and Stephanie Forrest. **Using Dynamic Analysis to Generate Disjunctive Invariants**. In 36th International Conference on Software Engineering (ICSE), pages 608--619. IEEE, 2014.
1. ThanhVu Nguyen, Deepak Kapur, Westley Weimer, and Stephanie Forrest. **Using Dynamic Analysis to Discover Polynomial and Array Invariants**. In 34th International Conference on Software Engineering (ICSE), pages 683--693. IEEE, 2012.  `Distinguish Paper Award`

## ACKNOWLEDGEMENTS

* This project is supported in part by NSF grants CCF 1948536, CCF 2200621 and ARO grant W911NF-19-1-0054.

