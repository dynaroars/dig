# DIG

**DIG** is a tool for generating program invariants at arbitrary program locations (e.g., loop invariants, post conditions). DIG infers (potentially **nonlinear**) numerical invariants using symbolic states extracted from a symbolic execution tool. DIG supports equalities such as `x+y=5`, `x*y=z`, `x*3y^3 + 2*zw + pq + q^3 = 3`, inequalities such as `x <= y^2 + 3`, and min/max inequalities such as `max(x,y) <= z + 2`.  The user can also use *terms* to represent desired information, e.g., `t = 2^x`, and have DIG infer invariants over terms.

DIG's numerical relations (in particular, nonlinear equalities) have been used for
- nonlinear program understanding and correctness checking (`TSE21`, `ICSE12`, `ICSE14`, `ASE17`, `FSE17`, `TOSEM13`)
- complexity analysis by providing program run time complexity such as `O(N^2)` or `O(NM)` (`ASE17`, `FSE17`)
- recurrence relations for complexity analysis (e.g., finding recurrence relations for recursive programs such as `T(n)=3*T(n/2) + f(n)`, `SEAD20`)
- termination and non-termination analyses (use nonlinear invariants to reason about ranking function for termination and recurrent sets for non-termination, `OOPSLA20`)
- array analysis (finding invariant relations over array data structures such as `A[i] = B[C[2i + 3]]`, `ICSE12`, `TOSEM13`)

DIG is written in Python and uses the **sympy** and **z3** library. It infers invariants using dynamic execution (over execution traces).  If source code is available, it can iteratively generate and check invariants using symbolic states for programs written in Java, Java bytecode, and C.
DIG uses symbolic execution (**Symbolic PathFinder** for Java and **CIVL** for C) to collect symbolic states and the **Z3** SMT solver for constraint solving.

---

## Usage

You can use DIG to generate invariants from a [trace file](#generating-invariants-from-traces) (a plain text semi-colon separated `csv` file consisting of concrete values of variables) or a [program](#generating-invariants-from-a-program) (either a Java file `.java`, a bytecode file `.class`, or a C file `.c`).

### Generating Invariants From Traces

DIG can infer invariants directly from an `CSV` file consisting of concreting program execution traces.  Below is an example of traces generated when running the above `CohenDiv` program with various inputs

```csv
# in DIG's src directory
$ less ../test/traces/CohenDiv.csv
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
tnguyen@debian ~/d/src> python3 -O dig.py ../tests/traces/CohenDiv.tcs -log 3
settings:INFO:2020-06-30 15:26:53.384339: dig.py ../tests/traces/CohenDiv.tcs -log 3
alg:INFO:analyze '../tests/traces/CohenDiv.tcs'
alg:INFO:test 30 invs using 181 traces (0.44s)
alg:INFO:simplify 26 invs (0.30s)
vtrace1 (8 invs):
1. q*y + r - x == 0
2. -q <= 0
3. -r <= 0
4. -y <= -1
5. q - x <= 0
6. r - x <= 0
7. -r - x <= -2
8. -x - y <= -10
vtrace2 (8 invs):
1. q*y + r - x == 0
2. -q <= 0
3. -r <= 0
4. q - x <= 0
5. r - x <= 0
6. r - y <= -1
7. -r - x <= -2
8. -x - y <= -10
```

*Note*: if we just run Dig over traces, then many generated inequality results would be spurious, i.e., they are correct with the given traces, but not real invariants.  If given the program source code [as shown here](#generating-invariants-from-a-program), DIG can check and remove spurious results.


### Generating Invariants From a Program

Consider the following `CohenDiv.java` program

```java
// in DIG's src directory
// $ less ../benchmark/java/nla/CohenDiv.java 

public class CohenDiv {
     public static void vtrace0(int q, int r, int a, int b, int x, int y){}
     public static void vtrace1(int q, int r, int a, int b, int x, int y){}
     public static void vtrace2(int x, int y, int q, int r){}

     public static void main (String[] args) {}
     public static int mainQ(int x, int y) {
          assert(x >= 0);
          assert(y >= 1);

          int q=0;
          int r=x;
          int a=0;
          int b=0;

          while(true) {
               vtrace0(q,r,a,b,x,y);
               if(!(r>=y)) break;
               a=1;
               b=y;

               while (true) {
                    vtrace1(q,r,a,b,x,y);
                    if(!(r >= 2*b)) break;

                    a = 2*a;
                    b = 2*b;
               }
               r=r-b;
               q=q+a;
          }

          vtrace2(x,y,q,r);
          return q;
     }
}

```

* To find invariants at some location, we declare a function `vtraceX` where `X` is some distinct number and call that function at that location.
  * For example, in `CohenDiv.java`,  we call `vtrace0`, `vtrace1` at the head of the outter and inner while loops find loop invariants  and  `vtrace2` before the function exit to find post conditions.
  * `vtraceX` takes a list of arguments that are variables in scope at the desired location. This tells DIG to find invariants over these variables.

* Next, we run DIG on `CohenDiv.java` or its byteclass version (compiled with `javac -g`) and discover the following invariants at `vtracesX` locations:

```sh
# in DIG's src directory
tnguyen@origin ~/d/src (dev)> python3 -O dig.py  ../benchmark/java/nla/CohenDiv.java -log 3
settings:INFO:2020-10-03 21:39:01.995144: dig.py ../benchmark/java/nla/CohenDiv.java -log 3
alg:INFO:analyze '../tests/paper/CohenDiv.java'
alg:INFO:compute symbolic states (18.65s)
alg:INFO:infer invs at 3 locs: vtrace0, vtrace2, vtrace1
alg:INFO:found 5 eqts (26.55s)
alg:INFO:found 67 ieqs (1.10s)
alg:INFO:found 377 minmax (2.55s)
alg:INFO:test 449 invs using 699 traces (0.93s)
alg:INFO:simplify 449 invs (1.79s)
* prog CohenDiv locs 3;  invs 25 (Eqt: 5, MP: 1, Oct: 19) V 6 T 3 D 2;  NL 5 (2) ;
-> time eqts 26.5s, ieqs 1.1s, minmax 2.5s, simplify 2.7s, symbolic_states 18.7s, total 51.9s
-> checks  0 () change depths 0 () change vals 0 ()
-> max  0 () change depths 0 ()
runs 1
rand seed 1601779141.99, test (6, 59)
vtrace0 (11 invs):
1. a*y - b == 0
2. q*y + r - x == 0
3. -r <= 0
4. -a <= 0
5. a - b <= 0
6. a - q <= 0
7. q - x <= 0
8. r - x <= 0
9. b - x <= 0
10. -a - y <= -1
11. min(q, y) - b <= 0
vtrace1 (8 invs):
1. a*y - b == 0
2. q*y + r - x == 0
3. -q <= 0
4. b - r <= 0
5. a - b <= 0
6. r - x <= 0
7. -b + y <= 0
8. -a - y <= -2
vtrace2 (6 invs):
1. q*y + r - x == 0
2. -r <= 0
3. -q <= 0
4. q - x <= 0
5. r - x <= 0
6. r - y <= -1
tmpdir: /var/tmp/dig_2282784602713568709_x0qxjt3s
```

### Other programs

* The directory `../benchmarks/java/nla` contains many programs having nonlinear invariants.


### Additional Options

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

## Setup

First, clone DIG

```sh
git clone https://github.com/unsat/dig.git
```

Then go to DIG's directory (`cd dig`).  Also make sure that you're in the right branch (e.g., `master` or `dev`).
To run DIG, you can either use the [provided  *docker* script](#using-docker) (easiest way) or [install DIG yourself](#installing-dig).

### Using DOCKER

```sh
# in DIG's directory

# build the docker image,
$ docker build . -t='dig'
...
...
# this will take some time as it will build a Linux image with all necessary dependencies to run DIG.  

# then run dig
$ docker run -it dig

# docker will drop you into a Linux prompt like below.
$ root@b53e0bd86c11:/dig/src#
```

You are now ready to use DIG, see instructions in the [USAGE](#usage) section

### Installing DIG
You can also install DIG yourself.  The tool has been tested using the following setups:

* Debian Linux `9` or `10` (64 bit)
* Python `3.9+`
* Sympy `1.8+`
* Microsoft Z3 SMT solver `4.8.3+`
* The following are only required if you want to analyze C or Java code.
  * Java JDK (Oracle `1.8.0_121` or OpenJDK `1.8.0_122`)
  * Java PathFinder and Symbolic Finder:
  * JPF (`java-8` branch, commit [`18a0c42de3e80be0c2ddcf0d212e376e576fcda0`](https://github.com/javapathfinder/jpf-core/commit/18a0c42de3e80be0c2ddcf0d212e376e576fcda0))
  * SPF (commit [`98a0e08fee323c15b651110dd3c28b2ce0c4e274`](https://github.com/SymbolicPathFinder/jpf-symbc/commit/98a0e08fee323c15b651110dd3c28b2ce0c4e274))

#### Installing Sympy and Z3

* Setup Sympy:
  * If you do not already have Sympy installed (e.g., doing `import sympy` in Python gives error), then the easiest way to install `sympy` is its recommeded way of using `anaconda`.
  * Download `https://docs.conda.io/en/latest/miniconda.html`, install `miniconda`
  * Run 
    * `/where/you/install/bin/conda install sympy`
    * `/where/you/install/bin/conda install z3-solver`
  
This should be enough to use `DIG` to infer invariants from [traces](#generating-invariants-from-traces). 

#### For Java files: install Java and Symbolic PathFinder

* Install Java 8: either the JDK from Oracle 1.8.0_121 or the OpenJDK packaged in Debian (`apt-get install -y default-jdk`, besure the version is 1.8.0_121 or 1.8.0_122).

* Install both Java PathFinder and the Symbolic Pathfinder extension

```sh
$ mkdir /PATH/TO/JPF
$ cd /PATH/TO/JPF
$ git clone https://github.com/javapathfinder/jpf-core #JPF
$ git clone https://github.com/SymbolicPathFinder/jpf-symbc #Symbolic extension

# build jpf
$ cd jpf-core
$ git checkout java-8  #switch to the java-8 branch
$ ant

#copy patched Listener file to SPF
$ cp /PATH/TO/dig/src/java/InvariantListenerVu.java jpf-symbc/src/main/gov/nasa/jpf/symbc

# build spf
$ cd jpf-symbc
$ ant

# sometimes it helps to rebuild jpf-core again
# cd jpf-core
$ ant


# Add the following to `~/.jpf/site.properties` (create `~/.jpf` if it doesn't exist)
jpf-core = /PATH/TO/JPF/jpf-core
jpf-symbc = /PATH/TO/JPF/jpf-symbc
extensions=${jpf-core},${jpf-symbc}
```

* Compile Java files in `java` directory for instrumenting Java byte classes

```sh
# in DIG's src directory
$ cd src/java
$ make
```

#### For C files: install the [CIVL symbolic execution tool](https://vsl.cis.udel.edu/civl/)

* Build CIL

```sh
# build CIL
$ git clone https://github.com/cil-project/cil.git
$ cd cil
$ ./configure ; make
```

* Compile the Ocaml files in `ocaml` directory for instrumenting C files (to CIVL format)

```sh
# in DIG's src directory
$ cd src/ocaml
$ edit Makefile  #point the OCAML_OPTIONS to where CIL is
$ make
```

* Get CIVL

```sh
$ wget --no-check-certificate https://vsl.cis.udel.edu/lib/sw/civl/1.20/r5259/release/CIVL-1.20_5259.tgz
$ tar xf CIVL-1.20_5259.tgz
$ ln -sf CIVL-1.20_5259 civl
$ ln -sf civl/lib/ lib


# Tell CIVL to use Z3  by editing the ~/.sarl file
prover {
 aliases = z3;
 kind = Z3;
 version = "4.8.7 - 64 bit";
 path = "/home/SHARED/Devel/Z3/z3/z3";
 timeout = 10.0;
 showQueries = false;
 showInconclusives = false;
 showErrors = true;
}

# test CIVL
$ /home/SHARED/Devel/JAVA/jdk/bin/java -jar /home/SHARED/Devel/CIVL/lib/civl-1.20_5259.jar verify -maxdepth=20 $DIG/tests/tools/cohendiv_civl.c
CIVL v1.20 of 2019-09-27 -- http://vsl.cis.udel.edu/civl
vtrace1: q = 0; r = X_x; a = 0; b = 0; x = X_x; y = X_y
path condition: (0<=(X_x-1))&&(0<=(X_y-1))
...

```

#### Setup Paths

* Put the following in your `~/.sh_profile`

```sh
# ~/.sh_profile
export Z3=PATH/TO/z3   #Z3 dir
export PYTHONPATH=$Z3/src/api/python:$PYTHONPATH
export JAVA_HOME=/PATH/TO/JAVA
export PATH=$JAVA_HOME/bin:$PATH
export JPF_HOME=/PATH/TO/JPF
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$JPF_HOME/jpf-symbc/lib/
```

* Some troubleshooting tips:
  * Make sure `sympy` is installed correctly so that you can do `python -c "import sympy"` without error.
  * Make sure Z3 is installed correctly so that you can do `python -c "import z3; z3.get_version()"` without error.
  * Use DIG with `-log 4` to enable detail logging information, also look at the `settings.py` for various settings on where DIG looks for external programs such as `java` and `javac`

---

## Publications

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

