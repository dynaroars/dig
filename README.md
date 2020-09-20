# DIG

**DIG** is a tool for generating (potentially **nonlinear**) numerical invariants using symbolic states extracted from a symbolic execution tool. DIG can infer equalities such as `x+y=5`, `x*y=z`, `x*3y^3 + 2*zw + pq + q^3 = 3`, inequalities such as `x <= y^2 + 3`, and min/max inequalities such as `max(x,y) <= z + 2`.  The user can also use *terms* to represent desired information, e.g., $t = 2^x$, and have DIG infer invariants over terms.

DIG is written in Python using the **SAGE** mathematics system. It infers invariants using dynamic execution (over execution traces) and checks those invariants using symbolic states and constraint solving.
DIG uses **Symbolic PathFinder** to collect symbolic states and uses the **Z3** SMT solver for constraint solving.

The current version of DIG works with programs written in Java, Java bytecode, and C. The tool also infers  invariants direclty from given concrete program execution traces.

## Usage

You can use DIG to generate invariants from a [program](#generating-invariants-from-a-program) (either a Java file `.java`, a bytecode file `.class`, or a C file `.c`), or a [trace file](#generating-invariants-from-traces) (a plain text file consisting of concrete values of variables).

### Generating Invariants From a Program

Consider the following `CohenDiv.java` program

```java
// in DIG's src directory
// $ less ../test/nla/CohenDiv.java

public class CohenDiv {
     public static void vtrace1(int q, int r, int a, int b, int x, int y){}
     public static void vtrace2(int x, int y, int q, int r){}

     public static void main (String[] args) {}

     public static int mainQ_cohendiv(int x, int y) {
          assert(x>=0 && y>=1);

          int q=0;
          int r=x;
          int a=0;
          int b=0;

          while(true) {
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

* To find invariants at some location, we declare a function `vtraceX` where `X` is some distinct number and call that function at the desired location.
  * For example, in `CohenDiv.java`,  we call `vtrace1` and `vtrace2` at the head of the inner while loop and before the function exit to find loop invariants and post conditions.
  * Notice that `vtraceX` takes a list of arguments that are variables in scope at the desired location. This tells DIG to find invariants over these variables.

* Next, we run DIG on `CohenDiv.java` or its byteclass version (compiled with `javac -g`) and discover the following equality and inequality invariants at `vtracesX` locations:

```bash
# in DIG's src directory
tnguyen@debian ~/dig/src> sage -python -O dig.py  ../tests/paper/CohenDiv.java   -log 3
settings:INFO:2020-06-30 13:13:43.240386: dig.py ../tests/paper/CohenDiv.java -log 3
alg:INFO:analyze '../tests/paper/CohenDiv.java'
alg:INFO:compute symbolic states (6.03s)
alg:INFO:infer invs at 2 locs: vtrace2, vtrace1
alg:INFO:found 3 eqts (10.00s)
alg:INFO:found 31 ieqs (0.41s)
alg:INFO:test 34 invs using 223 traces (0.08s)
alg:INFO:simplify 34 invs (0.58s)
vtrace1 (7 invs):
1. q*y + r - x == 0
2. a*y - b == 0
3. b - x <= 0
4. -y <= -1
5. -r + y <= 0
6. -q <= 0
7. -b <= -1
vtrace2 (4 invs):
1. q*y + r - x == 0
2. r - y <= -1
3. -r <= 0
4. -q <= 0
run time 17.44s, result dir: /var/tmp/dig_553402345795059927_3r_6gwkz
*** prog CohenDiv, runs 1, locs 2, V 6, T 3, D 2, NL 3, traces 223, inps 72
time eqts 10.00s, ieqs 0.41s, simplify 0.66s, symbolic_states 6.03s, total 17.44s
invs 11 (Eqt: 3, Oct: 8), check solver calls 0 (), check change depths 0 (), check change vals 0 (), max solver calls 0 (), max change depths 0 (), max change vals 0 ()
rand seed 1593540823.24, test (50, 75)
vtrace1 (7 invs):
1. q*y + r - x == 0
2. a*y - b == 0
3. b - x <= 0
4. -y <= -1
5. -r + y <= 0
6. -q <= 0
7. -b <= -1
vtrace2 (4 invs):
1. q*y + r - x == 0
2. r - y <= -1
3. -r <= 0
4. -q <= 0
alg:INFO:tmpdir: /var/tmp/dig_553402345795059927_3r_6gwkz
```

#### Other programs

The directory `tests/nla/` contains many programs having nonlinear invariants.

### Generating Invariants From Traces

DIG can infer invariants directly from a file concreting program execution traces.  Below is an example of traces generated when running the above `CohenDiv` program with various inputs

```bash
# in DIG's src directory
$ less ../test/traces/CohenDiv.tcs
vtrace1: I q, I r, I a, I b, I x, I y
vtrace1: 4, 8, 1, 4, 24, 4
vtrace1: 16, 89, 1, 13, 297, 13
vtrace1: 8, 138, 4, 76, 290, 19
vtrace1: 0, 294, 8, 192, 294, 24
vtrace1: 64, 36, 4, 16, 292, 4
...
vtrace2: I x, I y, I q, I r
vtrace2: 280, 24, 11, 16
vtrace2: 352, 11, 32, 0
vtrace2: 22, 298, 0, 22
vtrace2: 274, 275, 0, 274
vtrace2: 2, 287, 0, 2
...
```

```bash
# in DIG's src directory
tnguyen@debian ~/d/src> sage -python -O dig.py ../tests/traces/CohenDiv.tcs -log 3
settings:INFO:2020-06-30 15:26:53.384339: dig.py ../tests/traces/CohenDiv.tcs -log 3
alg:INFO:analyze '../tests/traces/CohenDiv.tcs'
alg:INFO:test 30 invs using 181 traces (0.96s)
alg:INFO:simplify 26 invs (0.42s)
vtrace1 (6 invs):
1. q*y + r - x == 0
2. -y <= -1
3. -x <= -1
4. -x - y <= -10
5. -r <= 0
6. -q <= 0
vtrace2 (5 invs):
1. q*y + r - x == 0
2. r - y <= -1
3. -x <= -1
4. -x - y <= -10
5. -r <= 0
```

Note that most of the inequality results here are spurious, i.e., they are correct with the given traces, but not real invariants.  If given the program source code as [shown above](#generating-invariants-from-a-program), then DIG can check and remove spurious results.

### Additional Options

Most of DIG's behaviors can be controlled by the users.  Use `-h` or `--help` option to see options that can be passed into DIG. Below we show several ones

#### Specify max degree for equalities

By default, DIG automatically to find equalities up to certain degree.  We can specify this degree directly with `-maxdeg X`

```bash
tnguyen@debian ~/dig/src> sage -python -O dig.py  ../tests/paper/CohenDiv.java   -log 3 -maxdeg 2 -noieqs  #find equalities up to degree 2 and donot infer inequalities
...
```

#### Infer Min/Max

We can find *min/max* inqualities with the option `-dominmax`.  This typically will take some time depends on the program.  Also, DIG might not return any min/max results if they are not available or can be implied by other invariants in the program.

```bash
tnguyen@debian ~/dig/src> sage -python -O dig.py  ../tests/paper/CohenDiv.java  -log 3  -maxdeg 2 -noieqs -dominmax  #find equalities up to degree 2, donot infer inequalities, infer min/max inequalities
...
vtrace1 (7 invs):
1. q*y + r - x == 0
2. a*y - b == 0
3. min(r, x, 0) - (a - 1) <= 0
4. min(q, r, y, 0) - (b - 1) <= 0
5. min(b, y, 0) - q <= 0
6. max(r, 0) - x <= 0
7. max(a, b, y, 0) - r <= 0
vtrace2 (5 invs):
1. q*y + r - x == 0
2. min(y, 0) - r <= 0
3. min(r, y, 0) - q <= 0
4. min(q, 0) - (y - 1) <= 0
5. (r + 1) - max(y, 0) <= 0
```

#### Customizing Inequalities

By default, DIG infers octagonal inequalities (i.e., linear inequalities among 2 variables with coefs in in the set {-1,0,1}).  But we can customize DIG to find more expression inequalities (of course, with the trade-off that it takes more time to generate more expressive invs).

Below we use a different example `Sqrt1.java` to demonstrate

```bash
tnguyen@debian ~/dig/src> sage -python -O dig.py  ../tests/paper/CohenDiv.java  -log 3  -noeqts  # for demonstration, only find default, octagonal, ieq's.
...
1. a <= 10
2. a - n <= 0
3. -t <= -1
4. -s <= -1
5. -n + t <= 2
6. -a <= 0


tnguyen@debian ~/dig/src> sage -python -O dig.py  ../tests/paper/Sqrt1.java  -log 4 -noeqts -ideg 2  # find nonlinear octagonal inequalities
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

tnguyen@debian ~/dig/src> timeout 900 sage -python -O dig.py  ../tests/paper/Sqrt1.java  -log 4 -noeqts -icoefs 2  # find linear inequalities with coefs in {2,-1,0,1,2}
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

## Setup

First, clone DIG

```bash
git clone https://github.com/unsat/dig.git
```

Then go to DIG's directory (`cd dig`).  Also make sure that you're in the right branch (e.g., `master` or `dev`).
To run DIG, you can either use the [provided  *docker* script](#using-docker) (easiest way) or [install DIG yourself](#installing-dig).

### Using DOCKER

```bash
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

You are now ready to use DIG, see instructions in [USAGE](#usage) below

### Installing DIG

You can install DIG yourself.  The tool has been tested using the following setup:

* Debian Linux 9 or 10 (64 bit)
* SageMath `9.0` (64 bit)
* Microsoft Z3 SMT solver `4.8.3`
* Java JDK (Oracle `1.8.0_121` or OpenJDK `1.8.0_122`)
* Java PathFinder and Symbolic Finder:
  * JPF (`java-8` branch, commit [`18a0c42de3e80be0c2ddcf0d212e376e576fcda0`](https://github.com/javapathfinder/jpf-core/commit/18a0c42de3e80be0c2ddcf0d212e376e576fcda0))
  * SPF (commit [`98a0e08fee323c15b651110dd3c28b2ce0c4e274`](https://github.com/SymbolicPathFinder/jpf-symbc/commit/98a0e08fee323c15b651110dd3c28b2ce0c4e274))

#### Installing SAGE and Z3

* Setup SAGE: download a precompiled [SageMath](http://mirrors.mit.edu/sage/linux/64bit/index.html) binary
* Setup Z3: [download](https://github.com/Z3Prover/z3/releases) and build Z3 by following the instructions in its README file
* To check that you have all needed stuff

```bash
# in DIG's src directory
$ cd src
$ sage helpers/check_requirements.py
...
...
Everything seems OK. Have fun with DIG!
```

#### For Java files: installing Java and Symbolic PathFinder

* Install Java 8: either the JDK from Oracle 1.8.0_121 or the OpenJDK packaged in Debian (`apt-get install -y default-jdk`, besure the version is 1.8.0_121 or 1.8.0_122).

* Install both Java PathFinder and the Symbolic Pathfinder extension

```bash
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

```bash
# in DIG's src directory
$ cd src/java
$ make
```

#### For C files: install the [CIVL symbolic execution tool](https://vsl.cis.udel.edu/civl/)

* Build CIL

```bash
# build CIL
$ git clone https://github.com/cil-project/cil.git
$ cd cil
$ ./configure ; make
```

* Compile the Ocaml files in `ocaml` directory for instrumenting C files (to CIVL format)

```bash
# in DIG's src directory
$ cd src/ocaml
$ edit Makefile  #point the OCAML_OPTIONS to where CIL is
$ make
```

* Get CIVL

```bash
$ wget --no-check-certificate https://vsl.cis.udel.edu/lib/sw/civl/1.20/r5259/release/CIVL-1.20_5259.tgz
$ tar xf CIVL-1.20_5259.tgz
$ ln -sf CIVL-1.20_5259 civl
$ ln -sf civl/lib/ lib


# Tell CIVL to use Z3  by editing the ~/.sarl file
prover {
 aliases = z3;
 kind = Z3;
 version = "4.8.7 - 64 bit";
 path = "/home/SHARED/Devel/Z3/z3/build/z3";
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

* Put the following in your `~/.bash_profile`

```bash
# ~/.bash_profile
export Z3=PATH/TO/z3   #Z3 dir
export SAGE=PATH/TO/sage  #where your SAGE dir is
export PYTHONPATH=$Z3/src/api/python:$PYTHONPATH
export JAVA_HOME=/PATH/TO/JAVA
export PATH=$SAGE:$JAVA_HOME/bin:$PATH
export JPF_HOME=/PATH/TO/JPF
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$JPF_HOME/jpf-symbc/lib/
```

* Some troubleshooting tips:
  * Make sure SAGE works, e.g., `sage` to run the SAGE interpreter or `sage --help`
  * Make sure Z3 is installed correctly so that you can do `sage -c "import z3; z3.get_version()"` without error.
  * Use DIG with `-log 4` to enable detail logging information, also look at the `settings.py` for various settings on where DIG looks for external programs such as `java` and `javac`

### Additional Info

To run doctests

```bash
make test
```

## Publications

Additional information on DIG can be found from these papers:

* ThanhVu Nguyen, Matthew Dwyer, and William Visser. SymInfer: Inferring Program Invariants using Symbolic States. In Automated Software Engineering (ASE). IEEE, 2017.
* ThanhVu Nguyen, Timos Antopoulos, Andrew Ruef, and Michael Hicks. A Counterexample-guided Approach to Finding Numerical Invariants. In 11th Joint Meeting on Foundations of Software Engineering (ESEC/FSE), pages 605--615. ACM, 2017.
* ThanhVu Nguyen, Deepak Kapur, Westley Weimer, and Stephanie Forrest. DIG: A Dynamic Invariant Generator for Polynomial and Array Invariants. Transactions on Software Engineering Methodology (TOSEM), 23(4):30:1--30:30, 2014.
* ThanhVu Nguyen, Deepak Kapur, Westley Weimer, and Stephanie Forrest. Using Dynamic Analysis to Generate Disjunctive Invariants. In 36th International Conference on Software Engineering (ICSE), pages 608--619. IEEE, 2014.
* ThanhVu Nguyen, Deepak Kapur, Westley Weimer, and Stephanie Forrest. Using Dynamic Analysis to Discover Polynomial and Array Invariants. In 34th International Conference on Software Engineering (ICSE), pages 683--693. IEEE, 2012.

## ACKNOWLEDGEMENTS

* This project is supported in part by NSF grant CCF-1948536 and ARO grant W911NF-19-1-0054.
