# DIG
DIG is a tool for generating (potentially **nonlinear**) numerical invariants using symbolic states extracted from a symbolic execution tool.

DIG is written in Python using the **SAGE** mathematics system. It infers invariants using dynamic execution (over execution traces) and checks those invariants using symbolic states and constraint solving.
DIG uses **Symbolic PathFinder** to collect symbolic states and uses the **Z3** SMT solver for constraint solving. 

The current version of DIG works with Java programs, C programs, and concrete program execution traces.


## Setup

First, clone DIG

```shell
git clone https://github.com/unsat/dig.git
```
Then go to DIG's directory (`cd dig`).  Also make sure that you're in the right branch (e.g., `master` or `dev`).
To run DIG, you can either use the [provided  *docker* script](#using-docker) (easiest way) or [install DIG yourself](#installing-dig).

### Using DOCKER

```
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

### Using DOCKER

```
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

#### Installing SAGE and Z3
* Setup SAGE: download a precompiled [SageMath](http://mirrors.mit.edu/sage/linux/64bit/index.html) binary
* Setup Z3: [download](https://github.com/Z3Prover/z3/releases) and build Z3 by following the instructions in its README file 
* To check that you have all needed stuff

```shell
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

```shell
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

```shell
# in DIG's src directory
$ cd src/java
$ make
```

#### For C files: install the [CIVL symbolic execution tool](https://vsl.cis.udel.edu/civl/)

* Build CIL
```shell
$ git clone https://github.com/cil-project/cil.git
$ cd cil
$ ./configure ; make
```

* Compile the Ocaml files in `ocaml` directory for instrumenting C files (to CIVL format)

```shell
# in DIG's src directory
$ cd src/ocaml
$ edit Makefile  #point the OCAML_OPTIONS to where CIL is
$ make
```

* Get CIVL

```shell
$ wget --no-check-certificate https://vsl.cis.udel.edu/lib/sw/civl/1.20/r5259/release/CIVL-1.20_5259.tgz
$ tar xf CIVL-1.20_5259.tgz
$ ln -sf CIVL-1.20_5259 civl
$ ln -sf civl/lib/ lib

# test CIVL
/home/SHARED/Devel/JAVA/jdk/bin/java -jar /home/SHARED/Devel/CIVL/lib/civl-1.20_5259.jar verify -maxdepth=20 $DIG/tests/tools/cohendiv_civl.c
CIVL v1.20 of 2019-09-27 -- http://vsl.cis.udel.edu/civl
vtrace1: q = 0; r = X_x; a = 0; b = 0; x = X_x; y = X_y
path condition: (0<=(X_x-1))&&(0<=(X_y-1))
...

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
```

#### Setup Paths

* Put the following in your `~/.bash_profile`

```shell
#~/.bash_profile
export Z3=PATH/TO/z3   #Z3 dir
export SAGE=PATH/TO/sage  #where your SAGE dir is
export PYTHONPATH=$Z3/src/api/python:$PYTHONPATH
export JAVA_HOME=/PATH/TO/JAVA
export PATH=$SAGE:$JAVA_HOME/bin:$PATH
export JPF_HOME=/PATH/TO/JPF
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$JPF_HOME/jpf-symbc/lib/
```

* Some troubleshooting tips:
  *  Make sure SAGE works, e.g., `sage` to run the SAGE interpreter or `sage --help`
  *  Make sure Z3 is installed correctly so that you can do `sage -c "import z3; z3.get_version()"` without error.
  *  Use DIG with `-log 4` to enable detail logging information, also look at the `settings.py` for various settings on where DIG looks for external programs such as `java` and `javac`

## Usage

You can use DIG to generate invariants from a [program](#generating-invariants-from-a-program) (either a Java file `.java` or a bytecode file `.class`), or a [trace file](#generating-invariants-from-traces) (a plain text file consisting of concrete values of variables).

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
          assert(x>0 && y>0);

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
  * Notice that `vtraceX` takes a list of arguments that are variables in scope at the desired location. This tells DIG to find invariants over these specific variables.

* Next, we run DIG on `CohenDiv.java` or its byteclass version (compiled with `javac -g`) and discover the following equality and inequality invariants at `vtracesX` locations:

```
#in DIG's src directory
$ sage -python -O dig.py ../tests/nla/CohenDiv.java -log 3
alg:INFO:analyze '../tests/nla/CohenDiv.java'
alg:INFO:gen eqts at 2 locs
alg:INFO:infer 3 eqts in 13.8612298965s
alg:INFO:gen ieqs at 2 locs
cegirIeqs:INFO:check upperbounds for 104 terms at 2 locs
alg:INFO:infer 52 ieqs in 9.20348906517s
alg:INFO:test 55 invs on 291 traces
alg:INFO:uniqify 47 invs
*** '../tests/nla/CohenDiv.java', 2 locs, invs 10 (3 eqts), inps 83 time 26.650242 s, rand 63:
vtrace1: q*y + r - x == 0 p, a*y - b == 0 p, r - x <= 0 p, -a - q <= -1 p, -b <= -1 p, b - r <= 0 p
vtrace2: q*y + r - x == 0 p, -q - x <= -1 p, -r <= 0 p, r - y <= -1 p
```



#### Other programs
The directory `tests/nla/` contains many programs having nonlinear invariants.


### Generating Invariants From Traces

DIG can infer invariants directly from a file concreting program execution traces.  Below is an example of traces generated when running the above `CohenDiv` program with various inputs

```
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

```
# in DIG's src directory
$ sage -python -O dig.py ../tests/traces/CohenDiv.tcs -log 3
alg:INFO:analyze '/home/tnguyen/Dropbox/code/dig/tests/traces/cohendiv.tcs'
alg:INFO:test 48 invs using 397 traces in 0.12s
alg:INFO:simplify 45 invs in 0.72s
*** '/home/tnguyen/Dropbox/code/dig/tests/traces/cohendiv.tcs', 2 locs, invs 16 (Oct: 14, Eqt: 2), traces 397, inps 0, time 10.11s, rand seed 1564806847.44, test 99 40:
vtrace1 (11 invs):
1. a*y - b == 0 None
2. b - r <= 0 None
3. q - x <= -1 None
4. r - x <= 0 None
5. -q <= 0 None
6. -b <= -1 None
7. -y <= -1 None
8. -q - r <= -7 None
9. -x + y <= -2 None
10. -x - y <= -10 None
11. -x <= -7 None
vtrace2 (5 invs):
1. q*y + r - x == 0 None
2. r - y <= -1 None
3. -r <= 0 None
4. -x - y <= -10 None
5. -x <= -1 None
```
Note that most of the inequality results here are spurious, i.e., they are correct with the given traces, but not real invariants.  If given the program source code as [shown above](#generating-invariants-from-a-program), then DIG can check and remove spurious results.


### Additional Info
To run doctests
```
make test
```

## Publications ##
Additional information on DIG can be found from these papers:

* ThanhVu Nguyen, Matthew Dwyer, and William Visser. SymInfer: Inferring Program Invariants using Symbolic States. In Automated Software Engineering (ASE). IEEE, 2017.


