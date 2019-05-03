# DIG
DIG is a tool for generating (potentially **nonlinear**) numerical invariants using symbolic states extracted from a symbolic execution tool.

DIG is written in Python using the **SAGE** mathematics system. It infers invariants using dynamic execution (over execution traces) and checks those invariants using symbolic states and constraint solving.
DIG uses **Symbolic PathFinder** to collect symbolic states and uses the **Z3** SMT solver for constraint solving. 

The current version of DIG works with Java programs and raw program execution traces.  Previous versions also work with C and raw traces.


## Setup

First, clone DIG

```shell
git clone https://github.com/nguyenthanhvuh/dig.git
```
Then go to DIG's directory (`cd dig`).  Also make sure that you're in the `master` branch (if not, do `git checkout master`).
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

You are now ready to use DIG, see instructions in [USAGE](##usage)

### Installing DIG

You can install DIG yourself.  The tool has been tested using the following setup:

* Debian Linux 9 or 10 (64 bit)
* SageMath `8.7` (64 bit)
* Microsoft Z3 SMT solver `4.8.3`
* Java JDK (Oracle `1.8.0_121` or OpenJDK `1.8.0_122`)
* Java PathFinder and Symbolic Finder: 
  * JPF (`java-8` branch, commit [`18a0c42de3e80be0c2ddcf0d212e376e576fcda0`](https://github.com/javapathfinder/jpf-core/commit/18a0c42de3e80be0c2ddcf0d212e376e576fcda0))
  * SPF (commit [`98a0e08fee323c15b651110dd3c28b2ce0c4e274`](https://github.com/SymbolicPathFinder/jpf-symbc/commit/98a0e08fee323c15b651110dd3c28b2ce0c4e274))



#### Installing SAGE and Z3
* Setup SAGE: download a precompiled [SageMath](http://mirrors.mit.edu/sage/linux/64bit/index.html) binary
* Setup Z3: [download](https://github.com/Z3Prover/z3/releases) and build Z3 by following the instructions in its README file 
* To check that you have all needed stuff

```shell
# in DIG's src directory
$ cd src
$ sage check_requirements.py
...
...
Everything seems OK. Have fun with DIG!
```

#### Installing Java and PathFinder
* Install Java 8: either the JDK from Oracle 1.8.0_121 or the OpenJDK packaged in Debian (`apt-get install -y default-jdk`, besure the version is 1.8.0_121 or 1.8.0_122).

* Install both Java PathFinder and the Symbolic Pathfinder extension

```shell
$ mkdir /PATH/TO/JPF; 
$ cd /PATH/TO/JPF
$ git clone https://github.com/javapathfinder/jpf-core #JPF
$ git clone https://github.com/SymbolicPathFinder/jpf-symbc #Symbolic extension

#then add the following to `~/.jpf/site.properties` (create ~/.jpf if it doesn't exist)
jpf-core = /PATH/TO/JPF/jpf-core
jpf-symbc = /PATH/TO/JPF/jpf-symbc
extensions=${jpf-core},${jpf-symbc}


#build jpf
$ cd jpf-core
$ git checkout java-8  #switch to the java-8 branch
$ ant

#copy patched Listener file to SPF
$ cp /PATH/TO/dig/src/java/InvariantListenerVu.java jpf-symbc/src/main/gov/nasa/jpf/symbc

#build spf
$ cd jpf-symbc
$ ant
```

* Compile Java files in `java` directory for instrumenting Java byte classes

```shell
# in DIG's src directory
$ cd src/java
$ make
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
```

* Some troubleshooting tips:
  *  Make sure SAGE works, e.g., `sage` to run the SAGE interpreter or `sage --help`
  *  Make sure Z3 is installed correctly so that you can do `sage -c "import z3; z3.get_version()"` without error.


## Usage

### Generating invariants

Consider the following `CohenDiv.java` program

```java
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

* Next, we run DIG on `CohenDiv.java` and discover the following equality and inequality invariants at `vtracesX` locations:

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



### Other programs
The directory `tests/nla/` contains many programs having nonlinear invariants.

### Additional Info
To run doctests, use `sage -t`
```
$ export SAGE_PATH=$Z3/src/api/python:.
$ sage -t miscs.py
```

## Publications ##
Additional information on DIG can be found from these papers:

* ThanhVu Nguyen, Matthew Dwyer, and William Visser. SymInfer: Inferring Program Invariants using Symbolic States. In Automated Software Engineering (ASE). IEEE, 2017.


