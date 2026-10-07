/*
 * Purpose: Search increasing trial divisors using updated remainders and four conditional branches.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Primary benchmark collection: https://github.com/dynaroars/dig. No original
 * publication for this exact C variant has been verified.
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: d**2*q-2*q*d-4*r*d+4*k*d+8*r-8*n == 0.
 *   vtrace1: k*t-t**2 == 0.
 *   vtrace1: (d-a)*(k-t) == 0.
 *   vtrace2: d**2*q-2*q*d-4*r*d+4*k*d+8*r-8*n == 0.
 *   vtrace2: k*t-t**2 == 0.
 *   vtrace2: (d-a)*(k-t) == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: The code attributes the algorithm to Knuth. Use n >= 0, a > 2 for the divisor-search
 * interpretation; only a > 2 is enforced. The helper computes floor(sqrt(n)). Exact book section
 * for this C implementation has not been established.
 */
#include <stdio.h>
#include <stdlib.h>
void vassume(int b){}
void vtrace1(int n, int a, int r, int k, int q, int d, int s, int t){}
void vtrace2(int n, int a, int r, int k, int q, int d, int s, int t){}

static int isqrt(int n) { int s = 0; while ((s+1)*(s+1) <= n) s++; return s; }

int mainQ(int n, int a){
     //algorithm searching for a divisor for factorization, by Knuth
    vassume(a > 2);
     int r,k,q,d,s,t;
     d=a;
     r= n % d;
     t = 0;

     k=n % (d-2);
     q=4*(n/(d-2) - n/d);
     s=isqrt(n);

     while(1){
	  //assert(d*d*q - 2*q*d - 4*r*d + 4*k*d  + 8*r == 8*n);
	  //assert(k*t == t*t);
	  //assert(d*d*q - 2*d*q - 4*d*r + 4*d*t + 4*a*k - 4*a*t - 8*n + 8*r == 0);
	  //assert(d*k - d*t - a*k + a*t == 0);       
	  //%%%traces: int n, int a, int r, int k, int q, int d, int s, int t
	 vtrace1(n,a,r,k,q,d,s,t);

	  if (!((s>=d)&&(r!=0))) break;

	  if (2*r-k+q<0){
	       t=r;
	       r=2*r-k+q+d+2;
	       k=t;
	       q=q+4;
	       d=d+2;
	  } 
	  else if ((2*r-k+q>=0)&&(2*r-k+q<d+2)){
	       t=r;
	       r=2*r-k+q;
	       k=t;
	       d=d+2;
	  }
	  else if ((2*r-k+q>=0)&&(2*r-k+q>=d+2)&&(2*r-k+q<2*d+4)){
	       t=r;
	       r=2*r-k+q-d-2;
	       k=t;
	       q=q-4;
	       d=d+2;
	  }
	  else {/* ((2*r-k+q>=0)&&(2*r-k+q>=2*d+4)) */
	       t=r;
	       r=2*r-k+q-2*d-4;
	       k=t;
	       q=q-8;
	       d=d+2;
	  }

     }
     vtrace2(n,a,r,k,q,d,s,t);
     return d;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

