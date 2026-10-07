/*
 * Purpose: Approximate the nearest integer square root by successive subtraction.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: P. Freire, SQRT, Part I, square-root algorithm and mathematical proof.
 * https://www.pedrofreire.com/sqrt/sqrt1.en.html
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   internal_loop: 2*x+r**2-r-a == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: For root interpretation use a >= 0. Specification uses exact reals for x; floating-point
 * preservation requires representable values. Archived fail variant: no active trace calls in
 * freire1, freire2, or ps1; knuth calls sqrt from libm. Some archived drivers lack stdlib.h for
 * atoi.
 */
#include <stdio.h>
#include <assert.h>

int mainQ(int a){
     float x = ((double)a)/2.0;
     int r = 0;


     while(1){
	  //assert((double)a == 2*x + r*r - r); 
	  //%%%traces: int a, double x, int r
	  
	  if (!(x>r)) break;
	  x = x - r;
	  r = r + 1;
     }

     //assert(r==(int)round(sqrt(a)));
     return r;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}

