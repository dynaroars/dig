/*
 * Purpose: Approximate an integer cube root by subtracting successively updated quadratic offsets.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: P. Freire, SQRT, Part I, Cube Root section.
 * https://www.pedrofreire.com/sqrt/sqrt1.en.html
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   internal_loop: 4*r**3-6*r**2+3*r+4*x-4*a-1 == 0.
 *   internal_loop: 4*s-12*r**2-1 == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: For root interpretation use positive integer a; this adaptation initializes r=1 even
 * when a=0. Specification uses exact reals; the C type differs in the archived fail variant.
 * Archived fail variant: no active trace calls in freire1, freire2, or ps1; knuth calls sqrt from
 * libm. Some archived drivers lack stdlib.h for atoi.
 */
#include <stdio.h>
#include <assert.h>

int mainQ(int a){
     float x,s;
     int r;
     x = (double)a;
     r = 1;
     s = 3.25;
     
     while (1){
	  //%%%traces: int a, double x, int r, double s
	  if(!(x-s > 0.0)) break;
	  
	  //assert(((int)(4*r*r*r - 6*r*r + 3*r) + (int)(4*x - 4*a)) == 1); 
	  //assert((int)(4*s) -12*r*r == 1); 
	  
	  x = x - s;
	  s = s + 6 * r + 3;
	  r = r + 1;
     }
     
     return r;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}

