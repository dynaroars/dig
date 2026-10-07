/*
 * Purpose: Compute integer quotient and remainder by doubling the divisor and subtracting chunks.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Primary benchmark collection: https://github.com/dynaroars/dig. No original
 * publication for this exact C variant has been verified.
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: x-q*y-r == 0.
 *   vtrace1: b-y*a == 0.
 *   vtrace2: x-q*y-r == 0.
 *   vtrace2: b-y*a == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: Encoded domain: x >= 1, y >= 1. At inner heads r >= b; r >= 2*b holds only when its loop
 * guard permits another doubling. At exit 0 <= r < y.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int q, int r, int a, int b, int x, int y){}
void vtrace2(int q, int r, int a, int b, int x, int y){}

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
    
    return q;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


