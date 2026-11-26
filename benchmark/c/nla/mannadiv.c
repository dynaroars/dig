/*
 * Purpose: Compute quotient by consuming one dividend unit at a time and cycling a remainder
 * counter.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Primary benchmark collection: https://github.com/dynaroars/dig. No original
 * publication for this exact C variant has been verified.
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: q*y+a+b-x == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: Encoded domain: x >= 0, y >= 1. At loop heads 0 <= a < y, b >= 0; exit b=0 gives
 * x=q*y+a. Original publication for this exact C variant is not established; the filename alone
 * is not an attribution.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int q, int a, int b, int x, int y){}  
//void vtrace2(int q, int a, int x, int y){}

int mainQ(int x, int y){
     
    vassume(x >= 0);
    vassume(y >= 1);   //can also be y!=0, but CIVL will give disj
     
    int q, a, b; 
    q = 0;
    a = 0;
    b = x;

    while(1) {
	//assert(q* y + a + b == x);
	vtrace1(q, a, b, x, y);
	if(!(b != 0)) break;
	  
	if (a + 1 == y) {
	    q = q + 1;
	    a = 0;
	    b = b - 1;
	}
	else {
	    a = a + 1;
	    b = b - 1;
	}
    }
    //vtrace2(q, a, x, y); 
    //assert(q == x / y);
    return q;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

