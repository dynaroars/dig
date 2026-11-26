/*
 * Purpose: Compute extended GCD with subtraction and track Bezout coefficients.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Primary benchmark collection: https://github.com/dynaroars/dig. No original
 * publication for this exact C variant has been verified.
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: a-x*p-y*r == 0.
 *   vtrace1: b-x*q-y*s == 0.
 *   vtrace1: p*s-r*q-1 == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: Encoded domain: x >= 1, y >= 1. Exit has a=b=gcd(x,y). The determinant remains +1 for
 * these subtraction updates.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int a, int b, int p, int r, int q, int s){}

int mainQ(int x, int y){
    vassume(x >= 1);
    vassume(y >= 1);
    
    int a,b,p,q,r,s;
    
    a = x;
    b = y;
    p = 1;
    q = 0;
    r = 0;
    s = 1;

    while(1){
	/* assert(1 == p*s - r*q); */
	/* assert(a == y*r + x*p); */
	/* assert(b == x*q + y*s); */
	  
	vtrace1(x, y, a, b, p, r, q, s);
	
	if(!(a!=b)) break;
	  
	if (a > b) {
	    a = a - b; 
	    p = p - q; 
	    r = r - s;
	}
	else {
	    b = b - a; 
	    q = q - p; 
	    s = s - r;}
    }
    return a;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

