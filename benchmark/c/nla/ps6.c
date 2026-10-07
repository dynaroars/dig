/*
 * Purpose: Accumulate powers of exponent 5: 1^5+...+y^5.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Mathematical background: NIST DLMF 24.4.7, sums of powers. This is background for the
 * derived equality, not a claim that NIST supplied this C program. https://dlmf.nist.gov/24.4#E7
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: 12*x-2*y**6-6*y**5-5*y**4+y**2 == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: The suffix is one more than the summed power. The polynomial has degree 6. Original
 * publication for this exact C variant is not established.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int k){}

int mainQ(int k){
    vassume(k >= 0);
    vassume(k <= 30); //if too large then overflow
     
    int y = 0;
    int x = 0;
    int c = 0;


    while(1){
	//assert(-2*pow(y,6) - 6*pow(y,5) - 5*pow(y,4) + pow(y,2) + 12*x == 0.0); //DIG Generated  (but don't uncomment, assertion will fail because of int overflow)	  

	vtrace1(x, y, k);

	if (!(c < k)) break;
	c = c + 1 ;
	y = y + 1;
	x=y*y*y*y*y+x;
    }
    return x;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}

