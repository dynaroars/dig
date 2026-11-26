/*
 * Purpose: Accumulate powers of exponent 1: 1^1+...+y^1.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Mathematical background: NIST DLMF 24.4.7, sums of powers. This is background for the
 * derived equality, not a claim that NIST supplied this C program. https://dlmf.nist.gov/24.4#E7
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: 2*x-y**2-y == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: The suffix is one more than the summed power. The polynomial has degree 2. Original
 * publication for this exact C variant is not established.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int k){}

int mainQ(int k){
    vassume(k >=0);
    vassume(k<=30);
     
    int y = 0;
    int x = 0;
    int c = 0;


    while(1){
	vtrace1(x, y, k);
	if (!(c < k)) break;
	c = c +1 ;
	y=y +1;
	x=y+x;
    }
    return x;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}

