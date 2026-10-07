/*
 * Purpose: Accumulate 1+z+...+z^(c-1), while tracking y=z^(c-1).
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Primary benchmark collection: https://github.com/dynaroars/dig. No original
 * publication for this exact C variant has been verified.
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: 1+x*z-x-z*y == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: Encoded domain: 0 <= z <= 10 and 1 <= k <= 10. Original publication for this exact C
 * variant is not established.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int z, int k){}

int mainQ(int z, int k){
    vassume(z>=0);
    vassume(z<=10);
    vassume(k>0);
    vassume(k<=10);

    int x = 1; int y = 1; int c = 1;

    while (1){
	//assert(1+x*z-x-z*y==0);
	vtrace1(x, y, z, k);
	  
	if(!(c < k)) break;
	c = c + 1;
	x = x*z + 1;
	y = y*z;
    }
    return x;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));

}

