/*
 * Purpose: Accumulate a scaled geometric sum a*(1+z+...+z^(c-1)).
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Primary benchmark collection: https://github.com/dynaroars/dig. No original
 * publication for this exact C variant has been verified.
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: z*x-x+a-a*z*y == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: Encoded domain: 0 <= z <= 10 and 1 <= k <= 10; a is unbounded here. The invariant has
 * degree 3 when a,z are variables. Original publication for this exact C variant is not
 * established.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}

void vtrace1(int x, int y, int z, int a, int k){}

int mainQ(int z, int a, int k){
    vassume(z >= 0);
    vassume(z <= 10);
    vassume(k > 0);
    vassume(k <= 10); 

    int x = a; int y = 1;  int c = 1;

    while (1){
	//assert(z*x-x+a-a*z*y == 0);
	vtrace1(x, y, z, a, k);

	if (!(c < k)) break;
	c = c + 1;
	x = x*z + a;
	y = y*z;

    }
    return x;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}

