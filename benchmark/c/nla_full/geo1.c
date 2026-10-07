/*
 * Purpose: Accumulate 1+z+...+z^(c-1), while tracking y=z^c.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Primary benchmark collection: https://github.com/dynaroars/dig. No original
 * publication for this exact C variant has been verified.
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: x*z-x-y+1 == 0.
 *   vtrace2: x-y+1 == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: c starts at 1, so k=0 still observes the initialized sum x=1. Between vtrace1 and
 * vtrace2, x is multiplied by z-1; this changes the appropriate equality at the exit trace.
 * Original publication for this exact C variant is not established.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int x, int y, int z, int k){}
void vtrace2(int x, int y, int z, int k){}

int mainQ(int z, int k){
    vassume(z >= 0);
    vassume(z <= 10);
    vassume(k >= 0);
    vassume(k <= 10);
	    
    int x = 1; int y = z; int c = 1;

    while (1){
	//assert(x*z - x - y + 1 == 0);
	//%%%traces: int x, int y, int z, int k
	vtrace1(x, y, z, k);
	if(!(c < k)) break;
	  
	c = c + 1;
	x = x*z + 1;
	y = y*z;

    }//geo1

    x = x *(z - 1);
    vtrace2(x, y, z, k);
    return x;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));

}
