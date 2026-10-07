/*
 * Purpose: Generate successive integer cubes using first and second finite differences.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Rodriguez-Carbonell and Kapur, Automatic Generation of Polynomial Loop Invariants:
 * Algebraic Foundations, ISSAC 2004, section 6: cohencu; reference [2] is E. Cohen, Programming
 * in the 1990s (1990). https://www.cs.unm.edu/~kapur/mypapers/issac04enric.pdf
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: x-n**3 == 0.
 *   vtrace1: y-3*n**2-3*n-1 == 0.
 *   vtrace1: z-6*n-6 == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: The guard n <= a advances to a+1 for a >= 0; the returned value is then (a+1)^3.
 */
#include <stdio.h>
#include <stdlib.h>

void vtrace1(int a, int n, int x, int y, int z){}
//void vtrace2(int a, int n, int x, int y, int z){}

int mainQ(int a){
    int n,x,y,z;

    n=0; x=0; y=1; z=6;

    while(1){
	//assert(z == 6*n + 6);
	//assert(y == 3*n*n + 3*n + 1);
	//assert(x == n*n*n);

	vtrace1(a, n, x, y, z);
	if(!(n<=a)) break;
       
	n=n+1;
	x=x+y;
	y=y+z;
	z=z+6;
    }
    //vtrace2(a, n, x, y, z);
    return x;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}

