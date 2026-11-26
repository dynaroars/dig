/*
 * Purpose: Count iterations by increasing x and y together.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Mathematical background: NIST DLMF 24.4.7, sums of powers. This is background for the
 * derived equality, not a claim that NIST supplied this C program. https://dlmf.nist.gov/24.4#E7
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   internal_loop: x-y == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: This ps1 implementation adds 1, so its basic equality is linear; it does not sum the
 * integers 1 through y. Original publication for this exact C variant is not established.
 * Archived fail variant: no active trace calls in freire1, freire2, or ps1; knuth calls sqrt from
 * libm. Some archived drivers lack stdlib.h for atoi.
 */
#include <stdio.h>
#include <assert.h>
int mainQ(int k){
     assert (k>=0);          
     int y = 0;
     int x = 0;
     int c = 0;

     while(1){
	  //%%%traces: int x, int y, int k
	  if (!(c < k)) break;
    
	  c = c + 1;
	  y = y + 1;
	  x = x + 1;
     }
     return x;
}



int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}

