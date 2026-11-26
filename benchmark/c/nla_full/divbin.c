/*
 * Purpose: Compute a binary long-division quotient, first doubling then halving a working divisor.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Rodriguez-Carbonell and Kapur, ISSAC 2004, section 6: divbin; reference [12] is A.
 * Kaldewaij, Programming: The Derivation of Algorithms (1990).
 * https://www.cs.unm.edu/~kapur/mypapers/issac04enric.pdf
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: q == 0.
 *   vtrace1: r-A == 0.
 *   vtrace2: A-q*b-r == 0.
 *   vtrace3: A-q*b-r == 0.
 *   vtrace3: b-B == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: Intended division domain: A >= 0, B >= 1. nla enforces only B >= 1; nla_full also
 * enforces A > 0. Exit gives A = q*B+r and 0 <= r < B on the intended domain.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int A, int B, int q, int b, int r){}
void vtrace2(int A, int B, int q, int b, int r){}
void vtrace3(int A, int B, int q, int b, int r){}

int mainQ(int A, int B){
    vassume(A > 0 && B > 0);
 
    int q = 0;
    int r = A;
    int b = B;

    while(1){
	vtrace1(A, B, q, b, r);
	if (!(r>=b)) break;
	b=2*b;
    }


    while(1){
	//assert(A == q*b + r && r >= 0);
	vtrace2(A, B, q, b, r);
	if (!(b!=B)) break;
	  
	q = 2*q;
	b = b/2;
	if (r >= b) {
	    q = q + 1;
	    r = r - b;
	}
    }
    vtrace3(A, B, q, b, r);
    return q;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

