/*
 * Purpose: Compute floor(sqrt(n)) by increasing r until its next square exceeds n.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Primary benchmark collection: https://github.com/dynaroars/dig. No original
 * publication for this exact C variant has been verified.
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: r*r <= n.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: Encoded domain: 0 <= n <= 100. At the final trace also n < (r+1)^2; that strict
 * inequality is not an invariant of all earlier traces. Original attribution for this exact C
 * variant is not established.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int n, int r){}

int mainQ(int n){
    vassume(n >= 0);
    vassume(n <= 100);

    int r = 0;
    while ((r+1)*(r+1) <= n){
	vtrace1(n, r);
	r = r + 1;
    }
    vtrace1(n, r);
    return r;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}
