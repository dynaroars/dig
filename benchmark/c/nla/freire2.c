/*
 * Purpose: Approximate an integer cube root by subtracting successively updated quadratic offsets.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: P. Freire, SQRT, Part I, Cube Root section.
 * https://www.pedrofreire.com/sqrt/sqrt1.en.html
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: 4*r**3-6*r**2+3*r+4*x-4*a-1 == 0.
 *   vtrace1: 4*s-12*r**2-1 == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: For root interpretation use positive integer a; this adaptation initializes r=1 even
 * when a=0. Specification uses exact reals; the C type differs in the archived fail variant.
 */
/* Freire's algorithm for the closest integer to cbrt(a).
 * see: http://www.pedrofreire.com/sqrt/sqrt1.en.html
 * loop invariant (over the reals): 4*r*r*r - 6*r*r + 3*r + 4*x - 4*a == 1
 */
#include <stdio.h>
#include <stdlib.h>

void vtrace1(int a, double x, int r, double s){}

int mainQ(int a){
    double x = (double)a;
    int r = 1;
    double s = 3.25;

    while (1){
	vtrace1(a, x, r, s);
	if(!(x - s > 0.0)) break;

	x = x - s;
	s = s + 6 * r + 3;
	r = r + 1;
    }

    return r;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}
