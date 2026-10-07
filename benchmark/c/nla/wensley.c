/*
 * Purpose: Approximate P/D by choosing binary fractional quotient bits over 20 iterations.
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: Related algorithm: SRI-hosted report, section VI, The Real Number Quotient Algorithm
 * (Wensley quotient example). Exact source lineage of this fixed-20-step C variant is not
 * established. https://www.sri.com/wp-content/uploads/2021/12/765.pdf
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: a-D*y == 0.
 *   vtrace1: 2*b-D*d == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: For quotient interpretation require 0 <= P < D and D > 0; this file does not enforce
 * these assumptions. Exact-real invariant specification.
 */
/* Wensley's algorithm (1958) for real division y ~= P/D, 0 <= P < D.
   Real loop invariants: a - D*y == 0 and 2*b - D*d == 0. */
#include <stdio.h>
#include <stdlib.h>
void vtrace1(int P, int D, double a, double b, double d, double y){}
int mainQ(int P, int D){
    double a = 0.0;
    double b = ((double)D) / 2.0;
    double d = 1.0;
    double y = 0.0;
    int k = 0;
    while (k < 20){
        vtrace1(P, D, a, b, d, y);
        if (P - a >= b){
            y = y + d/2.0;
            a = a + b;
        }
        b = b/2.0;
        d = d/2.0;
        k = k + 1;
    }
    return 0;
}
void main(int argc, char **argv){ mainQ(atoi(argv[1]), atoi(argv[2])); }
