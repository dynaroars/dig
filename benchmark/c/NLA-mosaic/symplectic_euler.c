/*
 * Purpose: Advance a harmonic oscillator using momentum-first symplectic Euler steps.
 * Sources: E. Hairer and G. Vilmart, Computing the Long Term Evolution of the Solar System with
 * Geometric Numerical Integrators, section 3.
 * https://www.unige.ch/~vilmart/snapshots-2017-009.pdf
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   p**2+q**2-h*p*q-energy == 0 (degree 3 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 8], [-5, 5], [-5, 5], [1, 3]].
 * Arithmetic: exact dyadic C doubles within input bounds.
 * Notes: Our momentum-first ordering uses the negative cross term; its sign/coefficient were
 * derived and checked independently. energy stores the initial modified energy. Steps are
 * 1/4,1/2,3/4; bounded dyadic runs preserve the observed values exactly.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(double p, double q, double h, double energy){}

int mainQ(int n, int p0, int q0, int step){
    vassume(n >= 0 && n <= 8);
    vassume(p0 >= -5 && p0 <= 5);
    vassume(q0 >= -5 && q0 <= 5);
    vassume(step >= 1 && step <= 3);
    if (n < 0 || n > 8 || p0 < -5 || p0 > 5 || q0 < -5 || q0 > 5 || step < 1 || step > 3) return 0;
    double p = p0, q = q0, h = step/4.0;
    double energy = p*p + q*q - h*p*q;
    int i = 0;
    while (1){
        // assert(p*p+q*q-h*p*q-energy == 0);
        vtrace1(p, q, h, energy);
        if (!(i < n)) break;
        p = p - h*q;
        q = q + h*p;
        i++;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 5) return 1;
    return mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
}
