/*
 * Purpose: Compute an online mean and corrected sum of squared deviations (M2).
 * Sources: B. P. Welford, Note on a Method for Calculating Corrected Sums of Squares and
 * Products, Technometrics 4(3), 419-420 (1962). https://doi.org/10.1080/00401706.1962.10490022
 * Provenance: C benchmark adaptation created for the DIG NLA-mosaic suite.
 *
 * Expected invariants at every vtrace1 call (mathematical notation):
 *   n*mean-sum == 0 (degree 2 search cap).
 *   n*M2-n*sumsq+sum**2 == 0 (degree 2 search cap).
 *   ** denotes exponentiation, not C syntax.
 * Domain: mainQ arguments, in order, range over [[0, 12], [-5, 5], [-5, 5]].
 * Arithmetic: exact-real specification; C doubles round.
 * Notes: Our deterministic sample stream uses base, step, and n. Auxiliary sum and sumsq expose
 * prefix statistics. The identities hold over exact reals; ordinary C doubles can produce nonzero
 * rounding residuals. M2 is an unnormalized sum; sample variance is M2/(n-1) for n>1.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int n, double mean, double M2, int sum, int sumsq){}

int mainQ(int N, int base, int step){
    vassume(N >= 0 && N <= 12);
    vassume(base >= -5 && base <= 5);
    vassume(step >= -5 && step <= 5);
    if (N < 0 || N > 12 || base < -5 || base > 5 || step < -5 || step > 5) return 0;
    int n = 0, sum = 0, sumsq = 0;
    double mean = 0.0, M2 = 0.0;
    while (1){
        // assert(n*mean-sum == 0);
        // assert(n*M2-n*sumsq+sum*sum == 0);
        vtrace1(n, mean, M2, sum, sumsq);
        if (!(n < N)) break;
        int sample = base + (n % 3 - 1)*step + n;
        n++;
        double delta = sample - mean;
        mean = mean + delta/n;
        M2 = M2 + delta*(sample - mean);
        sum = sum + sample;
        sumsq = sumsq + sample*sample;
    }
    return 0;
}

int main(int argc, char **argv){
    if (argc != 4) return 1;
    return mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}
