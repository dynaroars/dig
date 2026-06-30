/* Real arithmetic-series sum: s = sum_{i<n}(i + 1/2), t = n + 1/2.
   Invariants: 2*s - n*n == 0 (deg 2) and 2*t - 2*n - 1 == 0. */
#include <stdio.h>
#include <stdlib.h>
void vtrace1(double s, double t, int n){}
int mainQ(int N){
    double s = 0.0;
    double t = 0.5;
    int n = 0;
    while (n < N){
        vtrace1(s, t, n);
        s = s + t;
        t = t + 1.0;
        n = n + 1;
    }
    return n;
}
void main(int argc, char **argv){ mainQ(atoi(argv[1])); }
