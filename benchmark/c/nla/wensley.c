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
