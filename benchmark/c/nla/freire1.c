/* Freire's algorithm for the closest integer to sqrt(a).
 * see: http://www.pedrofreire.com/sqrt/sqrt1.en.html
 * loop invariant (over the reals, x is real-valued): 2*x + r*r - r - a == 0
 */
#include <stdio.h>
#include <stdlib.h>

void vtrace1(int a, double x, int r){}

int mainQ(int a){
    double x = ((double)a)/2.0;
    int r = 0;

    while(1){
	vtrace1(a, x, r);
	if (!(x > r)) break;
	x = x - r;
	r = r + 1;
    }

    return r;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}
