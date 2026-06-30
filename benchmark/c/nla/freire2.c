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
