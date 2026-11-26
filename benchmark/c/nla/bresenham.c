/*
 * Purpose: Step through integer pixels approximating a line from (0,0) toward (X,Y).
 *
 * Provenance: existing DIG NLA C benchmark collection:
 *   https://github.com/dynaroars/dig
 * Sources: J. E. Bresenham, Algorithm for Computer Control of a Digital Plotter, IBM Systems
 * Journal 4(1), 25-30 (1965); DOI 10.1147/SJ.41.0025. Algorithm citation; exact C adaptation
 * provenance is not established.
 *
 * Expected invariants (mathematical notation; ** means exponent):
 *   vtrace1: 2*Y*x-2*X*y-X+2*Y-v == 0.
 * These relations are derived from this file's initialization and updates.
 * They assume mathematical integers / exact reals and no signed overflow.
 * Notes: The usual line-drawing domain is 0 <= Y <= X; this file does not enforce it. The
 * polynomial follows directly from both branches.
 */
#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int X, int Y, int x, int y, int v){}

int mainQ(int X, int Y){

    int v, x, y;
    v = 2 * Y - X;
    y = 0;
    x = 0;
    while (1) {
	//2*Y*x - 2*X*y - X + 2*Y - v == 0
	vtrace1(X,Y, x,y,v);
	if (!(x <= X))
	    break;
	
	if (v < 0) {
	    v = v + 2 * Y;
	    } else {
	    v = v + 2 * (Y - X);
	    y++;
	}
	    x++;
    }
    // At this exit the same trace invariant holds: 2*Y*x - 2*X*y - X + 2*Y - v == 0.
    return 0;
}


void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

