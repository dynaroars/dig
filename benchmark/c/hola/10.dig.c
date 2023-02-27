#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int x, int y){}


void mainQ(int u1) {
    vassume(u1 > 0);
    int i1 = 0;
    int w = 1;
    int z = 0;
    int x = 0;
    int y = 0;

    while (i1 < u1) {
	i1++;
	if (w == 1) {
	    x++;
	    w = 0;
	};
	if (z == 0) {
	    y++;
	    z = 1;
	};
    }

    vtrace(x, y);
    //assert(x == y);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]));
}
