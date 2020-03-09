#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int j, int k){}

void mainQ(int flag, int u1) {
    vassume(u1 > 0);
    int j = 2;
    int k = 0;
    int i0 = 0;

    while (i0 < u1) {
	i0++;
	if (flag != 0)
	    j = j + 4;
	else {
	    j = j + 2;
	    k = k + 1;
	}
    }

    vtrace(j, k);
    //%%%traces: int j, int k
    //if (k != 0) assert(j == 2 * k + 2);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
