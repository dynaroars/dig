#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int a, int m){}


void mainQ(int m, int u4) {
    vassume(m > 0);

    int a = 0;
    int j = 0;
    for (j = 1; j <= m; j++) {
	if (u4)
	    a++;
	else
	    a--;
    }

    vtrace(a, m);
    //assert(a >= 0 - m);
    //assert(a <= m);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
