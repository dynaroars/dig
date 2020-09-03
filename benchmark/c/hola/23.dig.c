#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int s){}


void mainQ(int i, int n) {
    vassume(n >= 0);
    int s = 0;
    for (i = 0; i < n; ++i) {
	s = s + i;
    }

    vtrace(s);
    //assert(s >= 0);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
