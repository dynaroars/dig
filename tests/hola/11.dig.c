#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int j, int x){}

void mainQ(void) {
    int j = 0;
    int x = 100;
    int i = 0;

    for (i = 0; i < x; i++) {
	j = j + 2;
    }
    vtrace(j, x);
    //assert(j == 2 * x);
}

void main(int argc, char *argv[]) {
    mainQ();
}
