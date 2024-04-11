#include <stdio.h>
#include <stdlib.h>
void vassume(int b){}
void vtrace(int i){}


void mainQ(int i, int n, int l) {
    vassume(l > 0);
    int t = 0;
    int k = 0;

    for (k = 1; k < n; k++) {

	for (i = l; i < n; i++) {
	    t = t + 1;
	}

	for (i = l; i < n; i++) {
	    vtrace(i);
	    //assert(1 <= i)
	    t = t + 1;
	}
    }
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}
