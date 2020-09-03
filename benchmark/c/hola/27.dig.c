#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int k){}

void mainQ(int l, int i, int k, int n) {
    vassume(l > 0);

    for (k = 1; k < n; k++) {

	for (i = l; i < n; i++) {
	}

	for (i = l; i < n; i++) {
	    vtrace(k);
	    //assert(1 <= k);
	}
    }
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
}
