#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int k, int i){}

void mainQ(int j, int k, int n) {
    int i = 0;

    for (i = 0; i < n; i++) {

	for (j = i; j < n; j++) {

	    for (k = j; k < n; k++) {
		vtrace(k, i);
		//assert(k >= i);
	    }
	}
    }
    //%%%traces: int k, int j, int n, int i
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
}
