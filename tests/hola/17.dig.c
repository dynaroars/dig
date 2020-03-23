#include <stdlib.h>
#include <stdio.h>

void vassume(int b){}
void vtrace(int k, int n){}


void mainQ(int n) {
    vassume(n > 0);
    int k = 1;
    int i = 1;
    int j = 0;

    while (i < n) {
	j = 0;
	while (j < i) {
	    k += (i - j);
	    j++;
	}
	i++;
    }
    vtrace(k, n);
    //assert(k >= n);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]));
}
