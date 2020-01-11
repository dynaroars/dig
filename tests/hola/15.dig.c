#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int k){}

void mainQ(int n, int k) {
    vassume(n > 0);
    vassume(k > n);

    int j = 0;
    while (j < n) {
	j++;
	k--;
    }
    
    vtrace(k);
    //assert(k >= 0);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
