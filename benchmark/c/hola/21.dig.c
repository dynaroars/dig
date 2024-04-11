#include <stdio.h>
#include <stdlib.h>


void vassume(int b){}
void vtrace(int k, int n){}

void mainQ(int n, int j, int v, int u4) {
    vassume(n > 0);
    vassume(n < 10);

    int c1 = 4000;
    int c2 = 2000;

    int k = 0;
    int i = 0;
    while (i < n) {
	i++;
	if (u4)
	    v = 0;
	else
	    v = 1;

	if (v == 0)
	    k += c1;
	else
	    k += c2;
    }
  
    vtrace(k, n);
    //assert(k > n);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
}
