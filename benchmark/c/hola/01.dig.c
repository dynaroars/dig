#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int x, int y){}
    
void mainQ(int n) {
    vassume(n > 0);
    int x = 1;
    int y = 1;
    int j = 0;

    while (j < n) {
	int t1 = x;
	int t2 = y;
	x = t1 + t2;
	y = t1 + t2;
	j = j + 1;
    }
    vtrace(x, y);

    //assert(y >= 1);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]));
}
