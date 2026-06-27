#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int n, int r){}

int mainQ(int n){
    vassume(n >= 0);
    vassume(n <= 100);

    int r = 0;
    while ((r+1)*(r+1) <= n){
	vtrace1(n, r);
	r = r + 1;
    }
    vtrace1(n, r);
    return r;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]));
}
