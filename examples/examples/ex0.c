#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int m){}
    
void mainQ(int m, int n) {
    vassume(n > 9);
    if (2*m == 18){
        vtrace1(m);
    }
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
