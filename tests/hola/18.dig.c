#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace1(int flag, int j){}

void mainQ(int flag, int a) {
    int b = 0;
    int j = 0;
    for (b = 0; b < 5; ++b) {
	if (flag != 0) j = j + 1;
    }

    if (flag !=0){
	vtrace1(flag, j);
    }
    //if (flag != 0) assert(j == 100);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
