#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace(int i, int j, int y){}

void mainQ(int i, int j) { 
    int x = i;
    int y = j;

    while (x != 0) {
	x--;
	y--;
    }
    //%%%traces: int i, int j, int y
    vtrace(i, j, y);
    //if (i == j) assert(y == 0);
}

void main(int argc, char *argv[]) {
    mainQ(atoi(argv[1]), atoi(argv[2]));
}
