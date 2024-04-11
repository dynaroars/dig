#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}

int mainQ(int x, int y){
    vassume(x >= 1 && y >= 1);

    return 0;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


