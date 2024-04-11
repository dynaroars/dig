#include <stdio.h>
#include <stdlib.h>
void vassume(int b){}
void vtrace2(int x, int y, int z, int it){}

int mainQ(int x, int y){
    vassume(x >= 1 );

    int z = 0;
    int x1 = x;

    int it = 1;
    while (it < 28){
        it++;

    }


    vtrace2(x, y, z, it);  //postconditions
    return x;
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}




