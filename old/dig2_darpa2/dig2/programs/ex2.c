#include <stdio.h>
#include <assert.h>


void mainQ(int x, int y){
     assert (x >= 2);
     assert (y >= 5);
     //assert (2*x == 5*y);
     //%%%traces: int x, int y
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

