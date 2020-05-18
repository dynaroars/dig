#include <stdio.h>
#include <assert.h>


void mainQ(int x, int y, int z, int w){
     assert (2*x == 5*y);
     //%%%traces: int x, int y
     assert (z==w*w);
     //%%%traces: int z, int w
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
     return 0;
}

