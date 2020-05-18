#include <stdio.h>
#include <assert.h>

int mainQ(int z, int a, int k){
     assert(k>0);
     int x = a; int y = 1;  int c = 1;

     while (1){
	  //assert(z*x-x+a-a*z*y == 0);
	  //%%%traces: int x, int y, int z, int a, int k

	  if (!(c < k)) break;
	  c = c + 1;
	  x = x*z + a;
	  y = y*z;

     }
     return x;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
     return 0;
}

