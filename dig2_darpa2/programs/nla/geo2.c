#include <stdio.h>
#include <assert.h>

int mainQ(int z, int k){
     //if too large then might cause overflow
     assert(z>=0);
     assert(z<=10);
     assert(k>0);
     assert(k<=10);
     int x = 1; int y = 1; int c = 1;

     while (1){
	  //assert(1+x*z-x-z*y==0);
	  //%%%traces: int x, int y, int z, int k
	  //printf("%d %d %d %d\n", x, y ,z, k);
	  
	  if(!(c < k)) break;
	  c = c + 1;
	  x = x*z + 1;
	  y = y*z;
     }
     return x;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

