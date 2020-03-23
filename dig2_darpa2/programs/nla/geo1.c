#include <stdio.h>
#include <assert.h>
#include <math.h>

int mainQ(int z, int k){
     //if too large then might cause overflow
     assert(z>=0);
     assert(z<=10);
     assert(k > 0);
     assert(k<=10); 
     
     int x = 1; int y = z; int c = 1;

     while (1){
	  //assert(x*z - x - y + 1 == 0);
	  //%%%traces: int x, int y, int z, int k

	  if(!(c < k)) break;
	  
	  c = c + 1;
	  x = x*z + 1;
	  y = y*z;

     }//geo1

     x = x *(z - 1);

     return x;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

