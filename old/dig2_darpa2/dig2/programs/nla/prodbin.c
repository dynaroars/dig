#include <stdio.h>
#include <assert.h>

int mainQ(int a, int b){
     assert(a>=0);
     assert(b>=0);

     int x,y,z;
     x = a;
     y = b;
     z = 0;

     while(1) { 
	  //assert(z+x*y==a*b);
	  //%%%traces: int a, int b, int x, int y, int z
	  if(!(y!=0)) break;
	  
	  if (y%2 ==1 ){
	       z = z+x;
	       y = y-1;
	  }
	  x = 2*x;
	  y = y/2;

     }
     assert(z == a*b);
     return z; 

}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}

