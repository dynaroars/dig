#include <stdio.h>
#include <assert.h>

int mainQ(int a){
     float x,s;
     int r;
     x = (double)a;
     r = 1;
     s = 3.25;
     
     while (1){
	  //%%%traces: int a, double x, int r, double s
	  if(!(x-s > 0.0)) break;
	  
	  //assert(((int)(4*r*r*r - 6*r*r + 3*r) + (int)(4*x - 4*a)) == 1); 
	  //assert((int)(4*s) -12*r*r == 1); 
	  
	  x = x - s;
	  s = s + 6 * r + 3;
	  r = r + 1;
     }
     
     return r;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}

