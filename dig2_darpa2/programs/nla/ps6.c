#include <stdio.h>
#include <assert.h>

int mainQ(int k){
     assert (k>=0);
     assert (k<=30); //if too large then overflow
     
     int y = 0;
     int x = 0;
     int c = 0;


     while(1){
	  //assert(-2*pow(y,6) - 6*pow(y,5) - 5*pow(y,4) + pow(y,2) + 12*x == 0.0); //DIG Generated  (but don't uncomment, assertion will fail because of int overflow)	  
	  //%%%traces: int x, int y, int k


	  if (!(c < k)) break;
	  c = c + 1 ;
	  y = y + 1;
	  x=y*y*y*y*y+x;
     }
     return x;
}

int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}

