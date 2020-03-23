#include <stdio.h>
#include <stdlib.h>
#include <assert.h>


int mainQ(int n){
     int x = 0;
     int y = 0;
     int t = 0;
     while(x < n){
	  y = x;
	  while (y < n){
	       t++;
	       y++;
	  }
	  
	  x=y+1;
     }
     //%%%traces: int n, int t
     //dig2:  n*t - (t*t) == 0, -t <= 0, n - t <= 0
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]));
     return 0;
}
