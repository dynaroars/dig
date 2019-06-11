#include <stdio.h>
#include <assert.h>

int mainQ(int n, int m){
     int x = 0;
     int y = 0;
     int t = 0;
     while(x < n){
	  y=0;
	  x++;
	  while(y < m){
	       y++;
	       t++;
	  }
	  
     }
     //%%%traces: int n, int m, int t
     //dig2: t>= 0
     //NOTE: *** why didn't I get anything useful here ?  should t = some function of n, m ? 
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
