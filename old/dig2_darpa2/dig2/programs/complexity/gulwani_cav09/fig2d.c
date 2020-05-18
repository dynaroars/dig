#include <stdio.h>
#include <assert.h>

int mainQ(int n, int m){
     //these assertions are based on gulwani pldi fig 4_3
     //(same as cav fig 2a).
     assert (m > 0);
     assert (n > m);
     
     int x = 0;
     int y = 0;
     int t = 0;
     while(x < n){
	  while (y < m){
	       t++;
	       y++;
	  }
	  y=0;
	  x++;
	  
     }

     //%%%traces: int n, int m, int t
     //dig2: -m <= -1, m*n - t == 0, m - n <= -1
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
