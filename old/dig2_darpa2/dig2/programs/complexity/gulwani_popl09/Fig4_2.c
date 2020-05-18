#include <stdio.h>
#include <assert.h>

int mainQ(int x0, int y0, int n, int m){
     int x = x0;
     int y = y0;
     
     int t = 0;
     while(x < n){
	  while(y < m){
	       y = y + 1;
	       t++;
	  }
	  x = x + 1;
     }
     //%%%traces: int n, int m, int x0, int y0, int t
     //dig2: l16: -t <= 0, m*t - (t*t) - t*y0 == 0
     //solve for t: [t == m - y0, t == 0]
     //NOTE: *** are these results correct ?  What is the complexity of this program?
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
     return 0;
}
