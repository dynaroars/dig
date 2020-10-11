#include <stdio.h>
#include <assert.h>

int mainQ(int x0, int y0, int n, int m){
     int x = x0;
     int y = y0;
     int t = 0;
     while(x < n){
	  if(y < m){
	       y++;
	  }
	  else{
	       x++;
	  }
	  t++;
     }
     //%%%traces: int n, int m, int x0, int y0, int t
     //NOTE: have to manually pass in the flag -maxdeg 3 (otherwise SAGE's eqt solver seems to hang).
     //dig2:  l17: m*n*t + (n*n)*t - m*(t*t) - 2*n*(t*t) + (t*t*t) - m*t*x0 - 2*n*t*x0 + 2*(t*t)*x0 + t*(x0*x0) - n*t*y0 + (t*t)*y0 + t*x0*y0 == 0, -t <= 0
     //solve for t get:  [t == m + n - x0 - y0, t == n - x0, t == 0]
     //NOTE: *** are these results correct, better, etc than the given bound of Max(0, n-x0) + Max(0, m-y0)
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
     return 0;
}
