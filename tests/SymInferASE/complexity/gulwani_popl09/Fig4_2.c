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
	  t++;
     }
     //%%%traces: int n, int m, int x0, int y0, int t
     //   l17: -t <= 0, m*n*t + (n*n)*t - m*(t*t) - 2*n*(t*t) + (t*t*t) - m*t*x0 - 2*n*t*x0 + 2*(t*t)*x0 + t*(x0*x0) - n*t*y0 + (t*t)*y0 + t*x0*y0 == 0
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]), atoi(argv[4]));
     return 0;
}
