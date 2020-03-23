/* *** I don't really know what this dir = fwd means so cannot try this example*** */

#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int n, int m, int j, int tCtr){}

int mainQ(int n, int m, int j){
     vassume(m > 0);
     vassume(n > m);
     int i = m;
     int tCtr = 0;
     while(i>0 && i < n){
	  if (j > 0) {
	       i++;
	  }else{
	       i--;
	  }
	  tCtr++;
     }
     vtrace_post(n, m, j, tCtr);
     //%%%traces: int n, int m, int j, int t
     
     //NOTE: With DIG1 I got m^2*t - m*n*t + n*t^2 - t^3 == 0, whose solutions are t = n-m, t = m, t =0. They seem correct.
     //j plays the role of a fixed truth value representing dir=fwd

     //dig2: (m*m) - m*n + n*t - (t*t) == 0, m - n <= -1, -m <= -1
     //NOTE: solving for the above eqt:  [t == -m + n, t == m] 
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
     return 0;
}
