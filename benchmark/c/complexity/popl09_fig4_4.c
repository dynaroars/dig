#include <stdio.h>
#include <stdlib.h>

void vassume(int b){}
void vtrace_post(int n, int m, int tCtr){}

int mainQ(int n, int m){
     vassume(m >= 0);
     vassume(n >= 0);
     int x = 0;
     int y = 0;
     int tCtr = 0;
     while(x < n){
	  y=0;
	  x++;
	  while(y < m){
	       y++;
	       tCtr++;
	  }
          tCtr++;
     }
     vtrace_post(n, m, tCtr);     
     //%%%traces: int n, int m, int t
     //dig2: t>= 0
     //NOTE: *** why didn't I get anything useful here ?  should t = some function of n, m ?
     // Again, there is a t++ missing for the outer loop. I ran the corrected version on DIG1 and got m*n + n - t == 0 which looks correct.
     return 0;
}


void main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
}
