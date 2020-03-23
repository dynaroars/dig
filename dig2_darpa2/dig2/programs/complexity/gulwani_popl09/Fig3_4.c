#include <stdio.h>
#include <assert.h>

int mainQ(int n, int m){
     int x = 0;
     int y = 0;
     int t = 0;
     while((x < n || y < m)){
	  if(x < n){
	       x++;
	       y++;
	  }
	  else if(y < m){
	       x++;
	       y++;
	  }
	  else{
	       assert(0);
	       break;
	  }
	  t++;
     }
     //%%%traces: int n, int m, int t
     //dig2: m*n*t - m*(t*t) - n*(t*t) + (t*t*t) == 0, m - t <= 0, n - t <= 0, -t <= 0
     //solve for t : t == n, t == m, t == 0
     //NOTE: *** are the above correct ? there are 3 exact bounds as indicated for this?
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
