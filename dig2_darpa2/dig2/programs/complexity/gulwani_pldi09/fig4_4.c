#include <stdio.h>
#include <assert.h>
#include <time.h>

int mainQ(int n, int m){
     assert (m > 0);
     assert (n > m);
     int i = n;
     int t = 0;
     while(i>0){
	  if (i < m) {
	       i--;
	  }else{
	       i = i-m;
	  }
	  t++;
     }
     //%%%traces: int n, int m, int t, int i
     //dig2: -m <= -1, -n + t <= 0, -i <= 0, -i - t <= -2, i <= 0, m - n <= -1

     //NOTE: *** cannot get anything useful wrt to t ***, did I do something wrong here ? what do we expect the number of iterations t to be ?
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
