#include <stdio.h>
#include <assert.h>
//same as fig2a gulwani_cav09


int mainQ(int n, int m){
     assert (m > 0);
     assert (n > m);
     int i = 0;
     int j = 0;
     int t = 0;
     while(i<n){
	  if (j < m) {
	       j++;
	  }else{
	       j=0;
	       i++;
	  }
	  t++;
     }
     //%%%traces: int n, int m, int t
     //dig2: -m <= -1, m*n + n - t == 0, m - n <= -1

     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]));
     return 0;
}
