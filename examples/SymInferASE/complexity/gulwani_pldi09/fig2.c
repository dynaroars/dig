#include <stdio.h>
#include <assert.h>

int mainQ(int n, int m, int N){
     assert (0 <= n);
     assert (0 <= m);
     assert (0 <= N);
     int t = 0;
     int i = 0;
     int j = 0;
     int k = 0;
     while(i < n){
	  j = 0;
	  while(j<m){	       
	       j = j+1;
	       k=i;
	       t = t +1;
	       while (k<N){		    
		    k=k+1;
		    t = t +1;
	       }
	       i=k;
	  }
	  i=i+1;
	  t = t + 1;
     }
     //%%%traces: int n, int m, int N, int t
     //dig2 invs:
     //l29: -N <= 0, -m <= 0, -n <= 0, n - t <= 0, (N*N)*m*n + N*(m*m)*n - N*m*(n*n) - (m*m)*(n*n) - N*m*n*t + m*(n*n)*t + N*m*n - N*(n*n) - 2*m*(n*n) + N*n*t + m*n*t + (n*n)*t - n*(t*t) - (n*n) + n*t == 0, (N*N)*m*t + N*(m*m)*t - N*m*n*t - (m*m)*n*t - N*m*(t*t) + m*n*(t*t) + N*m*t - N*n*t - 2*m*n*t + N*(t*t) + m*(t*t) + n*(t*t) - (t*t*t) - n*t + (t*t) == 0
     
     return 0;
}


int main(int argc, char **argv){
     mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
     return 0;
}
